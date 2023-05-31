#lang racket

(struct state (messages lstates undelivered) #:transparent)
(struct flowop (f) #:property prop:custom-write (lambda (v p w?) (fprintf p "(flowop <f>)")))
(struct message (to inp d) #:transparent)
(struct output (new-lstate out-messages) #:transparent)

(define (make-step resolve-link)
  (let* ()
    (lambda (s)
      (match s
        ((state '() _ _)
         (set))
        ((state messages lstates undelivered)
         (match (car messages)
           ((message op inp d) 
            (match-let (((output new-lstate out-messages) ((flowop-f op) inp d (hash-ref lstates op (lambda () #f)))))
              (let loop ((out-messages out-messages) (messages (cdr messages)) (undelivered undelivered))
                (if (null? out-messages)
                    (set (state messages (hash-set lstates op new-lstate) undelivered))
                    (let ((out-message (car out-messages)))
                      (match (car out-messages)
                        ((cons outp d)
                         (let ((resolved (resolve-link op outp)))
                           (if (null? resolved)
                               (loop (cdr out-messages)
                                     messages
                                     (append undelivered (list out-message)))
                               (loop (cdr out-messages)
                                     (append messages (map (lambda (toop-inp)
                                                             (message (car toop-inp) (cdr toop-inp) d))
                                                           resolved))
                                     undelivered))))))))))))))))

(define (inject messages)
  (state messages (hash) '()))

(define (run s step)
  (let loop ((visited (set))
             (todo (set s))
             (final (set)))
    (if (set-empty? todo)
        final
        (let ((s (set-first todo)))
          (if (set-member? visited s)
              (loop visited (set-rest todo) final)
              (let ((succs (step s)))
                (if (set-empty? succs)
                    (loop (set-add visited s) (set-rest todo) (set-add final s))
                    (loop (set-add visited s) (set-union succs (set-rest todo)) final))))))))


;; fixed connections
(struct link (from outp in inp) #:transparent)
(define (make-fixed-linker . links)
  (lambda (op outp)
    (for/fold ((resolved '())) ((l (in-list links)))
      (match l
        ((link (== op) (== outp) in inp)
         (append resolved (list (cons in inp) )))
        (_ resolved)))))
;;

;; operators
(define (make-map f)
  (flowop (lambda (_ d s)
            (output s (list (cons 'out (f d)))))))

(define (make-counter n)
  (flowop (lambda (_ d s)
            (if (< d n)
                (output s (list (cons 'out (+ d 1))))
                (output d '())))))

(define (make-counterf n)
  (flowop (lambda (_ d finished)
            (if finished
                (output #t '())
                (if (< d n)
                    (output #f (list (cons 'out (+ d 1))))
                    (output #t (list (cons 'out 'complete))))))))

(define (make-adder)
  (flowop (lambda (_ d s)
            (let ((new-d (+ (or s 0) d)))
              (output new-d (list (cons 'out new-d)))))))

(define (make-adderf)
  (flowop (lambda (_ d s)
            (if (eq? (car d) 'complete)
            (let ((new-d (+ (or s 0) d)))
              (output new-d (list (cons 'out new-d)))))))

;; examples (every let* is an example)  

(let* ((doubler (make-map (lambda (n) (* n 2))))
       (resolve-link (make-fixed-linker))
       (step (make-step resolve-link))
       (initial-state (inject (list (message doubler 'in 123)))))
  (run initial-state step))


(let* ((doubler (make-map (lambda (n) (* n 2))))
       (filtrino (flowop (lambda (_ d s)
                           (output s (if (zero? (remainder d 5))
                                        '()
                                        (list (cons 'out d)))))))
       (resolve-link (make-fixed-linker (link doubler 'out filtrino 'in)))
       (step (make-step resolve-link))
       (initial-state (inject (list (message doubler 'in 1)
                                    (message doubler 'in 2)
                                    (message doubler 'in 3)
                                    (message doubler 'in 4)
                                    (message doubler 'in 5)
                                    (message doubler 'in 6)))))
  (run initial-state step))

(let* ((plexer (flowop (lambda (_ d s)
                         (output s (list (cons 'out d))))))
       (doubler (make-map (lambda (n) (* n 2))))
       (squarer (make-map (lambda (n) (* n n))))
       (filtrino (flowop (lambda (_ d s)
                           (output s (if (zero? (remainder d 5))
                                        '()
                                        (list (cons 'out d)))))))
       (resolve-link (make-fixed-linker (link plexer 'out doubler 'in) (link plexer 'out squarer 'in) (link doubler 'out filtrino 'in) (link squarer 'out filtrino 'in)))
       (step (make-step resolve-link))
       (initial-state (inject (list (message plexer 'in 1)
                                    (message plexer 'in 2)
                                    (message plexer 'in 3)
                                    (message plexer 'in 4)
                                    (message plexer 'in 5)
                                    (message plexer 'in 6)))))
  (run initial-state step))


(let* ((adder (make-adder))
       (resolve-link (make-fixed-linker))
       (step (make-step resolve-link))
       (initial-state (inject (list (message adder 'in 1)
                                    (message adder 'in 2)
                                    (message adder 'in 3)))))
  (run initial-state step))


(let* ((counter (make-counter 10))
       (resolve-link (make-fixed-linker (link counter 'out counter 'in)))
       (step (make-step resolve-link))
       (initial-state (inject (list (message counter 'in 0)))))
  (run initial-state step))

(let* ((counter (make-counter 10))
       (receiver (make-map (lambda (x) x)))
       (resolve-link (make-fixed-linker (link counter 'out counter 'in) (link counter 'out receiver 'in)))
       (step (make-step resolve-link))
       (initial-state (inject (list (message counter 'in 0)))))
  (run initial-state step))

(let* ((counter (make-counter 10))
       (adder (make-adder))
       (resolve-link (make-fixed-linker (link counter 'out counter 'in) (link counter 'out adder 'in)))
       (step (make-step resolve-link))
       (initial-state (inject (list (message counter 'in 0)))))
  (run initial-state step))

(let* ((counter (make-counterf 10))
       (adder (make-adder))
       (resolve-link (make-fixed-linker (link counter 'out counter 'in) (link counter 'out adder 'in)))
       (step (make-step resolve-link))
       (initial-state (inject (list (message counter 'in 0)))))
  (run initial-state step))




