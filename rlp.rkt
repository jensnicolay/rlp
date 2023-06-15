#lang racket

(random-seed 111) ; deterministic random

(require "datalog.rkt")
(require "naive.rkt")

(struct state (messages lstates undelivered) #:transparent)
;(struct flowop (f) #:property prop:custom-write (lambda (v p w?) (fprintf p "(flowop <f>)")))
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
            (match-let (((output new-lstate out-messages) (op inp d (hash-ref lstates op (lambda () #f)))))
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
(define (make-iter-source collection)
  (let ((lst (for/list ((x collection)) x)))
    (lambda (_ d s)
      (output 'completed (map (lambda (x) `(out . ,x)) lst)))))

(define (make-counter n)
  (lambda (_ d s)
    (if (< d n)
        (output s `((out . ,(+ d 1))))
        (output d '()))))

(define (make-map f)
  (lambda (_ d s)
    (output s `((out . ,(f d))))))

(define (make-adder)
  (lambda (_ d s)
    (let ((new-d (+ (or s 0) d)))
      (output new-d `((out . ,new-d))))))

(define (make-rules rules)
  (match-lambda* 
    (`(add ,d ,s)
     (let* ((previous-tuples (if s
                                 (set-union (solver-result-tuples s) d)
                                 d))
            (new-s (if s
                       ((solver-result-delta-solver s) 'apply-delta (list->set (set-map d add-tuple)))
                       (solve-naive rules d)))
            (result-tuples (solver-result-tuples new-s))
            (tuples-added (set-subtract result-tuples previous-tuples)))
      (output new-s `((added . ,tuples-added)))))))
                   
;; examples (every let* is an example)  

;(let* ((doubler (make-map (lambda (n) (* n 2))))
;       (resolve-link (make-fixed-linker))
;       (step (make-step resolve-link))
;       (initial-state (inject (list (message doubler 'in 123)))))
;  (run initial-state step))
;
;
;(let* ((doubler (make-map (lambda (n) (* n 2))))
;       (filtrino (lambda (_ d s)
;                           (output s (if (zero? (remainder d 5))
;                                        '()
;                                        (list (cons 'out d))))))
;       (resolve-link (make-fixed-linker (link doubler 'out filtrino 'in)))
;       (step (make-step resolve-link))
;       (initial-state (inject (list (message doubler 'in 1)
;                                    (message doubler 'in 2)
;                                    (message doubler 'in 3)
;                                    (message doubler 'in 4)
;                                    (message doubler 'in 5)
;                                    (message doubler 'in 6)))))
;  (run initial-state step))
;
;(let* ((plexer (lambda (_ d s)
;                         (output s (list (cons 'out d)))))
;       (doubler (make-map (lambda (n) (* n 2))))
;       (squarer (make-map (lambda (n) (* n n))))
;       (filtrino (lambda (_ d s)
;                           (output s (if (zero? (remainder d 5))
;                                        '()
;                                        (list (cons 'out d))))))
;       (resolve-link (make-fixed-linker (link plexer 'out doubler 'in) (link plexer 'out squarer 'in) (link doubler 'out filtrino 'in) (link squarer 'out filtrino 'in)))
;       (step (make-step resolve-link))
;       (initial-state (inject (list (message plexer 'in 1)
;                                    (message plexer 'in 2)
;                                    (message plexer 'in 3)
;                                    (message plexer 'in 4)
;                                    (message plexer 'in 5)
;                                    (message plexer 'in 6)))))
;  (run initial-state step))
;
;
;(let* ((adder (make-adder))
;       (resolve-link (make-fixed-linker))
;       (step (make-step resolve-link))
;       (initial-state (inject (list (message adder 'in 1)
;                                    (message adder 'in 2)
;                                    (message adder 'in 3)))))
;  (run initial-state step))
;
;
;(let* ((counter (make-counter 10))
;       (resolve-link (make-fixed-linker (link counter 'out counter 'in)))
;       (step (make-step resolve-link))
;       (initial-state (inject (list (message counter 'in 0)))))
;  (run initial-state step))
;
;(let* ((counter (make-counter 10))
;       (receiver (make-map (lambda (x) x)))
;       (resolve-link (make-fixed-linker (link counter 'out counter 'in) (link counter 'out receiver 'in)))
;       (step (make-step resolve-link))
;       (initial-state (inject (list (message counter 'in 0)))))
;  (run initial-state step))
;
;(let* ((counter (make-counter 10))
;       (adder (make-adder))
;       (resolve-link (make-fixed-linker (link counter 'out counter 'in) (link counter 'out adder 'in)))
;       (step (make-step resolve-link))
;       (initial-state (inject (list (message counter 'in 0)))))
;  (run initial-state step))
;
;
;(let* ((src (make-iter-source (set 1 2 3)))
;       (resolve-link (make-fixed-linker))
;       (step (make-step resolve-link))
;       (initial-state (inject (list (message src 'in 'start)))))
;  (run initial-state step))

(define r1 (:- #(Reachable x y) #(Link x y)))
(define r2 (:- #(Reachable x y) #(Link x z) #(Reachable z y)))
(define P (set r1 r2))

;(let* ((src (make-iter-source (list (set #(Link 1 2) #(Link 2 3)))))
;       (rules (make-rules P))
;       (resolve-link (make-fixed-linker (link src 'out rules 'add)))
;       (step (make-step resolve-link))
;       (initial-state (inject (list (message src 'in 'start)))))
;  (run initial-state step))

(let* ((src (make-iter-source (list (set #(Link 1 2) #(Link 2 3)) (set #(Link 3 4)))))
       (rules (make-rules P))
       (resolve-link (make-fixed-linker (link src 'out rules 'add)))
       (step (make-step resolve-link))
       (initial-state (inject (list (message src 'in 'start)))))
  (run initial-state step))


