#lang racket

(require "datalog.rkt")
(provide solve-naive)


(define (solve-naive P E)

  (define strata (stratify P))
  
  ; * E      set of tuples (initially only the ones in the database)
  (define (solve E0)

    (define num-derived-tuples 0)

    (define (stratum-rule-loop rules tuples) ; per stratum
      (let loop ((rules rules) (derived-tuples tuples))
        (if (set-empty? rules) ; Check whether all rules have been traversed as far as needed.
            derived-tuples
            (let ((rule (set-first rules)))
              (let ((derived-tuples-for-rule (for/set ((fr (in-set (fire-rule rule derived-tuples (set)))))
                                                (car fr)))) ; drop provenance
                ; (printf "fired ~a got ~a\n" rule derived-tuples-for-rule)
                (set! num-derived-tuples (+ num-derived-tuples (set-count derived-tuples-for-rule)))
                (loop (set-rest rules) (set-union derived-tuples derived-tuples-for-rule))))))) ; Accumulate all derived tuples.

    (define (stratum-loop S E-inter)
      ; (printf "\nn stratum ~a/~a with ~a tuples\n" (- (set-count strata) (set-count S)) (set-count strata) (set-count E-inter))
      (if (null? S) ; Check whether there are more strata to traverse.
          (solver-result E-inter num-derived-tuples (make-delta-solver E-inter)); All tuples (initial and derived).
          (let ((Pi (car S))) ; Rules in the first stratum.
            ; (printf "Pi: ~v\n" (list->set (set-map Pi (lambda (r) (atom-name (rule-head r))))))
            (let intra-loop ((E-intra E-inter))
              (let ((tuples (stratum-rule-loop Pi E-intra)))
                (let ((E-intra* (set-union E-intra tuples)))
                    (if (equal? E-intra E-intra*) ; monotonicity: size check quicker? (TODO)
                        (stratum-loop (cdr S) E-intra*)
                        (intra-loop E-intra*))))))))

    (define (make-delta-solver tuples)
      (lambda msg 
        (match msg
          (`(match-atom ,atom)
            (for/set ((tuple+bindings (in-set (match-all-atoms atom tuples (hash)))))
              (car tuple+bindings)))
          (`(run-query ,atoms ...)
            (run-query atoms tuples (set)))
          (`(apply-delta ,deltas)
            (let ((E (apply-deltas deltas E0)))
              (solve E)))
          (_ (error "incremental delta solver does not understand " msg)))))

    (stratum-loop strata E0))

  (solve E)                       
)


(module+ main

  (define r1 (:- #(Reachable x y) #(Link x y)))
  (define r2 (:- #(Reachable x y) #(Link x z) #(Reachable z y)))

  (define P (set r1 r2))
  (define E (set #(Link a b) #(Link b c)))

  (define result (solve-naive P E))
  (define tuples (solver-result-tuples result))
  (printf "~a\n" (sort-tuples tuples))
  (unless (equal? tuples (set-union E (set
    #(Reachable a b)
    #(Reachable b c)
    #(Reachable a c)
    )))
    (error "wrong!"))
)

