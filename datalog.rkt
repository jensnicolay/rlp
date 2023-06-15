





#lang racket

(provide
    atom? atom-name atom-arity atom-term ¬
    rule rule-head rule-body :-
    match-all-atoms run-query
    stratify fire-rule
    solver-result solver-result-tuples solver-result-num-derived-tuples solver-result-delta-solver
    add-tuple remove-tuple apply-deltas
    sort-tuples print-map)

; Terminology (TODO: look at https://dodisturb.me/posts/2018-12-25-The-Essence-of-Datalog.html for ADT naming)
; * Term: Constant or Variable
; * Atom: Predicate + list of terms
; * EDB predicate: predicate in the source tables of the database
; * IDB predicate: predicate in tables derived by Datalog program

; Conventions
; * A prefix `l` indicates labelling.

; Naming
; * P   the set of rules
; * E   the set of tuples

(define ns (make-base-namespace))

(struct ¬ (p) #:transparent)
(struct rule (head body aggregates) #:transparent)

(struct solver-result (tuples num-derived-tuples delta-solver) #:transparent)

;;;
; (struct tuples (tuple-set meta) #:transparent)

; (define (tuples-add-tuple ts tuple meta)
;   (match-let (((tuples tuple-set meta) ts))
;     (tuples (set-add tuple-set tuple) (hash-set meta tuple meta)


;;;
(struct add-tuple (tuple) #:transparent)
(struct remove-tuple (tuple) #:transparent)

(define (apply-deltas deltas E)
  (for/fold ((E E)) ((delta deltas))
     (match delta
      ((add-tuple tuple) (set-add E tuple))
      ((remove-tuple tuple) (set-remove E tuple)))))
;;;

(define variable? symbol?)

(define (make-atom name terms)
  `#(,name ,@terms))

(define (atom-name a)
  (vector-ref a 0))

(define atom? vector?)

(define (atom-arity a)
  (sub1 (vector-length a)))

(define (atom-term a i)
  (vector-ref a (add1 i)))

; A rule consists out of a head and a body, the latter again consisting out of an arbitrary number of atoms.

(define (:- head . body)

  (define head-name (atom-name head))
  (define head-terms (cdr (vector->list head)))

  (define (term->aggregator term)
    (match term
      ('#:sum (lambda xs (apply + (car xs))))
      ('#:count (lambda xs (length (car xs))))
      ('#:min (lambda xs (apply min (car xs))))
      ('#:max (lambda xs (apply max (car xs))))
      (_ #f)
    ))

  (define (parse-regular-head head headr bodyr)
    (if (null? head)
        (rule (make-atom head-name headr) bodyr '())
        (let ((term (car head)))
          (let ((agg (term->aggregator term)))
            ; (printf "term ~a agg ~a\n" term agg)
            (if agg
                (parse-agg-head (cdr head) (list agg) headr bodyr '())
                (parse-regular-head (cdr head) (append headr (list term)) bodyr))))))

  (define (parse-agg-head head curr headr bodyr aggr)
    (if (null? head)
        (rule (make-atom head-name headr) bodyr (append aggr (list curr)))
        (let ((term (car head)))
          (let ((agg (term->aggregator term)))
            (if agg
                (parse-agg-head (cdr head) (list agg) headr bodyr (append aggr (list curr)))
                (parse-agg-head (cdr head) (append curr (list term)) headr bodyr aggr))))))

  (let ((r (parse-regular-head head-terms '() body)))
    ;(printf "rule: ~a" r)
    r))
  
(struct ledge (to label) #:transparent)

(define (lsuccessors G n)
  (for/fold ((R (set))) ((s (in-set (hash-ref G n (set)))))
    (set-add R (ledge-to s))))

(define (ltranspose G)
  (for/fold ((G* (hash))) (((from tos) (in-hash G)))
    (for/fold ((G* (hash-set G* from (hash-ref G* from (set))))) ((to (in-set tos)))
      (match-let (((ledge v label) to))
        (hash-set G* v (set-add (hash-ref G* v (set)) (ledge from label)))))))

(define (sinks G)
  (for/set (((from tos) (in-hash G)) #:when (set-empty? tos))
    from))

(define (precedence-lgraph P)
  (for/fold ((G (hash))) ((r (in-set P)))
    (let ((head (atom-name (rule-head r))))
      (for/fold ((G (hash-set G head (hash-ref G head (set))))) ((p (in-list (rule-body r))))
        (match p
          ((¬ n)
            (let ((dep (atom-name n)))
              (hash-set G dep (set-add (hash-ref G dep (set)) (ledge head ¬)))))
          (_
            (let ((dep (atom-name p)))
              (hash-set G dep (set-add (hash-ref G dep (set)) (ledge head +)))))
        )))))

(define (lscc-map G)

  ; Part 1: Tarjan's algorithm to find strongly connected components in a directed graph (= each node is reachable from every other node).

  (define index 0)
  (define S '())
  (define Index (hash))
  (define Lowlink (hash))
  (define Onstack (hash))
  (define SCC (set))        ; Strongly connected components.

  (define (strongconnect v)
    (set! Index (hash-set Index v index))
    (set! Lowlink (hash-set Lowlink v index))
    (set! index (add1 index))
    (set! S (cons v S))
    (set! Onstack (hash-set Onstack v #t))

    (for ((w (in-set (lsuccessors G v))))
      (if (not (hash-ref Index w #f))
          (begin
            (strongconnect w)
            (set! Lowlink (hash-set Lowlink v (min (hash-ref Lowlink v) (hash-ref Lowlink w)))))
          (when (hash-ref Onstack w)
              (set! Lowlink (hash-set Lowlink v (min (hash-ref Lowlink v) (hash-ref Index w)))))))

    (when (= (hash-ref Lowlink v) (hash-ref Index v))
      (letrec ((f (lambda (scc)
                    (let ((w (car S)))
                      (set! S (cdr S))
                      (set! Onstack (hash-set Onstack w #f))
                      ;(printf "~v ~v\n" (hash-ref Index v) w)
                      (set! scc (cons w scc))
                      (if (not (equal? w v))
                          (f scc)
                          (set! SCC (set-add SCC scc)))))))
        (f '()))))

  (for ((v (in-list (hash-keys G))))
    (let ((index (hash-ref Index v #f)))
      (unless index (strongconnect v))))

  ; Part 2: Perform a mapping step. 

  (let loop ((index 0) (SCC SCC) (R (hash)))
    (if (set-empty? SCC)
        R
        (let ((C (set-first SCC)))
          (let ((R*
              (for/fold ((R R)) ((v (in-list C)))
                (hash-set R v index))))
            (loop (add1 index) (set-rest SCC) R*))))))

; adapted from https://rosettacode.org/wiki/Topological_sort#Racket
(define (clean G)
  (define G* (hash-copy G))
  (for ([(from tos) G])
    ; remove self dependencies
    (hash-set! G* from (set-remove tos from))
    ; make sure all nodes are present in the ht
    (for ([to tos]) (hash-update! G* to (λ(_)_) (set))))
  G*)
 
(define (incoming G)
  (define in (make-hash))
  (for* ([(from tos) G] [to tos])
    (hash-update! in to (λ(fs) (set-add fs from)) (set)))
  in)
 
(define (nodes G)       (hash-keys G))
(define (out G n)       (hash-ref G n (set)))
(define (remove! G n m) (hash-set! G n (set-remove (out G n) m)))
 
(define (topo-sort G*)
  (define G (clean G*))
  (define n (length (nodes G)))
  (define in (incoming G))
  (define (no-incoming? n) (set-empty? (hash-ref in n (set))))
  (let loop ([L '()] [S (list->set (filter no-incoming? (nodes G)))])
    (cond [(set-empty? S)
           (if (= (length L) n)
               (reverse L)
               (error 'topo-sort (~a "cycle detected" G)))]
          [else 
           (define n   (set-first S))
           (define S\n (set-rest S))                
           (for ([m (out G n)])
             (remove! G n m)
             (remove! in m n)
             (when (no-incoming? m)
               (set! S\n (set-add S\n m))))
           (loop (cons n L) S\n)])))
 
; returns list of sets of rule names
(define (strata P)

  (define G-pred (precedence-lgraph P))   ; Compute a precedence graph based on dependencies between the predicates.
  ;(printf "G-pred:\n")(print-map G-pred)(newline)
  (define v2cid (lscc-map G-pred))        ; Determine strongly connected components.
  (printf "v2cid: ~v\n" v2cid)

  (define G-red
    (for/fold ((R (hash))) (((from edges) (in-hash G-pred)))
      (let ((from-cid (hash-ref v2cid from)))
        (for/fold ((R (hash-set R from-cid (hash-ref R from-cid (set))))) ((edge (in-set edges)))
          (hash-set R from-cid (set-add (hash-ref R from-cid) (hash-ref v2cid (ledge-to edge))))))))

  ;(printf "G-red:\n") (print-map G-red)(newline) ; (generate-dot G-red "G-red")
  (define cid-sorted (topo-sort G-red))
  ;(printf "topo: ~v\n" cid-sorted)

  (define cid2C (for/fold ((R (hash))) (((v cid) (in-hash v2cid)))
                        (hash-set R cid (set-add (hash-ref R cid (set)) v))))
  ;(printf "cid2C: ~v\n" cid2C)
  ;(map (lambda (cids) (for/fold ((R (set))) ((cid (in-set cids))) (set-union R (hash-ref cid2C cid)))) cid-sorted))
  (map (lambda (cid) (hash-ref cid2C cid)) cid-sorted))

(define (generate-dot graph name)  
  (let ((dotf (open-output-file (format "~a.dot" name) #:exists 'replace)))
    (fprintf dotf "digraph G {\n")
    (for/fold ((S (set))) (((s ts) graph))
      (unless (set-member? S s)
        (fprintf dotf "~a [label=\"~a\"];\n" s s))
        (for/fold ((S (set-add S s))) ((s* ts))
          (unless (set-member? S s*)
            (fprintf dotf "~a [label=\"~a\"];\n" s* s*))
          (fprintf dotf "~a -> ~a;\n" s s*)
          (set-add S s*)))
      (fprintf dotf "}")
      (close-output-port dotf)))



; returns list of sets of rules
(define (stratify P)
  (define S (strata P))
  ;(printf "strata: ~v\n" S)

  (define strata-rules
    (map (lambda (Preds)
          (for/fold ((R (set))) ((Pred (in-set Preds)))
            (set-union R (for/set ((r (in-set P)) #:when (eq? (atom-name (rule-head r)) Pred)) ; why not lists for "set" of rules?
                            r))))
        S))
  
  (cdr strata-rules)) ; throwing away first (true EDB) stratum 

; Evaluate unquoted expressions in a given environment. Expressions that are not unquoted are not evaluated.
(define (evaluate-unquoted x env)
  (match x
    ((cons 'unquote y) (evaluate (car y) env))
    (_ x)))

; Evaluate x in a given environment of bindings.
(define (evaluate x env)
  ; (printf "evaluate ~a\n" x)
  (let ((RES
      (cond
        ((symbol? x) (hash-ref env x (lambda () (eval x ns)))) ; Look up symbols in the given environment.
        ((list? x)
        (let ((rator (car x))
                (rands (cdr x)))
          (cond
            ((eq? rator 'quote)
              (car rands))
            ((eq? rator 'quasiquote)
              (evaluate-quasi (car rands) env))
            (else
              (let ((proc (evaluate (car x) env))
                    (args (map (lambda (operand) (evaluate operand env)) (cdr x))))
                (apply proc args))))))
        (else x))))
    ; (printf "evaluate ~a => ~a\n" x RES)
    RES))
      

(define (evaluate-quasi x env)
  ; (printf "evaluate-quasi ~a\n" x)
  (let ((RES
      (cond
        ((list? x)
          (let ((rator (car x))
                  (rands (cdr x)))
            (cond
              ((eq? rator 'unquote)
                (evaluate (car rands) env))
              (else (error "evaluate-quasi app" x)))))
        ((vector? x)
          (for/vector ((term (in-vector x)))
            (evaluate-quasi term env)))
        (else x))))
  ; (printf "evaluate-quasi ~a => ~a\n" x RES)
  RES))



; atom = pred + terms*
; returns an extended environment or #f if match fails
(define (match-atom atom tuple env) ; TODO which is the pattern?
  ; (printf "match-atom ~a ~a in ~a\n" atom tuple env)
  (let ((RES
      (if (and (eq? (atom-name atom) (atom-name tuple)) (= (atom-arity atom) (atom-arity tuple)))
          (let match-atom-args ((i 0) (env env)) ; Check unifiability for all argument terms of the atom.
            (if (= i (atom-arity tuple))
                env
                (let ((atom-arg-i (atom-term atom i))
                      (tuple-arg-i (atom-term tuple i)))
                  (let ((env* (match-term atom-arg-i tuple-arg-i env))) ; Try to unify the i-th argument of both atoms.
                    (if env*
                        (match-atom-args (add1 i) env*)
                        #f))))) ; match of the i-th argument failed.
          #f))) ; non-matching pred name or arity
    ; (printf "match-atom ~a ~a in ~a => ~a\n" atom tuple env RES)
    RES))

; term = variable | constant
; TODO CHECK: The pattern must be grounded but may contain wildcards (_).
; returns an extended environment or #f if unification fails.
(define (match-term term pattern env) ; pattern must be grounded
  ; (printf "match-term ~a ~a in ~a\n" term pattern env)
  (let ((RES 
;      (let ((red (evaluate pattern env))) ; Reduce the term if needed.
        (cond
          ((and (atom? term) (atom? pattern)) (match-atom term pattern env))
          ((eq? term '_) env) ; wildcard: always unifies without side effect on env
          ((variable? term) ; variable: current value must match the pattern. If the variable is unbound, this becomes bound.
            (if (hash-has-key? env term)
                  (let ((existing-value (hash-ref env term)))
                      (if (equal? existing-value pattern)
                          env
                          #f))
                  (hash-set env term pattern)))
          ((and (pair? term) (eq? (car pattern) 'quote))
            (if (eq? (cadr term) pattern)
                env
                #f))
          ((equal? term pattern) env)
          (else #f))))
    ; (printf "match-term ~a ~a in ~a => ~a\n" term pattern env RES)
    RES))
      

(define (bind-fact hv env)
  ; (printf "bind-fact ~a ~a\n" hv env)
  (let ((terms 
    (for/list ((i (in-range (atom-arity hv))))
      (let ((x (atom-term hv i)))
        (cond
          ((symbol? x)
            (hash-ref env x (lambda () (error 'bind-fact "no value for ~a in ~a for ~a" x env hv))))
          ((vector? x)
            (bind-fact x env))
          ((and (pair? x) (eq? (car x) 'quote))
            (cadr x))
          (else x))))))
  (let ((new-fact (make-atom (atom-name hv) terms)))
    new-fact)))

(define (fire-rule rule E delta-tuples)
  ;(printf "fire rule ~v E ~v\n" rule E)
  (let ((qresult (run-query (rule-body rule) E delta-tuples)))
    (let ((aggs (rule-aggregates rule)))
      (if (null? aggs)
        (let ((hv (rule-head rule)))
          (for/set ((qr (in-set qresult)))
            (let ((env (car qr))
                  (ptuples (cdr qr)))
              (let ((new-fact (bind-fact hv env)))
                  (cons new-fact ptuples)))))
        (handle-aggs-rule rule qresult)))))

(define (handle-aggs-rule rule qresult) ; qresult = (cons env ptuples)*

  ; (printf "handle aggs ~a ~a\n" rule qresult)

  (define (group-by-key terms env)
    (map (lambda (var) (hash-ref env var (lambda () (error 'group-by-key "no value for ~a in ~a for ~a" var env head)))) terms))

  (define head (rule-head rule))
  (define head-list (vector->list head))
  (define terms (cdr head-list))
  (define aggs (rule-aggregates rule))
  
  (define grouped-values
    (for/fold ((gb-result (hash))) ((qr (in-set qresult)))
      (let ((env (car qr)))
        (let ((gb-key (group-by-key terms env)))
          ; (printf "gb-key ~a\n" gb-key)
          (let ((gb-env (hash-ref gb-result gb-key (hash))))
            (let ((gb-env*
                (for/fold ((gb-env gb-env)) ((agg (in-list aggs)))
                  (let ((agg-terms (cdr agg)))
                    (for/fold ((gb-env gb-env)) ((agg-term (in-list agg-terms)))
                      (let ((current-values (hash-ref gb-env agg-term '())))
                        (hash-set gb-env agg-term (cons (hash-ref env agg-term) current-values))))))))
              (hash-set gb-result gb-key gb-env*)))))))

  ; (printf "grouped values: ~a\n" grouped-values)

  (let ((RES
  (for/fold ((fresh-tuples (set))) (((gb-key gb-env) (in-hash grouped-values)))
    (for/fold ((fresh-tuples fresh-tuples)) ((agg (in-list aggs)))
      (let ((agg-values
          (for/list ((agg (in-list aggs)))
            (let ((args (map (lambda (aggterm) (hash-ref gb-env aggterm)) (cdr agg))))
              ; (printf "apply ~a ~a\n" (car agg) args)
              (apply (car agg) args)))))
        (let ((fresh-tuple (vector->immutable-vector (list->vector (cons (car head-list) (append gb-key agg-values))))))
          (set-add fresh-tuples (cons fresh-tuple 'no-prov))))))
  ))
  (printf "fresh tuples: ~a\n" RES)
  RES)
)



(struct fire-state (atoms env ptuples) #:transparent)

(define (run-query atoms E delta-tuples)
  ;(printf "run query atoms ~a tuples ~a\n" atoms E) ; was `fire-rule`
  (let loop ((work (set (fire-state atoms (hash) (set))))
             (ΔE   (set)))
    (if (set-empty? work)
        ΔE
        (match-let (((fire-state atoms env ptuples) (set-first work)))
        ;(printf "looking at atoms ~v in ~v\n" atoms env)
        (if (null? atoms)
            (loop (set-rest work) (set-add ΔE (cons env ptuples)))
            (let ((av (car atoms))
                  (atoms-rest (cdr atoms)))
              (match av
                ((¬ av) ; duplicating special terms, other strategy: let special forms return results one by one for "fail-fast"
                  (match av
                    ((vector '= p q)
                      (let* (
                             (qq (evaluate q env))
                             (env* (match-term p qq env)))
                        (if env* ; Test whether unification succeeded.
                            (loop (set-rest work) ΔE)
                            (loop (set-add (set-rest work) (fire-state atoms-rest env ptuples)) ΔE))))
                    (_ ; this "datalog": don't bind in -, so either +bound var or _
                      (let e-loop ((E (for/set ((ev (in-set E)) #:when (eq? (atom-name ev) (atom-name av))) ev)))
                        (if (set-empty? E)
                            (begin
                              ;(printf "bind-fact ~a ~a\n" av env)
                            (let ((ptuple (¬ (bind-fact av env)))) ; provenance
                              (loop (set-add (set-rest work) (fire-state atoms-rest env (set-add ptuples ptuple))) ΔE))
                            )
                            (let* ((ev (set-first E))
                                   (env* (match-atom av ev env)))
                                ;(printf "¬ unify result ~a ~a: ~v\n" av ev env*)
                              (if env*
                                  (loop (set-rest work) ΔE)
                                  (let ((negterm (bind-fact ev env)))
                                    (e-loop (set-rest E))))))))))
                ((vector 'DEBUG name)
                  (printf "~a: about to match ~a with ~a\n\n" name (cadr atoms) env)
                  (loop (set-add (set-rest work) (fire-state atoms-rest env ptuples)) ΔE))
                ((vector '= p q)
                    (let (
                          (qq (evaluate q env)))
                        (let ((env* (match-term p qq env)))
                        (if env*
                            (loop (set-add (set-rest work) (fire-state atoms-rest env* ptuples)) ΔE)
                            (loop (set-rest work) ΔE)))))
                ((vector '*Recent* p)
                  (let ((matches (match-all-atoms p delta-tuples env)))
                    (let ((new-work (for/set ((m (in-set matches)))
                                                        (fire-state atoms-rest (cdr m) (set-add ptuples (car m))))))
                      (loop (set-union (set-rest work) new-work) ΔE))))
                    ;(loop (set-union (set-rest work) new-work) ΔE)))
                (_ 
                  (let ((matches (match-all-atoms av E env)))
                    (let ((new-work (for/set ((m (in-set matches)))
                                                        (fire-state atoms-rest (cdr m) (set-add ptuples (car m))))))
                      (loop (set-union (set-rest work) new-work) ΔE))))
                  )))))))

; returns set of (tuple . bindings)
(define (match-all-atoms atom E env)
  ; (printf "match-atom ~a ~a ~a\n" atom (set-count E) env)
  (let e-loop ((E E) (matches (set)))
    (if (set-empty? E)
        matches
        (let ((ev (set-first E)))
          (let ((env* (match-atom atom ev env)))
            ;(when m (printf "unify result: ~v\n" m))
            (if env*
;                (e-loop (set-rest E) (set-add work-acc (fire-state remaining-preds env* (set-add ptuples ev)))))
                (e-loop (set-rest E) (set-add matches (cons ev env*))) ; tuple that matched + extended env
                (e-loop (set-rest E) matches)))))))

(define (sort-tuples tuples)
  (let ((tuple-list (set->list tuples)))
    (sort (map ~a tuple-list) string<?)))

(define (print-map m)
  (for (((key value) (in-hash m)))
    (printf "~a -> ~a\n" key value)))


(module+ main
  (:- #(R x #:sum y) #(A b) #(C d e))
)