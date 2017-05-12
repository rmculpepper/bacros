#lang racket/base
(require racket/base
         racket/dict
         (rename-in racket/match [match-define defmatch])
         syntax/id-table
         syntax/parse
         syntax/parse/experimental/template
         "tag.rkt")
(provide (all-from-out "tag.rkt")
         (all-defined-out))

;; mods : Nat
;; Global counter for modifications.
(define mods 0)

;; modfix : (-> Void) -> Void
;; Runs given function until no more modifications.
(define (modfix proc)
  (let ([old-mods mods])
    (proc)
    (unless (= mods old-mods)
      (eprintf "** new mods, going again\n")
      (modfix proc))))

(struct gs (dict top join get-key)
        #:property prop:procedure
        (case-lambda
          [(self k)
           (defmatch (gs dict top join get-key) self)
           (dict-ref dict (get-key k) top)]
          [(self k v)
           (defmatch (gs dict top join get-key) self)
           (let* ([old (dict-ref dict (get-key k) top)]
                  [new (join old v)])
             (unless (equal? new old)
               (set! mods (add1 mods)))
             (dict-set! dict (get-key k) new))]))

;; make-get/set : Dict[K=>V] V (V V -> V) #:key (K* -> K)
;;             -> (case-> (K* -> V) (K* V -> Void))
(define (make-get/set dict top join #:key [get-key values])
  (gs dict top join get-key))

(define (make-tag-get/set top join)
  (make-get/set (make-hash) top join #:key (lambda (x) (if (syntax? x) (tag x) x))))

(define (make-var-get/set top join)
  (make-get/set (make-free-id-table) top join #:key values))

(define (dump-tag-function self)
  (defmatch (gs dict top join get-key) self)
  (define keys (sort (dict-keys dict) <))
  (for ([k (in-list keys)])
    (printf "~s => ~v  -- ~a\n" k (dict-ref dict k) (tag-summary k))))

(define (dump-var-function self)
  (defmatch (gs dict top join get-key) self)
  (for ([(k v) (in-dict dict)])
    (printf "~s => ~v\n" k v)))

;; ----------------------------------------

;; traverse : Proc Proc Syntax -> Void
(define (traverse pre post stx)
  (define (recur . xs) (for ([x (in-list xs)]) (traverse pre post x)))
  (define (recur* . xss) (for ([xs (in-list xss)]) (apply recur (syntax->list xs))))
  (begin
    (pre stx)
    (syntax-parse stx
      #:literal-sets (kernel-literals)
      ;; Fully-Expanded Programs
      ;; -- module body
      [(#%plain-module-begin form ...)
       (modfix (lambda () (recur* #'(form ...))))]
      ;; -- module-level form
      [(#%provide . _) (void)]
      [(begin-for-syntax . _) (void)]
      [(module . _) (void)]
      [(module* . _) (void)]
      [(#%declare . _) (void)]
      ;; -- general top-level form
      [(define-values vars e)
       (recur #'e)]
      [(define-syntaxes . _) (void)]
      [(#%require . _) (void)]
      ;; -- expr
      [var:id (void)]
      [(#%plain-lambda (var ...) e ...)
       (recur* #'(e ...))]
      [(case-lambda [(var ...) e ...] ...)
       (recur* #'(e ... ...))]
      [(if e1 e2 e3)
       (recur #'e1 #'e2 #'e3)]
      [(begin e ...)
       (recur* #'(e ...))]
      [(begin0 e ...)
       (recur* #'(e ...))]
      [(let-values ([vars rhs] ...) body ...)
       (recur* #'(rhs ... body ...))]
      [(letrec-values ([vars rhs] ...) body ...)
       (modfix (lambda () (recur* #'(rhs ...))))
       (recur* #'(body ...))]
      [(letrec-syntaxes+values ([svars srhs] ...) ([vvars vrhs] ...) body ...)
       (modfix (lambda () (recur* #'(vrhs ...))))
       (recur* #'(body ...))]
      [(set! var e)
       (recur #'e)]
      [(quote d) (void)]
      [(quote-syntax . _) (void)]
      [(with-continuation-mark e1 e2 e3)
       (recur #'e1 #'e2 #'e3)]
      [(#%top . var:id) (void)]
      [(#%variable-reference . _) (void)]
      [(#%expression e)
       (recur #'e)]
      ;; -- application
      [(#%plain-app e ...)
       (recur* #'(e ...))]
      [_ (raise-syntax-error #f "unhandled syntax" stx)])
    (post stx)))
