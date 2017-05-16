#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         racket/set
         syntax/id-table
         syntax/parse
         syntax/stx
         "util.rkt")
(provide (all-defined-out))

;; IMMBINDING : (GSTable Identifier Binding)
;; Connects identifiers to the expressions they are immediately bound to.
(define IMMBINDING (make-var-get/set #f))

;; Binding =
;; | #f               -- unknown (eg define-values w/o values rhs, set!)
;; | Tag              -- expr, not set!

;; FIXME: not a lattice! diverges on modfix w/ set!

;; ----------------------------------------

;; IMMBINDING-pre : Syntax -> Void
(define (IMMBINDING-pre stx)
  (define (bind vars rhs)
    (define exprs (rhs->values rhs))
    (if (= (length (stx->list vars)) (length exprs))
        (for-each IMMBINDING (stx->list vars) (map tag exprs))
        (for ([var (stx->list vars)]) (IMMBINDING var #f))))
  (define (rhs->values rhs)
    (syntax-parse rhs
      #:literal-sets (kernel-literals) #:literals (values)
      [(#%plain-app values e ...)
       (syntax->list #'(e ...))]
      [_ (list rhs)]))
  (syntax-parse stx
    #:literal-sets (kernel-literals) #:literals (values)
    [(define-values (var:id ...) rhs)
     (bind #'(var ...) #'rhs)]
    [(let-values ([(var:id ...) rhs] ...) body ...)
     (for ([vars (in-list (syntax->list #'((var ...) ...)))]
           [rhs (in-list (syntax->list #'(rhs ...)))])
       (bind vars rhs))]
    [(letrec-values ([(var:id ...) rhs] ...) body ...)
     (for ([vars (in-list (syntax->list #'((var ...) ...)))]
           [rhs (in-list (syntax->list #'(rhs ...)))])
       (bind vars rhs))]
    [(letrec-syntaxes+values _sbinds ([(vvar:id ...) vrhs] ...) body ...)
     (for ([vars (in-list (syntax->list #'((vvar ...) ...)))]
           [rhs (in-list (syntax->list #'(vrhs ...)))])
       (bind vars rhs))]
    [(set! var e)
     (IMMBINDING #'var #f)]
    [_ (void)]))

;; ----------------------------------------

(define (analyze-binding-immediate stx)
  (traverse stx IMMBINDING-pre void))
