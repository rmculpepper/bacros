#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         racket/set
         syntax/id-table
         syntax/parse
         "util.rkt")
(provide (all-defined-out))

;; TAIL : (GSTable Syntax/Tag Tag/#f)
;; Records what expressions are in tail position wrt what enclosing lambda.
(define TAIL (make-tag-get/set #f))

;; analyze-tail : Syntax -> Void
(define (analyze-tail stx)
  (traverse stx tail-pre))

(define (tail-pre stx)
  (define me-tail (TAIL stx))
  (syntax-parse stx
    #:literal-sets (kernel-literals)
    [(#%plain-lambda (var ...) e ... e*)
     (TAIL #'e* (tag stx))]
    [(case-lambda [(var ...) e ... e*] ...)
     (for ([e* (in-list (syntax->list #'(e* ...)))])
       (TAIL e* (tag stx)))]
    [(if e1 e2 e3)
     (when me-tail (TAIL #'e2 me-tail) (TAIL #'e3 me-tail))]
    [(begin e ... e*)
     (when me-tail (TAIL #'e* me-tail))]
    [(let-values BS body ... body*)
     (when me-tail (TAIL #'body* me-tail))]
    [(letrec-values BS body ... body*)
     (when me-tail (TAIL #'body* me-tail))]
    [(letrec-syntaxes+values SBS VBS body ... body*)
     (when me-tail (TAIL #'body* me-tail))]
    [(with-continuation-mark e1 e2 e3)
     (when me-tail (TAIL #'e3 me-tail))]
    [(#%expression e)
     (when me-tail (TAIL #'e me-tail))]
    [_ (void)]))
