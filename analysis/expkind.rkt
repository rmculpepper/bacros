#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         racket/set
         syntax/id-table
         syntax/parse
         "../lib.rkt")
(provide (all-defined-out))

;; ============================================================

;; LAMBDAEXP : (GSTable Syntax/Tag LambdaInfo)
;; Records what expressions are lambda-expressions.
(define LAMBDAEXP (make-tag-get/set #f))

;; LambdaInfo =
;; | (Lambda (Im/ProperListof Identifier) Tag)
;; | (CaseLambda (Listof Lambda))
;; | #f             -- not a lambda

(struct Lambda (formals body) #:transparent)
(struct CaseLambda (cases) #:transparent)

;; ----------------------------------------

;; VAREXP : (GSTable Syntax/Tag VarInfo)
;; Records what expressions are variable references.
(define VAREXP (make-tag-get/set #f))

;; VarInfo =
;; | Identifier   -- variable reference
;; | #f           -- not a variable reference

;; ----------------------------------------

(define (exp-kinds-pre stx)
  (syntax-parse stx
    #:literal-sets (kernel-literals)
    ;; ----
    [var:id
     (VAREXP (tag stx) #'var)]
    [(#%top . var:id)
     (VAREXP (tag stx) #'var)]
    ;; ----
    [(#%plain-lambda formals e ... e*)
     (LAMBDAEXP (tag stx)
                (Lambda (unwrap-formals #'formals) (tag #'e*)))]
    [(case-lambda [formals e ... e*] ...)
     (LAMBDAEXP (tag stx)
                (CaseLambda
                 (for/list ([formals (in-list (syntax->list #'(formals ...)))]
                            [body (in-list (syntax->list #'(e* ...)))])
                   (Lambda (unwrap-formals formals) (tag body)))))]
    ;; ----
    [_ (void)]))

(define (unwrap-formals stx)
  (syntax-parse stx
    [(var:id ...)
     (syntax->list #'(var ...))]
    [(var:id ... . rest:id)
     (syntax->list (append (syntax->list #'(var ...)) #'rest))]))

;; ----------------------------------------

;; analyze-expkind : Syntax -> Void
(define (analyze-expkind stx)
  (traverse stx exp-kinds-pre))
