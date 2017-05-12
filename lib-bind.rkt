#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         racket/set
         syntax/id-table
         syntax/parse
         "lib.rkt")
(provide (all-defined-out))

;; Connects identifiers to the expressions they are bound to.

;; Binding =
;; | #f              -- bound elsewhere (bottom)
;; | Tag             -- tag of initial binding rhs expr
;; | 'top            -- mutated (top)

;; b-join : Binding Binding -> Binding
(define (b-join b1 b2)
  (cond [(eq? b1 #f) b2]
        [(eq? b2 #f) b1]
        [(equal? b1 b2) b1]
        [else 'top]))

(define BINDING (make-var-get/set #f b-join))

;; ----------------------------------------

;; analyze-BINDING : Syntax -> Void
(define (analyze-BINDING stx)
  (syntax-parse stx
    #:literal-sets (kernel-literals)
    [(define-values (var:id) e)
     (BINDING #'var (tag e))]
    [(define-values vars e)
     (void)]
    [(let-values ([(var:id) rhs] ...) body ...)
     (for ([var (in-list (syntax->list #'(var ...)))]
           [rhs (in-list (syntax->list #'(rhs ...)))])
       (BINDING var (tag rhs)))]
    [(letrec-values ([(var:id) rhs] ...) body ...)
     (for ([var (in-list (syntax->list #'(var ...)))]
           [rhs (in-list (syntax->list #'(rhs ...)))])
       (BINDING var (tag rhs)))]
    [(letrec-syntaxes+values _sbinds ([(vvar:id) vrhs] ...) body ...)
     (for ([var (in-list (syntax->list #'(vvar ...)))]
           [rhs (in-list (syntax->list #'(vrhs ...)))])
       (BINDING var (tag rhs)))]
    [(set! var e)
     (BINDING #'var (tag #'e))]
    [_ (void)]))

;; ============================================================

;; Records what expressions are lambda-expressions.

;; LambdaRecord =
;; | 'bot           -- uninitialized (bot)
;; | (lambda-record (Im/ProperListof Identifier) Tag)
;; | (case-lambda-record (Listof lambda-record))
;; | #f             -- not a lambda (top)

(struct lambda-record (formals body) #:transparent)
(struct case-lambda-record (cases) #:transparent)

(define (lr-join a1 a2)
  (cond [(eq? a1 'bot) a2]
        [(eq? a2 'bot) a1]
        [(equal? a1 a2) a1]
        [else #f]))

(define LAMBDAEXP (make-tag-get/set 'bot lr-join))

;; ----------------------------------------

;; analyze-LAMBDAEXP : Syntax -> Void
(define (analyze-LAMBDAEXP stx)
  (syntax-parse stx
    #:literal-sets (kernel-literals)
    [(#%plain-lambda formals e ... e*)
     (LAMBDAEXP (tag stx) (lambda-record (unwrap-formals #'formals) (tag #'e*)))]
    [(case-lambda [formals e ... e*] ...)
     (LAMBDAEXP (tag stx)
                (case-lambda-record
                 (for/list ([formals (in-list (syntax->list #'(formals ...)))]
                            [body (in-list (syntax->list #'(e* ...)))])
                   (lambda-record (unwrap-formals formals) (tag body)))))]
    [_ (void)]))
