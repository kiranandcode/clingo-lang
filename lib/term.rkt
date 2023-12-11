#lang racket
(require "unsafe.rkt")

(provide
 term?
 inf sup
 term->string
 symbol->term)

(define-struct infinum () 
  #:methods gen:custom-write
  [(define write-proc (lambda (_ port mode) (write-string "#inf" port)))])
(define inf (make-infinum) )
(define-struct supremum () 
  #:methods gen:custom-write
  [(define write-proc (lambda (_ port mode) (write-string "#sup" port)))])
(define sup (make-supremum))

(define term?
  (flat-rec-contract term?
   (or/c
    infinum?              ;; #inf
    supremum?             ;; #sup
    number?               ;; 1
    string?               ;; "hello"
    symbol?               ;; a
    (list/c '-
            (or/c
             symbol?
             (cons/c symbol? (listof term?)))) ;; (- a) or (- (f x y))
    (cons/c symbol? (listof term?))))) ;; (f x y)

(define (term->string term)
  (-> term? string?)
  (match term
    [(struct infinum ()) "#inf"]
    [(struct supremum ()) "#sup"]
    [n #:when (number? n) (number->string n)]
    [s #:when (string? s) (format "\"~a\"" s)]
    [s #:when (symbol? s) (symbol->string s)]
    [`(- ,s) #:when (symbol? s) (format "-~a" s)]
    [`(- (,s ,@args)) #:when (symbol? s)
                      (format "-~a(~a)" s
                              (string-join
                               (map term->string args) ","))]
    [`(,s ,@args) #:when (symbol? s)
                  (format "~a(~a)" s
                          (string-join
                           (map term->string args) ","))]))

(define/contract (symbol->term sym)
  (-> any/c term?)
  (define symbol-type (clingo-symbol-type sym))
  (match symbol-type
    ['clingo-symbol-type-infimum inf]
    ['clingo-symbol-type-supremum sup]
    ['clingo-symbol-type-number (clingo-symbol-number sym)]
    ['clingo-symbol-type-string (clingo-symbol-string sym)]
    ['clingo-symbol-type-function
     (define is-positive (clingo-symbol-is-positive sym))
     (define f (string->symbol (clingo-symbol-name sym)))
     (define args (map symbol->term (clingo-symbol-arguments sym)))
     (define expr (if (null? args) f (cons f args)))
     (if is-positive
         expr
         (list '- expr))]))

