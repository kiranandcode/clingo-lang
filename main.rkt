#lang racket
(require "unsafe.rkt" racket/struct)

(define ctrl (clingo-control-new '[] #f #f 20))

(define (configure-to-enumerate-all-models ctrl)
  (define conf (clingo-control-configuration ctrl))
  (define root (clingo-configuration-root conf))
  (define sub-keys
    (clingo-configuration-map-at conf root "solve.models"))
  (clingo-configuration-value-set conf sub-keys "0"))

(configure-to-enumerate-all-models ctrl)

(clingo-control-add ctrl "base" '[] "a :- not  b. b :- not a. - a :- b.")
(clingo-control-ground ctrl `[,(make-clingo-part "base" #f 0)] #f #f)

(define solve-handle (clingo-control-solve ctrl 'clingo-solve-mode-yield '[] #f #f))

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

(define (symbol->term sym)
  (define symbol-type (clingo-symbol-type sym))
  (match symbol-type
    ['clingo-symbol-type-infimum inf]
    ['clingo-symbol-type-supremum sup]
    ['clingo-symbol-type-number (clingo-symbol-number sym)]
    ['clingo-symbol-type-string (clingo-symbol-string sym)]
    ['clingo-symbol-type-function
     (define is-positive (clingo-symbol-is-positive sym))
     (define is-negative (clingo-symbol-is-negative sym))
     (define f (string->symbol (clingo-symbol-name sym)))
     (define args (map symbol->term (clingo-symbol-arguments sym)))
     (define expr (if (null? args) f (cons f args)))
     (println [list is-positive is-negative])
     (if is-negative
         (list '- expr)
         expr)]))

(define (print-model model)
  (define symbols (clingo-model-symbols model 'clingo-show-type-shown))
  (println (length symbols))

  (println (for/list ([symbol symbols])
             (clingo-symbol-to-string symbol)))
  (displayln
   (for/list ([symbol symbols])
     (symbol->term symbol))))

(define (loop)
  (clingo-solve-handle-resume solve-handle)
  (define model (clingo-solve-handle-model solve-handle))
  (when model
    (print-model model)
    (loop)))
(loop)

(define solve-result (clingo-solve-handle-get solve-handle))
(println solve-result)
(clingo-solve-handle-close solve-handle)


