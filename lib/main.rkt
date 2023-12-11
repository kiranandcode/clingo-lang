#lang racket
(require "unsafe.rkt" "term.rkt" "config.rkt")

(define (configure-to-enumerate-all-models ctrl)
  (set-clingo-control-config! ctrl
   '[("solve.models" . 0)]))

(define (print-model model)
  (define symbols (clingo-model-symbols model 'clingo-show-type-shown))
  (define sym-strs
    (for/list ([symbol symbols])
      (clingo-symbol-to-string symbol)))
  (define mapped-strs
   (for/list ([symbol symbols])
     (define term (symbol->term symbol))
     (list
      term
      (term->string
       term))))
  (for ([s-str sym-strs]
        [m-pair mapped-strs]
        #:unless (equal? s-str (second m-pair)))
    (displayln (list (first m-pair) "==>" s-str (second m-pair))))
  )

(define ctrl (clingo-control-new '[] #f #f 20))
(configure-to-enumerate-all-models ctrl)

(clingo-control-add ctrl "base" '[] "a :- not  b. b :- not a. - a :- b.")
(clingo-control-ground ctrl `[,(make-clingo-part "base" #f 0)] #f #f)

(define solve-handle (clingo-control-solve ctrl 'clingo-solve-mode-yield '[] #f #f))

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


