#lang racket

(require "unsafe.rkt")
(provide clingo-control? fresh-clingo-control)

(define-struct clingo-control (control))

(define (fresh-clingo-control)
  (clingo-control (clingo-control-new '[] #f #f 20)))

(define clingo-current-part (make-parameter "base"))
(define clingo-current-part (make-parameter "base"))

(define (add-clingo-rule ctrl rule  #:part [part (clingo-current-part)])
  (void))

