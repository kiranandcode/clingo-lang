#lang racket
(require
  (lib "clingo-lib/lang.rkt")
  (lib "clingo-lib/control.rkt")
  (for-syntax syntax/parse))
(provide
  #%datum #%top #%app quote #%top-interaction
  set-clingo-option! add-clingo-rule! add-clingo-constraint!
  with-solver clingo-solve
  (rename-out [clingo-module-begin #%module-begin]
              [clingo-rule :-]))

(define-syntax (clingo-handle-form stx)
  (syntax-parse stx #:literals (set-clingo-option! clingo-rule)
    [(_ (set-clingo-option! k vl)) #'(set-clingo-option k vl)]
    [(_ (clingo-rule forms ...))
     #'(add-clingo-rule! (clingo-rule forms ...))]
    [(_ c)
     #'(add-clingo-constraint! (clingo-constraint c))]))

(define-syntax (clingo-module-begin stx)
  (syntax-parse stx
    [(_ form ...)
     #'(#%module-begin
        (with-solver
            (lambda ()
              (clingo-handle-form form)
              ...
              (clingo-solve))))]))
