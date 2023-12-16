#lang racket
(require "control.rkt" "rule.rkt")
(provide with-solver
         add-clingo-rule! clingo-ground clingo-solve
         set-clingo-option! add-clingo-constraint!
         add-clingo-show-constraint!
         rule card-between card-eq)
