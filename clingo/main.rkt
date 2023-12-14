#lang racket
(require clingo-lib)

(provide
 (except-out (all-from-out clingo-lib) rule)
 :-)

(define (:- head . tail)
  (rule head tail))
