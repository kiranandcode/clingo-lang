#lang racket
(require "unsafe.rkt")

(provide set-clingo-control-config!)

(define/contract (set-clingo-control-config! ctrl values)
  (-> any/c (listof (cons/c string? any/c)) void)
  (define conf (clingo-control-configuration ctrl))
  (define root (clingo-configuration-root conf))
  (for ([pair (in-list values)])
    (define key (car pair))
    (define value (cdr pair))
    (define sub-key-root
        (clingo-configuration-map-at conf root key))
    (clingo-configuration-value-set conf sub-key-root (format "~a" value))))

