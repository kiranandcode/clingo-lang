#lang racket
(require clingo)

(with-solver
    (lambda ()
      (add-clingo-constraint! '(person (|| alice bob sally 1)))
      (add-clingo-rule!
       (:- '(good P)
           `(person P)
           `(!= P 1)
           (card-eq 1 `(person P))))
      (clingo-solve)
      ))
