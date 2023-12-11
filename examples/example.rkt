#lang clingo

(person (|| 'alice 'bob))

(evil 'alice)

(:- (good p)
    (person p) (not (evil p)))

;; returns '((person alice) (person bob)
;;           (evil alice)
;;           (good bob))
