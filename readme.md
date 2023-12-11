# A `#lang clingo` clingo integration with Racket
Aim: to be able to call Clingo (an ASP solver) directly from Racket.

```
#lang clingo

(person (|| 'alice 'bob))

(evil 'alice)

(:- (good p)
    (person p) (not (evil p)))

;; returns '((person alice) (person bob)
;;           (evil alice)
;;           (good bob))
```

You'll need libclingo installed on your system.

For example, on debian-based systems do:
```
sudo apt install gringo 
```

Files of interest:
- see `unsafe.rkt` for an FFI binding to libclingo (currently hard codes the path to libclingo.so)
- see `main.rkt` for an example use of the FFI binding (ideally at the end, we'd like to have a #lang)
