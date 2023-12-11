#lang racket

(require "unsafe.rkt" "rule.rkt" "term.rkt" "config.rkt")
(provide with-solver add-clingo-rule! clingo-ground clingo-solve set-clingo-option!
         add-clingo-constraint!)
 
(define-struct clingo-control (control [grounded #:mutable]))

(define (fresh-clingo-control)
  (clingo-control (clingo-control-new '[] #f #f 20) #f))

(define (cleanup-clingo-control control)
  (clingo-control-free (clingo-control-control control)))

(define clingo-current-part (make-parameter "base"))
(define clingo-current-control (make-parameter #f))

(define (with-solver f)
  (define result #false)
  (define ctx (fresh-clingo-control))
  (parameterize ([clingo-current-control ctx])
    (set! result (f)))
  (cleanup-clingo-control ctx)
  result)

(define (set-clingo-option! key vl #:control [ctrl (clingo-current-control)])
  (unless ctrl
    (error "Attempt set parameter outside of a control section"))
  (set-clingo-control-config! (clingo-control-control ctrl)
                              (list (cons key vl))))

(define (add-clingo-rule!
         rule
         #:control [ctrl (clingo-current-control)]
         #:part [part (clingo-current-part)])
  (unless ctrl
    (error "Attempt declare rule outside of a control section"))
  #; (println (format "sending rule \"~a\"" (rule->string rule)))
  (clingo-control-add
   (clingo-control-control ctrl) part '[]
   (rule->string rule)))

(define (add-clingo-constraint!
         constraint
         #:control [ctrl (clingo-current-control)]
         #:part [part (clingo-current-part)])
  (unless ctrl
    (error "Attempt declare constraint outside of a control section"))
  #; (println (format "sending constraint \"~a\"" (format "~a." (constraint->string constraint))))
  (clingo-control-add
   (clingo-control-control ctrl) part '[]
   (format "~a." (constraint->string constraint))))

(define (clingo-ground #:parts [parts (list (clingo-current-part))]
                      #:control [ctrl (clingo-current-control)])
  (unless ctrl
    (error "Attempt ground outside of a control section"))
  (unless (not (clingo-control-grounded ctrl))
    (error "Attempt to ground multiple times..."))
  (define cl-parts
    (map (lambda (part) (make-clingo-part part #f 0)) parts))
  (clingo-control-ground (clingo-control-control ctrl) cl-parts #f #f)
  (set-clingo-control-grounded! ctrl #true))

(define (clingo-solve #:parts [parts (list (clingo-current-part))]
                      #:control [ctrl (clingo-current-control)])
  (unless ctrl
    (error "Attempt solve outside of a control section"))
  (unless (clingo-control-grounded ctrl)
    (clingo-ground #:parts parts #:control ctrl))

  (define solve-handle
    (clingo-control-solve (clingo-control-control ctrl)
                          'clingo-solve-mode-yield '[] #f #f))

  (define models '[])
  (define (loop)
    (clingo-solve-handle-resume solve-handle)
    (define model (clingo-solve-handle-model solve-handle))
    (when model
      (define symbols (clingo-model-symbols model 'clingo-show-type-shown))
      (define model-rkt
        (for/list ([symbol symbols])
          (symbol->term symbol)))
      (set! models (cons model-rkt models))
      (loop)))
  (loop)
  (clingo-solve-handle-close solve-handle)
  (define result (reverse models))
  (if (equal? (length result) 1)
     (first result)
     result))


