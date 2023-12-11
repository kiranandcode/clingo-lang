#lang racket

(require "term.rkt" "rule.rkt" syntax/parse (for-syntax racket/string  racket/base syntax/parse))

#; (provide
 (rename-out [clingo-not not]))

(begin-for-syntax
  (define (is-valid-symbol sym)
    (define str (symbol->string sym))
    (regexp-match "[a-z][A-Za-z0-9_-]*" str))

  (define (char-upcase? c) (equal? c (char-upcase c)))

  (define (is-variable sym)
    (define str (symbol->string sym))
    (char-upcase? (string-ref str 0)))

  (define (make-variable stx)
    (define sym (syntax-e stx))
    (define str (symbol->string sym))
    (define up-first-char (char-upcase (string-ref str 0)))
    (define rest (cdr (string->list str)))
    (define upcase-str (list->string (cons up-first-char rest)))
    (define upcase-sym (string->symbol upcase-str))
    (datum->syntax stx upcase-sym))

  (define current-resolve-symbol-fun (make-parameter (lambda (_) #false)))
  (define (resolve-binding-loc stx)
    (syntax-local-value stx (lambda () ((current-resolve-symbol-fun) stx))))
  (define (resolve-binding-loc-fun stx)
    (syntax-local-value stx (lambda () ((current-resolve-symbol-fun) stx))))

  (define-syntax-class atom-arg
    #:datum-literals (.. ||)
    #:attributes (datum)
    (pattern num:number
      #:attr datum (lambda () #'num))
    (pattern (.. (~or low:number low:id) (~or high:number high:id))
      #:attr datum (lambda () #'`(.. ,low ,high)))
    (pattern 'sym:id
      #:when (is-valid-symbol (syntax-e #'sym))
      #:attr datum (lambda () #''sym))
    (pattern sym:id
      #:when (is-valid-symbol (syntax-e #'sym))
      #:with sym-variable (make-variable #'sym) 
      #:attr datum
      (lambda ()
        (let ([binding-loc (resolve-binding-loc #'sym-variable)])
          (with-syntax ([fake-binder (datum->syntax #'sym #'sym-variable binding-loc)])
            #'(begin (let ([fake-binder 1]) sym-variable)
                     'sym-variable)))))
    (pattern (|| arg:atom-arg ...+)
      #:attr datum
      (lambda ()
        (with-syntax ([(data ...) (map (lambda (f) (f)) (attribute arg.datum))])
          #'(cons '|| (list data ...)))))
    (pattern (sym:id arg:atom-arg ...+)
      #:attr datum
      (lambda ()
        (let ([binding-loc (resolve-binding-loc-fun #'sym)])
          (with-syntax ([fake-binder (resolve-binding-loc #'sym)]
                        [(data ...) (map (lambda (f) (f)) (attribute arg.datum))])
            #'(begin (let ([fake-binder 1]) sym)
                     (cons 'sym (list data ...))))))))

  (define-syntax-class atom
    #:datum-literals (|| not)
    #:attributes (datum)
    (pattern 'sym:id
      #:when (is-valid-symbol (syntax-e #'sym))
      #:attr datum (lambda () #''sym))
    (pattern sym:id
      #:when (is-valid-symbol (syntax-e #'sym))
      #:with sym-variable (make-variable #'sym) 
      #:attr datum
      (lambda ()
        (let ([binding-loc (resolve-binding-loc #'sym-variable)])
          (with-syntax ([fake-binder (datum->syntax #'sym #'sym-variable binding-loc)])
            #'(begin (let ([fake-binder 1]) sym-variable)
                     'sym-variable)))))
    (pattern (not 'sym:id)
      #:when (is-valid-symbol (syntax-e #'sym))
      #:attr datum
      (lambda () #''(not sym)))
    (pattern (not sym:id)
      #:when (is-valid-symbol (syntax-e #'sym))
      #:with sym-variable (make-variable #'sym) 
      #:attr datum
      (lambda ()
        (let ([binding-loc (resolve-binding-loc #'sym-variable)])
          (with-syntax ([fake-binder (datum->syntax #'sym #'sym-variable binding-loc)])
            #'(begin (let ([fake-binder 1]) sym-variable)
                     (list 'not 'sym-variable))))))

    (pattern (not (sym:id arg:atom-arg ...))
      #:when (is-valid-symbol (syntax-e #'sym))
      #:attr datum
      (lambda ()
        (let ([binding-loc (resolve-binding-loc-fun #'sym)])
          (with-syntax ([fake-binder (resolve-binding-loc #'sym)]
                        [(data ...) (map (lambda (f) (f)) (attribute arg.datum))])
            
            #'(begin (let ([fake-binder 1]) sym)
                     (cons 'not (cons 'sym (list data ...))))))))
    (pattern (|| arg:atom ...+)
      #:attr datum
      (lambda ()
        (with-syntax
            ([(data ...) (map (lambda (f) (f)) (attribute arg.datum))])
          #'(cons '|| (list data ...)))))
    (pattern (sym:id arg:atom-arg ...+)
      #:attr datum
      (lambda ()
        (let ([binding-loc (resolve-binding-loc-fun #'sym)]
              [fs (attribute arg.datum)])
          (with-syntax ([fake-binder (resolve-binding-loc #'sym)]
                        [(data ...) (map (lambda (f) (f)) fs)])
            #'(begin (let ([fake-binder 1]) sym)
                     (cons 'sym (list data  ...))))))
      )))

(define-syntax (atom->datum stx)
  (syntax-parse stx
    [(_ data:atom) ((attribute data.datum))]))


(atom->datum (|| 'x y))



#; (begin-for-syntax
  

  (define (is-uppercase sym) (string (symbol->string (syntax-e sym))))

  (define-syntax-class term
    
    )
  )

#; (define-syntax (clingo-not stx)
  (syntax-parse stx
    [(_ term) #'(list 'not #'term)]))

#; (define-syntax (clingo-:- stx)
  (syntax-parse stx
    [(_ :- term terms ...)
     ]))

#;(clingo-not 'a)

#;(:- a (not a))
