#lang racket
(require "term.rkt" racket/struct)

(provide
 atom? atom->string
 card-between card-eq
 rule? rule rule->string)

(module+ test (require rackunit))

(define-struct card-between (low high set)
  #:constructor-name make-card-between-internal
  #:name card-between-internal)

(define-struct card-eq (value contents)
    #:constructor-name make-card-eq-internal
    #:name card-eq-internal)

(define numeric-range? (list/c '.. number? number?))

(define (numeric-range->string range)
  (-> numeric-range? string?)
  (match range
    [`(.. ,low ,high)
     (format "~a..~a" low high)]))

(define atom-arg?
  (flat-rec-contract atom-arg?
   (or/c
    number?
    symbol? ;; alice
    (cons/c '|| (non-empty-listof atom-arg?)) ;; (|| a b) ==> a;b
    (cons/c symbol? (non-empty-listof (or/c number? numeric-range? atom-arg?))) ;; (married alice claire) ==> married(alice, claire)
    )))

(define atom?
  (flat-rec-contract atom?
   (or/c
    card-between?
    card-eq?
    symbol? ;; alice
    number?
    numeric-range?
    (list/c (or/c '+ '- '* '/) atom? atom?)
    (list/c (or/c '= '!= '< '> '<= '>=) atom? atom?)
    (cons/c ': (cons/c atom? (listof atom?)))
    (cons/c 'subset (listof atom?))
    (list/c 'not symbol?)  ;; (not a) ==> not a
    (list/c 'not (cons/c symbol? (non-empty-listof (or/c number? numeric-range? atom?))))  ;; (not (f a b)) ==> not f(a,b)
    (cons/c '|| (non-empty-listof atom?)) ;; (|| a b) ==> a;b
    (cons/c symbol? (non-empty-listof (or/c number? numeric-range? atom?))) ;; (married alice claire) ==> married(alice, claire)
    )))


(define/contract (atom->string atom)
  (-> atom? string?)
  (match atom
    [cb #:when (card-between? cb) (card-between->string cb)]
    [ce #:when (card-eq? ce) (card-eq->string ce)]
    [n #:when (number? n) (format "~a" n)]
    [s #:when (symbol? s) (symbol->string s)]
    [r #:when (numeric-range? r) (numeric-range->string r)]
    [`(+ ,l ,r) (format "(~a) + (~a)" (atom->string l) (atom->string r))]
    [`(- ,l ,r) (format "(~a) - (~a)" (atom->string l) (atom->string r))]
    [`(* ,l ,r) (format "(~a) * (~a)" (atom->string l) (atom->string r))]
    [`(/ ,l ,r) (format "(~a) / (~a)" (atom->string l) (atom->string r))]
    [`(= ,l ,r) (format "(~a) = (~a)" (atom->string l) (atom->string r))]
    [`(!= ,l ,r) (format "(~a) != (~a)" (atom->string l) (atom->string r))]
    [`(< ,l ,r) (format "(~a) < (~a)" (atom->string l) (atom->string r))]
    [`(> ,l ,r) (format "(~a) > (~a)" (atom->string l) (atom->string r))]
    [`(<= ,l ,r) (format "(~a) <= (~a)" (atom->string l) (atom->string r))]
    [`(>= ,l ,r) (format "(~a) >= (~a)" (atom->string l) (atom->string r))]
    [`(: ,head ,@deps)
     (format "~a:~a" (atom->string head)
             (string-join (map atom->string deps) ","))]
    [`(subset ,@args)
     (define args-str (map atom->string args))
     (format "{~a}" (string-join args-str ";"))]
    [`(not ,s) (format "not ~a" (atom->string s))]
    [`(|| ,@args)
     (define args-str (map atom->string args))
     (string-join args-str ";")]
    [`(,s ,@args)
     #:when (symbol? s)
     (define args-str (map atom->string args))
     (format "~a(~a)" s (string-join args-str ","))]))

(module+ test
  (check-equal? (atom->string 'a) "a")
  (check-equal? (atom->string '(f a b)) "f(a,b)")
  (check-equal? (atom->string '(not (f a b))) "not f(a,b)")
  (check-equal? (atom->string '(|| (f a b) (g a b))) "f(a,b);g(a,b)")
  (check-equal? (atom->string '(f (|| a b))) "f(a;b)")
  (check-equal? (atom->string '(f (|| a b) 1)) "f(a;b,1)")
  (check-equal? (atom->string '(f (.. 1 10))) "f(1..10)")
  (check-equal? (atom->string '(f (.. 1 10) (.. 1 10) a)) "f(1..10,1..10,a)"))

(define/contract (card-between  #:low [low #false] #:high [high #false] . contents)
  (->* () (#:low (or/c integer? #f) #:high (or/c integer? #f)) #:rest (listof atom?) card-between?)
  (make-card-between-internal low high contents))

(define/contract (card-between->string cbetween)
  (-> card-between? string?)
  (match cbetween
    [(struct card-between-internal (low high set))
     (format "~a{~a}~a"
             (if low (format "~a " low) "")
             (string-join (map atom->string set) ";")
             (if high (format " ~a" high) ""))]))

(define/contract (card-eq  value . contents)
  (->* (integer?) #:rest (listof atom?) card-eq?)
  (make-card-eq-internal value contents))

(define/contract (card-eq->string ceq)
  (-> card-eq? string?)
  (match ceq
    [(struct card-eq-internal (value contents))
     (format "{~a} = ~a"
             (string-join (map atom->string contents) ";")
             value)]))

(define rule-head-constraint?
  (or/c
   #false
   (cons/c 'subset  (listof atom?)) ;; (subset a b) ==> {a;b}
   (cons/c '|| (listof atom?)) ;; (|| a b c)            ==> a; b; c
   card-between? ;; (card-between #:low 1 #:high 2 (a b)) ==> 1 {a;b} 2
   card-eq?      ;; (card-eq 1 a b c) ===> {a;b;c} = 1
   atom?
   ))

(define/contract (rule-head-constraint->string constraint)
  (-> rule-head-constraint? string?)
  (match constraint
    [#false ""]
    [`(subset ,@args)
     (define args-str (map atom->string args))
     (format "{~a}" (string-join args-str ";"))]
    [`(|| ,@args)
     (define args-str (map atom->string args))
     (format "~a" (string-join args-str ";"))]
    [v #:when (card-between? v) (card-between->string v)]
    [v #:when (card-eq? v) (card-eq->string v)]
    [v (atom->string v)]))

(define rule-body-constraint? (listof atom?))

(define/contract (rule-body-constraint->string body-constraint)
  (-> rule-body-constraint? string?)
  (define args-str (map atom->string body-constraint))
  (format "~a" (string-join args-str ",")))

(define/contract (rule-guard head body _)
  (-> rule-head-constraint? rule-body-constraint? any/c any)
  (values head body))

(define-struct rule
  (head body)
  #:guard rule-guard
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (_) 'rule)
      (lambda (obj) (list (rule->string obj)))))])

(define/contract (rule->string rule)
  (-> rule? string?)
  (define head (rule-head rule))
  (define body (rule-body rule))
  (format "~a:- ~a."
          (if head (format "~a "(rule-head-constraint->string head)) "")
          (rule-body-constraint->string body)))


(module+ test
  (check-equal?
   (rule->string
    (rule #f
          `((f a b))))
   ":- f(a,b).")
  (check-equal?
   (rule->string
    (rule `(|| a b c)
          (list
           `(|| (f a b) (g a b))
           `(g b c)
           )))
   "a;b;c :- f(a,b);g(a,b),g(b,c)."))
