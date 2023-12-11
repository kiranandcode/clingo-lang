#lang racket
(require ffi/unsafe ffi/cvector ffi/unsafe/define ffi/unsafe/define/conventions)
(define clingo-path "libclingo")

(provide
 _clingo-literal
 _clingo-atom
 _clingo-id
 _clingo-weight
 (struct-out clingo-weighted-literal)
 _clingo-error
 (struct-out clingo-error)
 clingo-error-string
 clingo-error-code
 clingo-error-message
 clingo-set-error
 _clingo-warning
 clingo-warning-string
 _clingo-logger
 clingo-version
 _clingo-truth-value
 (struct-out clingo-location)
 _clingo-signature
 clingo-signature-create
 clingo-signature-name
 clingo-signature-arity
 clingo-signature-is-positive
 clingo-signature-is-negative
 clingo-signature-is-equal-to
 clingo-signature-is-less-than
 clingo-signature-hash
 _clingo-symbol-type
 _clingo-symbol
 clingo-symbol-create-number
 clingo-symbol-create-supremum
 clingo-symbol-create-infimum
 clingo-symbol-create-string
 clingo-symbol-create-id
 clingo-symbol-create-function
 clingo-symbol-number
 clingo-symbol-name
 clingo-symbol-string
 clingo-symbol-is-positive
 clingo-symbol-is-negative
 clingo-symbol-arguments
 clingo-symbol-type
 clingo-symbol-to-string
 clingo-symbol-is-equal-to
 clingo-symbol-is-less-than
 clingo-symbol-hash
 clingo-add-string
 clingo-parse-term
 _clingo-symbolic-atoms-pointer
 _clingo-symbolic-atom-iterator
 clingo-symbolic-atoms-size
 clingo-symbolic-atoms-begin
 clingo-symbolic-atoms-end
 clingo-symbolic-atoms-find
 clingo-symbolic-atoms-iterator-is-equal-to
 clingo-symbolic-atoms-symbol
 clingo-symbolic-atoms-is-fact
 clingo-symbolic-atoms-is-external
 clingo-symbolic-atoms-literal
 clingo-symbolic-atoms-signatures
 clingo-symbolic-atoms-next
 clingo-symbolic-atoms-is-valid
 _clingo-symbol-callback
 _clingo-theory-term-type
 _clingo-theory-atoms-pointer
 clingo-theory-atoms-term-type
 clingo-theory-atoms-term-number
 clingo-theory-atoms-term-name
 clingo-theory-atoms-term-arguments
 clingo-theory-atoms-term-to-string
 clingo-theory-atoms-element-tuple
 clingo-theory-atoms-element-condition
 clingo-theory-atoms-element-condition-id
 clingo-theory-atoms-element-to-string
 clingo-theory-atoms-size
 clingo-theory-atoms-atom-term
 clingo-theory-atoms-atom-elements
 clingo-theory-atoms-atom-has-guard
 clingo-theory-atoms-atom-guard
 clingo-theory-atoms-atom-literal
 clingo-theory-atoms-atom-to-string
 _clingo-assignment-pointer
 clingo-assignment-decision-level
 clingo-assignment-root-level
 clingo-assignment-has-conflict
 clingo-assignment-has-literal
 clingo-assignment-level
 clingo-assignment-decision
 clingo-assignment-is-fixed
 clingo-assignment-is-true
 clingo-assignment-is-false
 clingo-assignment-truth-value
 clingo-assignment-size
 clingo-assignment-is-total
 #; clingo-assignment-at
 #; clingo-assignment-trail-size
 #; clingo-assignment-trail-begin
 #; clingo-assignment-trail-end
 #; clingo-assignment-trail-at
 _clingo-propagator-check-mode
 _clingo-weight-constraint-type
 clingo-propagate-init-solver-literal
 clingo-propagate-init-add-watch
 clingo-propagate-init-add-watch-to-thread
 #; clingo-propagate-init-remove-watch
 #; clingo-propagate-init-remove-watch-from-thread
 #; clingo-propagate-init-freeze-literal
 clingo-propagate-init-symbolic-atoms
 clingo-propagate-init-theory-atoms
 clingo-propagate-init-number-of-threads
 clingo-propagate-init-set-check-mode
 clingo-propagate-init-get-check-mode
 clingo-propagate-init-assignment
 clingo-propagate-init-add-clause
 _clingo-clause-type
 _clingo-propagate-control-pointer
 clingo-propagate-control-thread-id
 clingo-propagate-control-assignment
 clingo-propagate-control-add-literal
 clingo-propagate-control-add-watch
 clingo-propagate-control-has-watch
 clingo-propagate-control-remove-watch
 clingo-propagate-control-add-clause
 clingo-propagate-control-propagate
 _clingo-propagator-init-callback
 _clingo-propagator-propagate-callback
 _clingo-propagator-undo-callback
 _clingo-propagator-check-callback
 (struct-out clingo-propagator)
 _clingo-theory-sequence-type
 _clingo-heuristic-type
 _clingo-external-type
 _clingo-backend-pointer
 clingo-backend-begin
 clingo-backend-end
 clingo-backend-rule
 clingo-backend-weight-rule
 clingo-backend-minimize
 clingo-backend-project
 clingo-backend-external
 clingo-backend-assume
 clingo-backend-heuristic
 clingo-backend-acyc-edge
 clingo-backend-add-atom
 _clingo-configuration-type
 _clingo-configuration-type-bitset
 _clingo-configuration-pointer
 clingo-configuration-root
 clingo-configuration-type
 clingo-configuration-description
 clingo-configuration-array-size
 clingo-configuration-array-at
 clingo-configuration-map-size
 clingo-configuration-map-has-subkey
 clingo-configuration-map-subkey-name
 clingo-configuration-map-at
 clingo-configuration-value-is-assigned
 clingo-configuration-value-get
 clingo-configuration-value-set
 _clingo-statistics-type
 _clingo-statistics-pointer
 clingo-statistics-root
 clingo-statistics-type
 clingo-statistics-array-size
 clingo-statistics-array-at
 clingo-statistics-array-push
 clingo-statistics-map-size
 clingo-statistics-map-has-subkey
 clingo-statistics-map-subkey-name
 clingo-statistics-map-at
 clingo-statistics-map-add-subkey
 clingo-statistics-value-get
 clingo-statistics-value-set
 _clingo-solve-control-pointer
 _clingo-model-pointer
 _clingo-model-type
 _clingo-show-type
 clingo-model-type
 clingo-model-number
 clingo-model-symbols
 clingo-model-contains
 clingo-model-is-true
 clingo-model-cost
 clingo-model-optimality-proven
 clingo-model-thread-id
 clingo-model-extend
 clingo-model-context
 clingo-solve-control-symbolic-atoms
 clingo-solve-control-add-clause
 _clingo-solve-result
 _clingo-solve-mode
 _clingo-solve-event-type
 _clingo-solve-event-callback
 _clingo-solve-handle-pointer
 clingo-solve-handle-get
 clingo-solve-handle-wait
 clingo-solve-handle-model
 clingo-solve-handle-resume
 clingo-solve-handle-cancel
 clingo-solve-handle-close
 (struct-out clingo-ground-program-observer)
 (struct-out clingo-part)
 _clingo-ground-callback
 _clingo-control-pointer
 clingo-control-new
 clingo-control-free
 clingo-control-load
 clingo-control-add
 clingo-control-ground
 clingo-control-solve
 clingo-control-cleanup
 clingo-control-assign-external
 clingo-control-release-external
 clingo-control-register-propagator
 clingo-control-is-conflicting
 clingo-control-statistics
 clingo-control-interrupt
 clingo-control-clasp-facade
 clingo-control-configuration
 clingo-control-get-const
 clingo-control-has-const
 clingo-control-symbolic-atoms
 clingo-control-theory-atoms
 clingo-control-register-observer
 clingo-control-backend
 _clingo-options-pointer
 _clingo-main-function
 _clingo-default-model-printer
 _clingo-model-printer
 (struct-out clingo-application)
 clingo-options-add
 clingo-options-add-flag
 clingo-main
 (struct-out clingo-script))

(define-ffi-definer define-clingo (ffi-lib clingo-path)
  #:make-c-id convention:hyphen->underscore)

;; Signed integer type used for aspif and solver literals.
(define _clingo-literal _int32)
;; Unsigned integer type used for aspif atoms.
(define _clingo-atom _uint32)
;; Unsigned integer type used in various places.
(define _clingo-id _uint32)
;; Signed integer type for weights in sum aggregates and minimize constraints.
(define _clingo-weight _int32)

(define-cstruct _clingo-weighted-literal
  ([literal _clingo-literal]
   [weight _clingo-weight]))


;; Enumeration of error codes.
;;
;; @note Errors can only be recovered from if explicitly mentioned; most
;; functions do not provide strong exception guarantees.  This means that in
;; case of errors associated objects cannot be used further.  If such an
;; object has a free function, this function can and should still be called.
(define _clingo-error
  (_enum
   '(clingo-error-success   = 0  ;; successful API calls
     clingo-error-runtime   = 1  ;; errors only detectable at runtime like invalid input
     clingo-error-logic     = 2  ;; wrong usage of the clingo API
     clingo-error-bad-alloc = 3  ;; memory could not be allocated
     clingo-error-unknown   = 4)  ;; errors unrelated to clingo
   ))

(define-struct clingo-error (type text) #:transparent)

;; Convert error code into string.
(define-clingo clingo-error-string (_fun _clingo-error -> _string))
;; Get the last error code set by a clingo API call.
;; @note Each thread has its own local error code.
;; @return error code
(define-clingo clingo-error-code (_fun -> _clingo-error))
;; Get the last error message set if an API call fails.
;; @note Each thread has its own local error message.
;; @return error message or NULL
(define-clingo clingo-error-message (_fun -> _string))
;; Set a custom error code and message in the active thread.
;; @param[in] code the error code
;; @param[in] message the error message
(define-clingo clingo-set-error (_fun _clingo-error _string -> _void))

(define (raise-clingo-error)
  (let ([text (clingo-error-message)]
        [code (clingo-error-code)])
    (raise (make-clingo-error code text))))

;; Enumeration of warning codes.
(define _clingo-warning
  (_enum '(
    clingo-warning-operation-undefined = 0 ;;< undefined arithmetic operation or weight of aggregate
    clingo-warning-runtime-error       = 1 ;;< to report multiple errors; a corresponding runtime error is raised later
    clingo-warning-atom-undefined      = 2 ;;< undefined atom in program
    clingo-warning-file-included       = 3 ;;< same file included multiple times
    clingo-warning-variable-unbounded  = 4 ;;< CSP variable with unbounded domain
    clingo-warning-global-variable     = 5 ;;< global variable in tuple of aggregate element
    clingo-warning-other               = 6 ;;< other kinds of warnings
  )))


;; Convert warning code into string.
(define-clingo clingo-warning-string (_fun _clingo-warning -> _string))


;; Callback to intercept warning messages.
;;
;; @param[in] code associated warning code
;; @param[in] message warning message
;; @param[in] data user data for callback
;;
;; @see clingo_control_new()
;; @see clingo_parse_term()
;; @see clingo_parse_program()
(define _clingo-logger
  (_fun _clingo-warning _string _pointer -> _void))

;; Obtain the clingo version.
;;
;; @param[out] major major version number
;; @param[out] minor minor version number
;; @param[out] revision revision number
(define-clingo clingo-version
  (_fun (major : (_ptr o _int)) (minor : (_ptr o _int)) (revision : (_ptr o _int)) -> _void
        -> (values major minor revision)))

;; Represents three-valued truth values.
(define _clingo-truth-value
  (_enum '(
    clingo_truth_value_free  = 0  ;; no truth value
    clingo_truth_value_true  = 1 ;; true
    clingo_truth_value_false = 2  ;; false
  )))


;; Represents a source code location marking its beginnig and end.
;;
;; @note Not all locations refer to physical files.
;; By convention, such locations use a name put in angular brackets as filename.
;; The string members of a location object are internalized and valid for the duration of the process.
(define-cstruct _clingo-location (
  [begin-file _string]  ;; the file where the location begins
  [end-file _string]    ;; the file where the location ends
  [begin-line _size]    ;; the line where the location begins
  [end-line _size]      ;; the line where the location ends
  [begin-column _size]  ;; the column where the location begins
  [end-column _size])   ;; the column where the location ends
)

;; {{{1 signature and symbols

;; @example symbol.c
;; The example shows how to create and inspect symbols.
;;
;; ## Output ##
;;
;; ~~~~~~~~~~~~
;; $ ./symbol 0
;; the hash of 42 is 281474976710698
;; the hash of x is 562949963481760
;; the hash of x(42,x) is 1407374893613792
;; 42 is equal to 42
;; 42 is not equal to x
;; 42 is less than x
;; ~~~~~~~~~~~~
;;
;; ## Code ##

;; @defgroup Symbols Symbols
;; Working with (evaluated) ground terms and related functions.
;;
;; @note All functions in this module are thread-safe.
;;
;; For an example, see @ref symbol.c.

;; @addtogroup Symbols
;; @{

;; Represents a predicate signature.
;;
;; Signatures have a name and an arity, and can be positive or negative (to
;; represent classical negation).
(define _clingo-signature _uint64)

;; @name Signature Functions
;; @{

;; Create a new signature.
;;
;; @param[in] name name of the signature
;; @param[in] arity arity of the signature
;; @param[in] positive false if the signature has a classical negation sign
;; @param[out] signature the resulting signature
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-signature-create
  (_fun _string _uint32 _stdbool (s : (_ptr o _clingo-signature)) -> (b : _stdbool)
        -> (if b s (raise-clingo-error))))

;; Get the name of a signature.
;;
;; @note
;; The string is internalized and valid for the duration of the process.
;;
;; @param[in] signature the target signature
;; @return the name of the signature
(define-clingo clingo-signature-name (_fun _clingo-signature -> _string))

;; Get the arity of a signature.
;;
;; @param[in] signature the target signature
;; @return the arity of the signature
(define-clingo clingo-signature-arity (_fun _clingo-signature -> _uint32))

;; Whether the signature is positive (is not classically negated).
;;
;; @param[in] signature the target signature
;; @return whether the signature has no sign
(define-clingo clingo-signature-is-positive (_fun _clingo-signature -> _stdbool))

;; Whether the signature is negative (is classically negated).
;;
;; @param[in] signature the target signature
;; @return whether the signature has a sign
(define-clingo clingo-signature-is-negative (_fun _clingo-signature -> _stdbool))

;; Check if two signatures are equal.
;;
;; @param[in] a first signature
;; @param[in] b second signature
;; @return whether a == b
(define-clingo clingo-signature-is-equal-to (_fun _clingo-signature _clingo-signature -> _stdbool))

;; Check if a signature is less than another signature.
;;
;; Signatures are compared first by sign (unsigned < signed), then by arity,
;; then by name.
;;
;; @param[in] a first signature
;; @param[in] b second signature
;; @return whether a < b
(define-clingo clingo-signature-is-less-than (_fun _clingo-signature _clingo-signature -> _stdbool))

;; Calculate a hash code of a signature.
;;
;; @param[in] signature the target signature
;; @return the hash code of the signature
(define-clingo clingo-signature-hash (_fun _clingo-signature -> _size))

;; @}

;; Enumeration of available symbol types.
(define _clingo-symbol-type (_enum '(
    clingo-symbol-type-infimum  = 0  ;; the <tt>\#inf</tt> symbol
    clingo-symbol-type-number   = 1  ;; a numeric symbol, e.g., `1`
    clingo-symbol-type-string   = 4  ;; a string symbol, e.g., `"a"`
    clingo-symbol-type-function = 5  ;; a numeric symbol, e.g., `c`, `(1, "a")`, or `f(1,"a")`
    clingo-symbol-type-supremum = 7  ;; the <tt>\#sup</tt> symbol
 )))

;; Represents a symbol.
;;
;; This includes numbers, strings, functions (including constants when
;; arguments are empty and tuples when the name is empty), <tt>\#inf</tt> and <tt>\#sup</tt>.
(define _clingo-symbol (_cpointer 'clingo-symbol))


;; @name Symbol Construction Functions
;; @{

;; Construct a symbol representing a number.
;;
;; @param[in] number the number
;; @param[out] symbol the resulting symbol
(define-clingo clingo-symbol-create-number
  (_fun _int (symbol : (_ptr o _clingo-symbol)) -> _void -> symbol))
;; Construct a symbol representing \#sup.
;;
;; @param[out] symbol the resulting symbol
(define-clingo clingo-symbol-create-supremum
  (_fun (symbol : (_ptr o _clingo-symbol)) -> _void -> symbol))
;; Construct a symbol representing <tt>\#inf</tt>.
;;
;; @param[out] symbol the resulting symbol
(define-clingo clingo-symbol-create-infimum
  (_fun (symbol : (_ptr o _clingo-symbol)) -> _void -> symbol))
;; Construct a symbol representing a string.
;;
;; @param[in] string the string
;; @param[out] symbol the resulting symbol
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-symbol-create-string
  (_fun _string (symbol : (_ptr o _clingo-symbol)) -> (res : _stdbool) ->
        (if res symbol (raise-clingo-error))))
;; Construct a symbol representing an id.
;;
;; @note This is just a shortcut for clingo_symbol_create_function() with
;; empty arguments.
;;
;; @param[in] name the name
;; @param[in] positive whether the symbol has a classical negation sign
;; @param[out] symbol the resulting symbol
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-symbol-create-id
  (_fun _string _stdbool (symbol : (_ptr o _clingo-symbol)) -> (res : _stdbool)
        -> (if res symbol (raise-clingo-error))))
;; Construct a symbol representing a function or tuple.
;;
;; @note To create tuples, the empty string has to be used as name.
;;
;; @param[in] name the name of the function
;; @param[in] arguments the arguments of the function
;; @param[in] arguments_size the number of arguments
;; @param[in] positive whether the symbol has a classical negation sign
;; @param[out] symbol the resulting symbol
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-symbol-create-function
  (_fun _string (arguments : (_list i _clingo-symbol)) [_size = (length arguments)] _stdbool
        (symbol : (_ptr o _clingo-symbol)) -> (res : _stdbool)
        -> (if res symbol (raise-clingo-error))))

;; @}

;; @name Symbol Inspection Functions
;; @{

;; Get the number of a symbol.
;;
;; @param[in] symbol the target symbol
;; @param[out] number the resulting number
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_runtime if symbol is not of type ::clingo_symbol_type_number
(define-clingo clingo-symbol-number
  (_fun _clingo-symbol (number : (_ptr o _int)) -> (res : _stdbool) ->
        (if res number (raise-clingo-error))))
;; Get the name of a symbol.
;;
;; @note
;; The string is internalized and valid for the duration of the process.
;;
;; @param[in] symbol the target symbol
;; @param[out] name the resulting name
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_runtime if symbol is not of type ::clingo_symbol_type_function
(define-clingo clingo-symbol-name
  (_fun _clingo-symbol (name : (_ptr o _string)) -> (res : _stdbool) ->
        (if res name (raise-clingo-error))))
;; Get the string of a symbol.
;;
;; @note
;; The string is internalized and valid for the duration of the process.
;;
;; @param[in] symbol the target symbol
;; @param[out] string the resulting string
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_runtime if symbol is not of type ::clingo_symbol_type_string
(define-clingo clingo-symbol-string
  (_fun _clingo-symbol (name : (_ptr o _string)) -> (res : _stdbool) ->
        (if res name (raise-clingo-error))))
;; Check if a function is positive (does not have a sign).
;;
;; @param[in] symbol the target symbol
;; @param[out] positive the result
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_runtime if symbol is not of type ::clingo_symbol_type_function
(define-clingo clingo-symbol-is-positive
  (_fun _clingo-symbol (positive : (_ptr o _stdbool)) -> (res : _stdbool) ->
        (if res positive (raise-clingo-error))))
;; Check if a function is negative (has a sign).
;;
;; @param[in] symbol the target symbol
;; @param[out] negative the result
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_runtime if symbol is not of type ::clingo_symbol_type_function
(define-clingo clingo-symbol-is-negative
  (_fun _clingo-symbol (negative : (_ptr o _stdbool)) -> (res : _stdbool) ->
        (if res negative (raise-clingo-error))))
;; Get the arguments of a symbol.
;;
;; @param[in] symbol the target symbol
;; @param[out] arguments the resulting arguments
;; @param[out] arguments_size the number of arguments
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_runtime if symbol is not of type ::clingo_symbol_type_function
(define-clingo clingo-symbol-arguments
  (_fun _clingo-symbol
        (arguments : (_ptr o _pointer))
        (arguments-size : (_ptr o _size)) -> (res : _stdbool) ->
        (if res
            (if (equal? arguments-size 0)
                '[]
                (cvector->list
                 (cast arguments _pointer (_cvector o _clingo-symbol arguments-size))))
            (raise-clingo-error))))
;; (_ptr _clingo-symbol arguments_size)
;; Get the type of a symbol.
;;
;; @param[in] symbol the target symbol
;; @return the type of the symbol
(define-clingo clingo-symbol-type
  (_fun _clingo-symbol -> _clingo-symbol-type))
;; Get the size of the string representation of a symbol (including the terminating 0).
;;
;; @param[in] symbol the target symbol
;; @param[out] size the resulting size
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-symbol-to-string-size
  (_fun _clingo-symbol (size : (_ptr o _size)) -> (res : _stdbool) ->
        (if res size (raise-clingo-error))))
;; Get the string representation of a symbol.
;;
;; @param[in] symbol the target symbol
;; @param[out] string the resulting string
;; @param[in] size the size of the string
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;;
;; @see clingo_symbol_to_string_size()
(define-clingo clingo-symbol-to-string-unsafe
  (_fun _clingo-symbol _bytes _size -> (res : _stdbool))
  #:c-id clingo_symbol_to_string)

(define (clingo-symbol-to-string symbol)
  (define size (clingo-symbol-to-string-size symbol))
  (define buf (make-bytes size))
  (unless (clingo-symbol-to-string-unsafe symbol buf size)
    (raise-clingo-error))
  (bytes->string/utf-8 buf #f 0 (- size 1)))

;; @}

;; @name Symbol Comparison Functions
;; @{

;; Check if two symbols are equal.
;;
;; @param[in] a first symbol
;; @param[in] b second symbol
;; @return whether a == b
(define-clingo clingo-symbol-is-equal-to
  (_fun _clingo-symbol _clingo-symbol -> _stdbool))
;; Check if a symbol is less than another symbol.
;;
;; Symbols are first compared by type.  If the types are equal, the values are
;; compared (where strings are compared using strcmp).  Functions are first
;; compared by signature and then lexicographically by arguments.
;;
;; @param[in] a first symbol
;; @param[in] b second symbol
;; @return whether a < b
(define-clingo clingo-symbol-is-less-than
  (_fun _clingo-symbol _clingo-symbol -> _stdbool))
;; Calculate a hash code of a symbol.
;;
;; @param[in] symbol the target symbol
;; @return the hash code of the symbol
(define-clingo clingo-symbol-hash (_fun _clingo-symbol -> _size))

;; @}


;; Internalize a string.
;;
;; This functions takes a string as input and returns an equal unique string
;; that is (at the moment) not freed until the program is closed.
;;
;; @param[in] string the string to internalize
;; @param[out] result the internalized string
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-add-string
  (_fun _string (result : (_ptr o _string)) -> (res : _stdbool) ->
        (if res result (raise-clingo-error))))
;; Parse a term in string form.
;;
;; The result of this function is a symbol. The input term can contain
;; unevaluated functions, which are evaluated during parsing.
;;
;; @param[in] string the string to parse
;; @param[in] logger optional logger to report warnings during parsing
;; @param[in] logger_data user data for the logger
;; @param[in] message_limit maximum number of times to call the logger
;; @param[out] symbol the resulting symbol
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime if parsing fails
(define-clingo clingo-parse-term
  (_fun
   _string _clingo-logger _pointer _uint [symbol : (_ptr o _clingo-symbol)] -> (res : _stdbool) ->
   (if res symbol (raise-clingo-error))))


;; {{{1 symbolic atoms

;; @example symbolic-atoms.c
;; The example shows how to iterate over symbolic atoms.
;;
;; ## Output ##
;;
;; ~~~~~~~~~~~~
;; ./symbolic-atoms 0
;; Symbolic atoms:
;;   b
;;   c, external
;;   a, fact
;; ~~~~~~~~~~~~
;;
;; ## Code ##

;; @defgroup SymbolicAtoms Symbolic Atom Inspection
;; Inspection of atoms occurring in ground logic programs.
;;
;; For an example, see @ref symbolic-atoms.c.
;; @ingroup Control

;; @addtogroup SymbolicAtoms
;; @{

;; Object to inspect symbolic atoms in a program---the relevant Herbrand base
;; gringo uses to instantiate programs.
;;
;; @see clingo_control_symbolic_atoms()
(define _clingo-symbolic-atoms-pointer (_cpointer 'clingo-symbolic-atoms))
;; Object to iterate over symbolic atoms.
;;
;; Such an iterator either points to a symbolic atom within a sequence of
;; symbolic atoms or to the end of the sequence.
;;
;; @note Iterators are valid as long as the underlying sequence is not modified.
;; Operations that can change this sequence are ::clingo_control_ground(),
;; ::clingo_control_cleanup(), and functions that modify the underlying
;; non-ground program.
(define _clingo-symbolic-atom-iterator _uint64)

;; Get the number of different atoms occurring in a logic program.
;;
;; @param[in] atoms the target
;; @param[out] size the number of atoms
;; @return whether the call was successful
(define-clingo clingo-symbolic-atoms-size
  (_fun _clingo-symbolic-atoms-pointer (size : (_ptr i _size)) -> (res : _stdbool) ->
        (if res size (raise-clingo-error))))

;; Get a forward iterator to the beginning of the sequence of all symbolic
;; atoms optionally restricted to a given signature.
;;
;; @param[in] atoms the target
;; @param[in] signature optional signature
;; @param[out] iterator the resulting iterator
;; @return whether the call was successful
(define-clingo clingo-symbolic-atoms-begin
  (_fun _clingo-symbolic-atoms-pointer (_ptr i _clingo-signature)
        [iterator : (_ptr o _clingo-symbolic-atom-iterator)] -> (res : _stdbool) ->
        (if res iterator (raise-clingo-error))))

;; Iterator pointing to the end of the sequence of symbolic atoms.
;;
;; @param[in] atoms the target
;; @param[out] iterator the resulting iterator
;; @return whether the call was successful
(define-clingo clingo-symbolic-atoms-end
  (_fun
   _clingo-symbolic-atoms-pointer
   [iterator : (_ptr o _clingo-symbolic-atom-iterator)] -> (res : _stdbool) ->
   (if res iterator (raise-clingo-error))))


;; Find a symbolic atom given its symbolic representation.
;;
;; @param[in] atoms the target
;; @param[in] symbol the symbol to lookup
;; @param[out] iterator iterator pointing to the symbolic atom or to the end
;; of the sequence if no corresponding atom is found
;; @return whether the call was successful
(define-clingo clingo-symbolic-atoms-find
  (_fun _clingo-symbolic-atoms-pointer _clingo-symbol
        [iterator : (_ptr o _clingo-symbolic-atom-iterator)] -> (res : _stdbool) ->
        (if res iterator (raise-clingo-error))))

;; Check if two iterators point to the same element (or end of the sequence).
;;
;; @param[in] atoms the target
;; @param[in] a the first iterator
;; @param[in] b the second iterator
;; @param[out] equal whether the two iterators are equal
;; @return whether the call was successful
(define-clingo clingo-symbolic-atoms-iterator-is-equal-to
  (_fun _clingo-symbolic-atoms-pointer _clingo-symbolic-atom-iterator
        _clingo-symbolic-atom-iterator [equal : (_ptr o _stdbool)] -> (res : _stdbool) ->
        (if res equal (raise-clingo-error))))

;; Get the symbolic representation of an atom.
;;
;; @param[in] atoms the target
;; @param[in] iterator iterator to the atom
;; @param[out] symbol the resulting symbol
;; @return whether the call was successful
(define-clingo clingo-symbolic-atoms-symbol
  (_fun
   _clingo-symbolic-atoms-pointer
   _clingo-symbolic-atom-iterator
   [symbol : (_ptr o _clingo-symbol)] -> (res : _stdbool) ->
   (if res symbol (raise-clingo-error))))

;; Check whether an atom is a fact.
;;
;; @note This does not determine if an atom is a cautious consequence. The
;; grounding or solving component's simplifications can only detect this in
;; some cases.
;;
;; @param[in] atoms the target
;; @param[in] iterator iterator to the atom
;; @param[out] fact whether the atom is a fact
;; @return whether the call was successful
(define-clingo clingo-symbolic-atoms-is-fact
  (_fun
   _clingo-symbolic-atoms-pointer _clingo-symbolic-atom-iterator
   (fact : (_ptr o _stdbool)) -> (res : _stdbool) ->
   (if res fact (raise-clingo-error))))

;; Check whether an atom is external.
;;
;; An atom is external if it has been defined using an external directive and
;; has not been released or defined by a rule.
;;
;; @param[in] atoms the target
;; @param[in] iterator iterator to the atom
;; @param[out] external whether the atom is a external
;; @return whether the call was successful
(define-clingo clingo-symbolic-atoms-is-external
  (_fun
   _clingo-symbolic-atoms-pointer _clingo-symbolic-atom-iterator
   [external : (_ptr o _stdbool)] -> (res : _stdbool) ->
   (if res external (raise-clingo-error)) ))

;; Returns the (numeric) aspif literal corresponding to the given symbolic atom.
;;
;; Such a literal can be mapped to a solver literal (see the \ref Propagator
;; module) or be used in rules in aspif format (see the \ref ProgramBuilder
;; module).
;;
;; @param[in] atoms the target
;; @param[in] iterator iterator to the atom
;; @param[out] literal the associated literal
;; @return whether the call was successful
(define-clingo clingo-symbolic-atoms-literal
  (_fun
   _clingo-symbolic-atoms-pointer _clingo-symbolic-atom-iterator
   [literal : (_ptr o _clingo-literal)] -> (res : _stdbool) ->
   (if res literal (raise-clingo-error))))

;; Get the number of different predicate signatures used in the program.
;;
;; @param[in] atoms the target
;; @param[out] size the number of signatures
;; @return whether the call was successful
(define-clingo clingo-symbolic-atoms-signatures-size
  (_fun
   _clingo-symbolic-atoms-pointer [size : (_ptr o _size)] -> (res : _stdbool) ->
   (if res size (raise-clingo-error))))

;; Get the predicate signatures occurring in a logic program.
;;
;; @param[in] atoms the target
;; @param[out] signatures the resulting signatures
;; @param[in] size the number of signatures
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime if the size is too small
;;
;; @see clingo_symbolic_atoms_signatures_size()
(define-clingo clingo-symbolic-atoms-signatures-unsafe
  (_fun _clingo-symbolic-atoms-pointer _pointer _size -> (res : _stdbool) ->
        (if res (void) (raise-clingo-error)))
  #:c-id clingo_symbolic_atoms_signatures)

(define (clingo-symbolic-atoms-signatures atoms)
  (define size (clingo-symbolic-atoms-size atoms))
  (define buf (make-cvector _clingo-signature size))
  (clingo-symbolic-atoms-signatures-unsafe atoms (cvector-ptr buf) size)
  (cvector->list buf))

;; Get an iterator to the next element in the sequence of symbolic atoms.
;;
;; @param[in] atoms the target
;; @param[in] iterator the current iterator
;; @param[out] next the succeeding iterator
;; @return whether the call was successful
(define-clingo clingo-symbolic-atoms-next
  (_fun
   _clingo-symbolic-atoms-pointer _clingo-symbolic-atom-iterator
   [next : (_ptr o _clingo-symbolic-atom-iterator)] -> (res : _stdbool) ->
   (if res next (raise-clingo-error))))

;; Check whether the given iterator points to some element with the sequence
;; of symbolic atoms or to the end of the sequence.
;;
;; @param[in] atoms the target
;; @param[in] iterator the iterator
;; @param[out] valid whether the iterator points to some element within the
;; sequence
;; @return whether the call was successful
(define-clingo clingo-symbolic-atoms-is-valid
  (_fun
   _clingo-symbolic-atoms-pointer _clingo-symbolic-atom-iterator
   [valid : (_ptr o _stdbool)] -> (res : _stdbool) ->
   (if res valid (raise-clingo-error))))

;; Callback function to inject symbols.
;;
;; @param symbols array of symbols
;; @param symbols_size size of the symbol array
;; @param data user data of the callback
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; @see ::clingo_ground_callback_t
(define _clingo-symbol-callback
  (_fun (_cvector o _clingo-symbol size) [size : _size] _pointer -> _stdbool))

;; @}

;; {{{1 theory atoms

;; @example theory-atoms.c
;; The example shows how to inspect and use theory atoms.
;;
;; @verbatim@endverbatim
;;
;; This is a very simple example that uses the @link ProgramBuilder backend@endlink to let theory atoms affect answer sets.
;; In general, the backend can be used to implement a custom theory by translating it to a logic program.
;; On the other hand, a @link Propagator propagator@endlink can be used to implement a custom theory without adding any constraints in advance.
;; Or both approaches can be combined.
;;
;; ## Output ##
;;
;; ~~~~~~~~~~~~
;; ./theory-atoms 0
;; number of grounded theory atoms: 2
;; theory atom b/1 has a guard: true
;; Model: y
;; Model: x y
;; ~~~~~~~~~~~~
;;
;; ## Code ##

;; @defgroup TheoryAtoms Theory Atom Inspection
;; Inspection of theory atoms occurring in ground logic programs.
;; @ingroup Control
;;
;; During grounding, theory atoms get consecutive numbers starting with zero.
;; The total number of theory atoms can be obtained using clingo_theory_atoms_size().
;;
;; @attention
;; All structural information about theory atoms, elements, and terms is reset after @link clingo_control_solve() solving@endlink.
;; If afterward fresh theory atoms are @link clingo_control_ground() grounded@endlink, previously used ids are reused.
;;
;; For an example, see @ref theory-atoms.c.

;; @addtogroup TheoryAtoms
;; @{

;; Enumeration of theory term types.

(define _clingo-theory-term-type
  (_enum '(
    clingo-theory-term-type-tuple    = 0  ;; a tuple term, e.g., `(1,2,3)`
    clingo-theory-term-type-list     = 1  ;; a list term, e.g., `[1,2,3]`
    clingo-theory-term-type-set      = 2  ;; a set term, e.g., `{1,2,3}`
    clingo-theory-term-type-function = 3  ;; a function term, e.g., `f(1,2,3)`
    clingo-theory-term-type-number   = 4  ;; a number term, e.g., `42`
    clingo-theory-term-type-symbol   = 5  ;; a symbol term, e.g., `c`
  )))


;; Container that stores theory atoms, elements, and terms (see @ref clingo_control_theory_atoms()).
(define _clingo-theory-atoms-pointer (_cpointer 'clingo-theory-atoms))



;; @name Theory Term Inspection
;; @{

;; Get the type of the given theory term.
;;
;; @param[in] atoms container where the term is stored
;; @param[in] term id of the term
;; @param[out] type the resulting type
;; @return whether the call was successful
(define-clingo clingo-theory-atoms-term-type
  (_fun _clingo-theory-atoms-pointer _clingo-id
        (type : (_ptr o _clingo-theory-term-type)) -> (res : _stdbool) ->
        (if res type (raise-clingo-error))))
;; Get the number of the given numeric theory term.
;;
;; @pre The term must be of type ::clingo_theory_term_type_number.
;; @param[in] atoms container where the term is stored
;; @param[in] term id of the term
;; @param[out] number the resulting number
;; @return whether the call was successful
(define-clingo clingo-theory-atoms-term-number
  (_fun _clingo-theory-atoms-pointer _clingo-id [number : (_ptr o _int)] -> (res : _stdbool)
    -> (if res number (raise-clingo-error)) ))
;; Get the name of the given constant or function theory term.
;;
;; @note
;; The lifetime of the string is tied to the current solve step.
;;
;; @pre The term must be of type ::clingo_theory_term_type_function or ::clingo_theory_term_type_symbol.
;; @param[in] atoms container where the term is stored
;; @param[in] term id of the term
;; @param[out] name the resulting name
;; @return whether the call was successful
(define-clingo clingo-theory-atoms-term-name
  (_fun _clingo-theory-atoms-pointer _clingo-id [name : (_ptr o _string)] -> (res : _stdbool)
    -> (if res name (raise-clingo-error)) ))
;; Get the arguments of the given function theory term.
;;
;; @pre The term must be of type ::clingo_theory_term_type_function.
;; @param[in] atoms container where the term is stored
;; @param[in] term id of the term
;; @param[out] arguments the resulting arguments in form of an array of term ids
;; @param[out] size the number of arguments
;; @return whether the call was successful
(define-clingo clingo-theory-atoms-term-arguments-unsafe
  (_fun _clingo-theory-atoms-pointer _clingo-id
        [arguments : (_ptr o _pointer)] [size : (_ptr o _size)] -> (res : _stdbool)
        -> (if res (values arguments size) (raise-clingo-error)))
  #:c-id clingo_theory_atoms_term_arguments)
;; clingo_id_t const **arguments
(define (clingo-theory-atoms-term-arguments atoms term-id)
  (define-values (arguments size) (clingo-theory-atoms-term-arguments-unsafe atoms term-id))
  (cast arguments _pointer (_list o _clingo-id size)))

;; Get the size of the string representation of the given theory term (including the terminating 0).
;;
;; @param[in] atoms container where the term is stored
;; @param[in] term id of the term
;; @param[out] size the resulting size
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-theory-atoms-term-to-string-size
  (_fun _clingo-theory-atoms-pointer _clingo-id [size : (_ptr o _size)] -> (res : _stdbool)
    -> (if res size (raise-clingo-error))))
;; Get the string representation of the given theory term.
;;
;; @param[in] atoms container where the term is stored
;; @param[in] term id of the term
;; @param[out] string the resulting string
;; @param[in] size the size of the string
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_runtime if the size is too small
;; - ::clingo_error_bad_alloc
;;
;; @see clingo_theory_atoms_term_to_string_size()
(define-clingo clingo-theory-atoms-term-to-string-unsafe
  (_fun _clingo-theory-atoms-pointer _clingo-id _bytes _size -> (res : _stdbool)
    -> (if res (void) (raise-clingo-error)))
  #:c-id clingo_theory_atoms_term_to_string)
(define (clingo-theory-atoms-term-to-string atoms term-id)
  (define size (clingo-theory-atoms-term-to-string-size atoms term-id))
  (define buf (make-bytes size))
  (clingo-theory-atoms-term-to-string-unsafe atoms term-id buf size)
  (bytes->string/utf-8 buf #f 0 (- size 1)))
;; @}

;; @name Theory Element Inspection
;; @{

;; Get the tuple (array of theory terms) of the given theory element.
;;
;; @param[in] atoms container where the element is stored
;; @param[in] element id of the element
;; @param[out] tuple the resulting array of term ids
;; @param[out] size the number of term ids
;; @return whether the call was successful
(define-clingo clingo-theory-atoms-element-tuple-unsafe
  (_fun _clingo-theory-atoms-pointer _clingo-id
        [tuple : (_ptr o _pointer)] [size : (_ptr o _size)] -> (res : _stdbool)
    -> (if res (values tuple size) (raise-clingo-error)) )
  #:c-id clingo_theory_atoms_element_tuple)
(define (clingo-theory-atoms-element-tuple atoms term-id)
  (define-values (tuple size) (clingo-theory-atoms-element-tuple-unsafe atoms term-id))
  (cast tuple _pointer (_list o _clingo-id size)))
;; clingo_id_t const **tuple
;; Get the condition (array of aspif literals) of the given theory element.
;;
;; @param[in] atoms container where the element is stored
;; @param[in] element id of the element
;; @param[out] condition the resulting array of aspif literals
;; @param[out] size the number of term literals
;; @return whether the call was successful
(define-clingo clingo-theory-atoms-element-condition-unsafe
  (_fun _clingo-theory-atoms-pointer _clingo-id
        [condition : (_ptr o _pointer)] [size : (_ptr o _size)] -> (res : _stdbool)
    -> (if res (values condition size) (raise-clingo-error)) )
  #:c-id clingo_theory_atoms_element_condition)
(define (clingo-theory-atoms-element-condition atoms term-id)
  (define-values (condition size) (clingo-theory-atoms-element-condition-unsafe atoms term-id))
  (cast condition _pointer (_list o _clingo-literal size)))
;; clingo_literal_t const **condition

;; Get the id of the condition of the given theory element.
;;
;; @note
;; This id can be mapped to a solver literal using clingo_propagate_init_solver_literal().
;; This id is not (necessarily) an aspif literal;
;; to get aspif literals use clingo_theory_atoms_element_condition().
;;
;; @param[in] atoms container where the element is stored
;; @param[in] element id of the element
;; @param[out] condition the resulting condition id
;; @return whether the call was successful
(define-clingo clingo-theory-atoms-element-condition-id
  (_fun _clingo-theory-atoms-pointer _clingo-id
        [condition : (_ptr o _clingo-literal)] -> (res : _stdbool)
        -> (if res condition (raise-clingo-error))))
;; Get the size of the string representation of the given theory element (including the terminating 0).
;;
;; @param[in] atoms container where the element is stored
;; @param[in] element id of the element
;; @param[out] size the resulting size
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-theory-atoms-element-to-string-size
  (_fun _clingo-theory-atoms-pointer _clingo-id
        [size : (_ptr o _size)] -> (res : _stdbool)
        -> (if res size (raise-clingo-error))))
;; Get the string representation of the given theory element.
;;
;; @param[in] atoms container where the element is stored
;; @param[in] element id of the element
;; @param[out] string the resulting string
;; @param[in] size the size of the string
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_runtime if the size is too small
;; - ::clingo_error_bad_alloc
(define-clingo clingo-theory-atoms-element-to-string-unsafe
  (_fun _clingo-theory-atoms-pointer _clingo-id _bytes _size -> (res : _stdbool)
    -> (if res (void) (raise-clingo-error)) )
  #:c-id clingo_theory_atoms_element_to_string)
(define (clingo-theory-atoms-element-to-string atoms term-id)
  (define size (clingo-theory-atoms-element-to-string-size atoms term-id))
  (define buf (make-bytes size))
  (clingo-theory-atoms-element-to-string-unsafe atoms term-id buf size)
  (bytes->string/utf-8 buf #f 0 (- size 1)))
;; @}

;; @name Theory Atom Inspection
;; @{

;; Get the total number of theory atoms.
;;
;; @param[in] atoms the target
;; @param[out] size the resulting number
;; @return whether the call was successful
(define-clingo clingo-theory-atoms-size
  (_fun _clingo-theory-atoms-pointer [size : (_ptr o _size)] -> (res : _stdbool)
    -> (if res size (raise-clingo-error)) ))
;; Get the theory term associated with the theory atom.
;;
;; @param[in] atoms container where the atom is stored
;; @param[in] atom id of the atom
;; @param[out] term the resulting term id
;; @return whether the call was successful
(define-clingo clingo-theory-atoms-atom-term
  (_fun _clingo-theory-atoms-pointer _clingo-id [term : (_ptr o _clingo-id)] -> (res : _stdbool)
    -> (if res term (raise-clingo-error))))
;; Get the theory elements associated with the theory atom.
;;
;; @param[in] atoms container where the atom is stored
;; @param[in] atom id of the atom
;; @param[out] elements the resulting array of elements
;; @param[out] size the number of elements
;; @return whether the call was successful
(define-clingo clingo-theory-atoms-atom-elements-unsafe
  (_fun _clingo-theory-atoms-pointer _clingo-id
        [elements : (_ptr o _pointer)] [size : (_ptr o _size)] -> (res : _stdbool)
    -> (if res (values elements size) (raise-clingo-error)) )
  #:c-id clingo_theory_atoms_atom_elements)
(define (clingo-theory-atoms-atom-elements atoms atom-id)
  (define-values (elements size) (clingo-theory-atoms-atom-elements-unsafe atoms atom-id))
  (cast elements _pointer (_list o _clingo-id size)))
;; clingo_id_t const **elements
;; Whether the theory atom has a guard.
;;
;; @param[in] atoms container where the atom is stored
;; @param[in] atom id of the atom
;; @param[out] has_guard whether the theory atom has a guard
;; @return whether the call was successful
(define-clingo clingo-theory-atoms-atom-has-guard
  (_fun _clingo-theory-atoms-pointer _clingo-id [has-guard : (_ptr o _stdbool)] -> (res : _stdbool)
    -> (if res has-guard (raise-clingo-error))))
;; Get the guard consisting of a theory operator and a theory term of the given theory atom.
;;
;; @note
;; The lifetime of the string is tied to the current solve step.
;;
;; @param[in] atoms container where the atom is stored
;; @param[in] atom id of the atom
;; @param[out] connective the resulting theory operator
;; @param[out] term the resulting term
;; @return whether the call was successful
(define-clingo clingo-theory-atoms-atom-guard
  (_fun _clingo-theory-atoms-pointer _clingo-id
        [connective : (_ptr o _string)]
        [term : (_ptr o _clingo-id)] -> (res : _stdbool)
    -> (if res (values connective term) (raise-clingo-error)) ))
;; Get the aspif literal associated with the given theory atom.
;;
;; @param[in] atoms container where the atom is stored
;; @param[in] atom id of the atom
;; @param[out] literal the resulting literal
;; @return whether the call was successful
(define-clingo clingo-theory-atoms-atom-literal
  (_fun
   _clingo-theory-atoms-pointer _clingo-id [literal : (_ptr o _clingo-literal)] -> (res : _stdbool)
    -> (if res literal (raise-clingo-error)) ))
;; Get the size of the string representation of the given theory atom (including the terminating 0).
;;
;; @param[in] atoms container where the atom is stored
;; @param[in] atom id of the element
;; @param[out] size the resulting size
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-theory-atoms-atom-to-string-size
  (_fun _clingo-theory-atoms-pointer _clingo-id [size : (_ptr o _size)] -> (res : _stdbool)
    -> (if res size (raise-clingo-error)) ))
;; Get the string representation of the given theory atom.
;;
;; @param[in] atoms container where the atom is stored
;; @param[in] atom id of the element
;; @param[out] string the resulting string
;; @param[in] size the size of the string
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_runtime if the size is too small
;; - ::clingo_error_bad_alloc
(define-clingo clingo-theory-atoms-atom-to-string-unsafe
  (_fun _clingo-theory-atoms-pointer _clingo-id _bytes _size -> (res : _stdbool)
    -> (if res (void) (raise-clingo-error)))
  #:c-id clingo_theory_atoms_atom_to_string)
(define (clingo-theory-atoms-atom-to-string atoms atom-id)
  (define size (clingo-theory-atoms-atom-to-string-size atoms atom-id))
  (define buf (make-bytes size))
  (clingo-theory-atoms-atom-to-string-unsafe atoms atom-id buf size)
  (bytes->string/utf-8 buf #f 0 (- size 1)))
;; @}

;; {{{1 propagator

;; @example propagator.c
;; The example shows how to write a simple propagator for the pigeon hole problem. For
;; a detailed description of what is implemented here and some background, take a look at the following paper:
;;
;; https://www.cs.uni-potsdam.de/wv/publications/#DBLP:conf/iclp/GebserKKOSW16x
;;
;; ## Output ##
;;
;; The output is empty because the pigeon hole problem is unsatisfiable.
;;
;; ## Code ##

;; @defgroup Propagator Theory Propagation
;; Extend the search with propagators for arbitrary theories.
;;
;; For an example, see @ref propagator.c.
;; @ingroup Control

;; @addtogroup Propagator
;; @{

;; Represents a (partial) assignment of a particular solver.
;;
;; An assignment assigns truth values to a set of literals.
;; A literal is assigned to either @link clingo_assignment_truth_value() true or false, or is unassigned@endlink.
;; Furthermore, each assigned literal is associated with a @link clingo_assignment_level() decision level@endlink.
;; There is exactly one @link clingo_assignment_decision() decision literal@endlink for each decision level greater than zero.
;; Assignments to all other literals on the same level are consequences implied by the current and possibly previous decisions.
;; Assignments on level zero are immediate consequences of the current program.
;; Decision levels are consecutive numbers starting with zero up to and including the @link clingo_assignment_decision_level() current decision level@endlink.
(define _clingo-assignment-pointer (_cpointer 'clingo-assignment))

;; @name Assignment Functions
;; @{

;; Get the current decision level.
;;
;; @param[in] assignment the target assignment
;; @return the decision level
(define-clingo clingo-assignment-decision-level
  (_fun _clingo-assignment-pointer -> _uint32))
;; Get the current root level.
;;
;; Decisions levels smaller or equal to the root level are not backtracked during solving.
;;
;; @param[in] assignment the target assignment
;; @return the decision level
(define-clingo clingo-assignment-root-level
  (_fun _clingo-assignment-pointer -> _uint32))
;; Check if the given assignment is conflicting.
;;
;; @param[in] assignment the target assignment
;; @return whether the assignment is conflicting
(define-clingo clingo-assignment-has-conflict
  (_fun _clingo-assignment-pointer -> _stdbool))
;; Check if the given literal is part of a (partial) assignment.
;;
;; @param[in] assignment the target assignment
;; @param[in] literal the literal
;; @return whether the literal is valid
(define-clingo clingo-assignment-has-literal
  (_fun _clingo-assignment-pointer _clingo-literal -> _stdbool))
;; Determine the decision level of a given literal.
;;
;; @param[in] assignment the target assignment
;; @param[in] literal the literal
;; @param[out] level the resulting level
;; @return whether the call was successful
(define-clingo clingo-assignment-level
  (_fun _clingo-assignment-pointer _clingo-literal [level : (_ptr o _uint32)] -> (res : _stdbool)
    -> (if res level (raise-clingo-error)) ))
;; Determine the decision literal given a decision level.
;;
;; @param[in] assignment the target assignment
;; @param[in] level the level
;; @param[out] literal the resulting literal
;; @return whether the call was successful
(define-clingo clingo-assignment-decision
  (_fun _clingo-assignment-pointer _uint32 [literal : (_ptr o _clingo-literal)] -> (res : _stdbool)
    -> (if res literal (raise-clingo-error))))
;; Check if a literal has a fixed truth value.
;;
;; @param[in] assignment the target assignment
;; @param[in] literal the literal
;; @param[out] is_fixed whether the literal is fixed
;; @return whether the call was successful
(define-clingo clingo-assignment-is-fixed
  (_fun _clingo-assignment-pointer _clingo-literal [is-fixed : (_ptr o _stdbool)] -> (res : _stdbool)
    -> (if res is-fixed (raise-clingo-error)) ))
;; Check if a literal is true.
;;
;; @param[in] assignment the target assignment
;; @param[in] literal the literal
;; @param[out] is_true whether the literal is true
;; @return whether the call was successful
;; @see clingo_assignment_truth_value()
(define-clingo clingo-assignment-is-true
  (_fun _clingo-assignment-pointer _clingo-literal [is-true : (_ptr o _stdbool)] -> (res : _stdbool)
    -> (if res is-true (raise-clingo-error)) ))
;; Check if a literal has a fixed truth value.
;;
;; @param[in] assignment the target assignment
;; @param[in] literal the literal
;; @param[out] is_false whether the literal is false
;; @return whether the call was successful
;; @see clingo_assignment_truth_value()
(define-clingo clingo-assignment-is-false
  (_fun _clingo-assignment-pointer _clingo-literal [is-false : (_ptr o _stdbool)] -> (res : _stdbool)
    -> (if res is-false (raise-clingo-error)) ))
;; Determine the truth value of a given literal.
;;
;; @param[in] assignment the target assignment
;; @param[in] literal the literal
;; @param[out] value the resulting truth value
;; @return whether the call was successful
(define-clingo clingo-assignment-truth-value
  (_fun _clingo-assignment-pointer _clingo-literal [value : (_ptr o _clingo-truth-value)] -> (res : _stdbool)
    -> (if res value (raise-clingo-error)) ))
;; The number of (positive) literals in the assignment.
;;
;; @param[in] assignment the target
;; @return the number of literals
(define-clingo clingo-assignment-size (_fun _clingo-assignment-pointer -> _size))
;; Check if the assignment is total, i.e. there are no free literal.
;;
;; @param[in] assignment the target
;; @return wheather the assignment is total
(define-clingo clingo-assignment-is-total
  (_fun _clingo-assignment-pointer -> _stdbool))

;; @}


;; Supported check modes for propagators.
;;
;; Note that total checks are subject to the lock when a model is found.
;; This means that information from previously found models can be used to discard assignments in check calls.

(define _clingo-propagator-check-mode
  (_enum '(
    clingo-propagator-check-mode-none     = 0 ;; do not call @ref ::clingo_propagator::check() at all
    clingo-propagator-check-mode-total    = 1 ;; call @ref ::clingo_propagator::check() on total assignments
    clingo-propagator-check-mode-fixpoint = 2 ;; call @ref ::clingo_propagator::check() on propagation fixpoints
    clingo-propagator-check-mode-both     = 3 ;; call @ref ::clingo_propagator::check() on propagation fixpoints and total assignments
  )))

;; Enumeration of weight_constraint_types.
(define _clingo-weight-constraint-type
  (_enum '(
    clingo-weight-constraint-type-implication-left  = -1 ;; the weight constraint implies the literal
    clingo-weight-constraint-type-implication-right =  1 ;; the literal implies the weight constraint
    clingo-weight-constraint-type-equivalence       =  0 ;; the weight constraint is equivalent to the literal
  )))


;; Object to initialize a user-defined propagator before each solving step.
;;
;; Each @link SymbolicAtoms symbolic@endlink or @link TheoryAtoms theory atom@endlink is uniquely associated with an aspif atom in form of a positive integer (@ref ::clingo_literal_t).
;; Aspif literals additionally are signed to represent default negation.
;; Furthermore, there are non-zero integer solver literals (also represented using @ref ::clingo_literal_t).
;; There is a surjective mapping from program atoms to solver literals.
;;
;; All methods called during propagation use solver literals whereas clingo_symbolic_atoms_literal() and clingo_theory_atoms_atom_literal() return program literals.
;; The function clingo_propagate_init_solver_literal() can be used to map program literals or @link clingo_theory_atoms_element_condition_id() condition ids@endlink to solver literals.
(define _clingo-propagate-init-pointer (_cpointer 'clingo-propagate-init))


;; @name Initialization Functions
;; @{

;; Map the given program literal or condition id to its solver literal.
;;
;; @param[in] init the target
;; @param[in] aspif_literal the aspif literal to map
;; @param[out] solver_literal the resulting solver literal
;; @return whether the call was successful
(define-clingo clingo-propagate-init-solver-literal
  (_fun _clingo-propagate-init-pointer _clingo-literal
        [solver-literal : (_ptr o _clingo-literal)] -> (res : _stdbool) ->
        (if res solver-literal (raise-clingo-error))))
;; Add a watch for the solver literal in the given phase.
;;
;; @param[in] init the target
;; @param[in] solver_literal the solver literal
;; @return whether the call was successful
(define-clingo clingo-propagate-init-add-watch
  (_fun _clingo-propagate-init-pointer _clingo-literal -> (res : _stdbool) ->
        (if res (void) (raise-clingo-error))))
;; Add a watch for the solver literal in the given phase to the given solver thread.
;;
;; @param[in] init the target
;; @param[in] solver_literal the solver literal
;; @param[in] thread_id the id of the solver thread
;; @return whether the call was successful
(define-clingo clingo-propagate-init-add-watch-to-thread
  (_fun _clingo-propagate-init-pointer _clingo-literal _clingo-id -> (res : _stdbool) ->
        (if res (void) (raise-clingo-error)) ))


;; Get an object to inspect the symbolic atoms.
;;
;; @param[in] init the target
;; @param[out] atoms the resulting object
;; @return whether the call was successful
(define-clingo clingo-propagate-init-symbolic-atoms
  (_fun _clingo-propagate-init-pointer [atoms : (_ptr o _clingo-symbolic-atoms-pointer)] -> (res : _stdbool) ->
        (if res atoms (raise-clingo-error)) ))
;; Get an object to inspect the theory atoms.
;;
;; @param[in] init the target
;; @param[out] atoms the resulting object
;; @return whether the call was successful
(define-clingo clingo-propagate-init-theory-atoms
  (_fun _clingo-propagate-init-pointer [atoms : (_ptr o _clingo-theory-atoms-pointer)] -> (res : _stdbool) ->
        (if res atoms (raise-clingo-error))))
;; Get the number of threads used in subsequent solving.
;;
;; @param[in] init the target
;; @return the number of threads
;; @see clingo_propagate_control_thread_id()
(define-clingo clingo-propagate-init-number-of-threads
  (_fun _clingo-propagate-init-pointer -> _int))
;; Configure when to call the check method of the propagator.
;;
;; @param[in] init the target
;; @param[in] mode bitmask when to call the propagator
;; @see @ref ::clingo_propagator::check()
(define-clingo clingo-propagate-init-set-check-mode
  (_fun _clingo-propagate-init-pointer _clingo-propagator-check-mode -> _void))
;; Get the current check mode of the propagator.
;;
;; @param[in] init the target
;; @return bitmask when to call the propagator
;; @see clingo_propagate_init_set_check_mode()
(define-clingo clingo-propagate-init-get-check-mode
  (_fun _clingo-propagate-init-pointer -> _clingo-propagator-check-mode))
;; Get the top level assignment solver.
;;
;; @param[in] init the target
;; @return the assignment
(define-clingo clingo-propagate-init-assignment
  (_fun _clingo-propagate-init-pointer -> _clingo-assignment-pointer))
;; Add the given clause to the solver.
;;
;; @attention No further calls on the init object or functions on the assignment should be called when the result of this method is false.
;;
;; @param[in] init the target
;; @param[in] clause the clause to add
;; @param[in] size the size of the clause
;; @param[out] result result indicating whether the problem became unsatisfiable
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-propagate-init-add-clause
  (_fun _clingo-propagate-init-pointer [ls : (_list i _clingo-literal)] [_size = (length ls)]
        [result : (_ptr o _stdbool)] -> (res : _stdbool) ->
        (if res result (raise-clingo-error)) ))

;; @}

;; Enumeration of clause types determining the lifetime of a clause.
;;
;; Clauses in the solver are either cleaned up based on a configurable deletion policy or at the end of a solving step.
;; The values of this enumeration determine if a clause is subject to one of the above deletion strategies.
(define _clingo-clause-type
  (_enum '(
    clingo-clause-type-learnt          = 0 ;; clause is subject to the solvers deletion policy
    clingo-clause-type-static          = 1 ;; clause is not subject to the solvers deletion policy
    clingo-clause-type-volatile        = 2 ;; like ::clingo_clause_type_learnt but the clause is deleted after a solving step
    clingo-clause-type-volatile-static = 3  ;; like ::clingo_clause_type_static but the clause is deleted after a solving step
  )))

;; This object can be used to add clauses and propagate literals while solving.
(define _clingo-propagate-control-pointer (_cpointer 'clingo-propagate-control))


;; @name Propagation Functions
;; @{

;; Get the id of the underlying solver thread.
;;
;; Thread ids are consecutive numbers starting with zero.
;;
;; @param[in] control the target
;; @return the thread id
(define-clingo clingo-propagate-control-thread-id
  (_fun _clingo-propagate-control-pointer -> _clingo-id))
;; Get the assignment associated with the underlying solver.
;;
;; @param[in] control the target
;; @return the assignment
(define-clingo clingo-propagate-control-assignment
  (_fun _clingo-propagate-control-pointer -> _clingo-assignment-pointer))
;; Adds a new volatile literal to the underlying solver thread.
;;
;; @attention The literal is only valid within the current solving step and solver thread.
;; All volatile literals and clauses involving a volatile literal are deleted after the current search.
;;
;; @param[in] control the target
;; @param[out] result the (positive) solver literal
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_logic if the assignment is conflicting
(define-clingo clingo-propagate-control-add-literal
  (_fun _clingo-propagate-control-pointer [result : (_ptr o _clingo-literal)] -> (res : _stdbool) ->
   (if res result (raise-clingo-error)) ))
;; Add a watch for the solver literal in the given phase.
;;
;; @note Unlike @ref clingo_propagate_init_add_watch() this does not add a watch to all solver threads but just the current one.
;;
;; @param[in] control the target
;; @param[in] literal the literal to watch
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_logic if the literal is invalid
;; @see clingo_propagate_control_remove_watch()
(define-clingo clingo-propagate-control-add-watch
  (_fun _clingo-propagate-control-pointer _clingo-literal -> (res : _stdbool) ->
   (if res (void) (raise-clingo-error)) ))
;; Check whether a literal is watched in the current solver thread.
;;
;; @param[in] control the target
;; @param[in] literal the literal to check
;;
;; @return whether the literal is watched
(define-clingo clingo-propagate-control-has-watch
  (_fun _clingo-propagate-control-pointer _clingo-literal -> _stdbool))
;; Removes the watch (if any) for the given solver literal.
;;
;; @note Similar to @ref clingo_propagate_init_add_watch() this just removes the watch in the current solver thread.
;;
;; @param[in] control the target
;; @param[in] literal the literal to remove
(define-clingo clingo-propagate-control-remove-watch
  (_fun _clingo-propagate-control-pointer _clingo-literal -> _void))
;; Add the given clause to the solver.
;;
;; This method sets its result to false if the current propagation must be stopped for the solver to backtrack.
;;
;; @attention No further calls on the control object or functions on the assignment should be called when the result of this method is false.
;;
;; @param[in] control the target
;; @param[in] clause the clause to add
;; @param[in] size the size of the clause
;; @param[in] type the clause type determining its lifetime
;; @param[out] result result indicating whether propagation has to be stopped
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-propagate-control-add-clause
  (_fun _clingo-propagate-control-pointer [ls : (_list i _clingo-literal)] [_size = (length ls)]
        _clingo-clause-type [result : (_ptr o _stdbool)] -> (res : _stdbool) ->
   (if res result (raise-clingo-error)) ))
;; Propagate implied literals (resulting from added clauses).
;;
;; This method sets its result to false if the current propagation must be stopped for the solver to backtrack.
;;
;; @attention No further calls on the control object or functions on the assignment should be called when the result of this method is false.
;;
;; @param[in] control the target
;; @param[out] result result indicating whether propagation has to be stopped
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-propagate-control-propagate
  (_fun _clingo-propagate-control-pointer [result : (_ptr o _stdbool)] -> (res : _stdbool) ->
   (if res result (raise-clingo-error)) ))

;; @}


;; Typedef for @ref ::clingo_propagator::init().
(define _clingo-propagator-init-callback
  (_fun _clingo-propagate-init-pointer _pointer -> _stdbool))

;; Typedef for @ref ::clingo_propagator::propagate().
(define _clingo-propagator-propagate-callback
  (_fun _clingo-propagate-control-pointer
        (_list o _clingo-literal size)
        [size : _size]
        _pointer -> _stdbool))

;; Typedef for @ref ::clingo_propagator::undo().
(define _clingo-propagator-undo-callback
  (_fun _clingo-propagate-control-pointer
        (_list o _clingo-literal size)
        [size : _size] _pointer -> _void))

;; Typedef for @ref ::clingo_propagator::check().
(define _clingo-propagator-check-callback
  (_fun _clingo-propagate-control-pointer _pointer -> _stdbool))



;; An instance of this struct has to be registered with a solver to implement a custom propagator.
;;
;; Not all callbacks have to be implemented and can be set to NULL if not needed.
;; @see Propagator
(define-cstruct _clingo-propagator [
    ;; This function is called once before each solving step.
    ;; It is used to map relevant program literals to solver literals, add watches for solver literals, and initialize the data structures used during propagation.
    ;;
    ;; @note This is the last point to access symbolic and theory atoms.
    ;; Once the search has started, they are no longer accessible.
    ;;
    ;; @param[in] init initizialization object
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; @see ::clingo_propagator_init_callback_t
    [init (_fun _clingo-propagate-init-pointer _pointer -> _stdbool)]
    ;; Can be used to propagate solver literals given a @link clingo_assignment_t partial assignment@endlink.
    ;;
    ;; Called during propagation with a non-empty array of @link clingo_propagate_init_add_watch() watched solver literals@endlink
    ;; that have been assigned to true since the last call to either propagate, undo, (or the start of the search) - the change set.
    ;; Only watched solver literals are contained in the change set.
    ;; Each literal in the change set is true w.r.t. the current @link clingo_assignment_t assignment@endlink.
    ;; @ref clingo_propagate_control_add_clause() can be used to add clauses.
    ;; If a clause is unit resulting, it can be propagated using @ref clingo_propagate_control_propagate().
    ;; If the result of either of the two methods is false, the propagate function must return immediately.
    ;;
    ;; The following snippet shows how to use the methods to add clauses and propagate consequences within the callback.
    ;; The important point is to return true (true to indicate there was no error) if the result of either of the methods is false.
    ;; ~~~~~~~~~~~~~~~{.c}
    ;; bool result;
    ;; clingo_literal_t clause[] = { ... };
    ;;
    ;; // add a clause
    ;; if (!clingo_propagate_control_add_clause(control, clause, clingo_clause_type_learnt, &result) { return false; }
    ;; if (!result) { return true; }
    ;; // propagate its consequences
    ;; if (!clingo_propagate_control_propagate(control, &result) { return false; }
    ;; if (!result) { return true; }
    ;;
    ;; // add further clauses and propagate them
    ;; ...
    ;;
    ;; return true;
    ;; ~~~~~~~~~~~~~~~
    ;;
    ;; @note
    ;; This function can be called from different solving threads.
    ;; Each thread has its own assignment and id, which can be obtained using @ref clingo_propagate_control_thread_id().
    ;;
    ;; @param[in] control control object for the target solver
    ;; @param[in] changes the change set
    ;; @param[in] size the size of the change set
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; @see ::clingo_propagator_propagate_callback_t
    [propagate
     (_fun _clingo-propagate-control-pointer
           (_list o _clingo-literal size)
           [size : _size] _pointer -> _stdbool)]
    ;; Called whenever a solver undoes assignments to watched solver literals.
    ;;
    ;; This callback is meant to update assignment dependent state in the propagator.
    ;;
    ;; @note No clauses must be propagated in this callback and no errors should be set.
    ;;
    ;; @param[in] control control object for the target solver
    ;; @param[in] changes the change set
    ;; @param[in] size the size of the change set
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; @see ::clingo_propagator_undo_callback_t
    [undo
     (_fun _clingo-propagate-control-pointer
           (_list o _clingo-literal size)
           [size : _size] _pointer -> _void)]
    ;; This function is similar to @ref clingo_propagate_control_propagate() but is called without a change set on propagation fixpoints.
    ;;
    ;; When exactly this function is called, can be configured using the @ref clingo_propagate_init_set_check_mode() function.
    ;;
    ;; @note This function is called even if no watches have been added.
    ;;
    ;; @param[in] control control object for the target solver
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; @see ::clingo_propagator_check_callback_t
    [check (_fun _clingo-propagate-control-pointer _pointer -> _stdbool)]
    ;; This function allows a propagator to implement domain-specific heuristics.
    ;;
    ;; It is called whenever propagation reaches a fixed point and
    ;; should return a free solver literal that is to be assigned true.
    ;; In case multiple propagators are registered,
    ;; this function can return 0 to let a propagator registered later make a decision.
    ;; If all propagators return 0, then the fallback literal is
    ;;
    ;; @param[in] thread_id the solver's thread id
    ;; @param[in] assignment the assignment of the solver
    ;; @param[in] fallback the literal choosen by the solver's heuristic
    ;; @param[out] decision the literal to make true
    ;; @return whether the call was successful
    [decide
     (_fun _clingo-id _clingo-assignment-pointer
           _clingo-literal _pointer
           (_ptr i _clingo-literal) -> _stdbool)]
])

;; @}


;; {{{1 backend

;; @example backend.c
;; The example shows how to used the backend to extend a grounded program.
;;
;; ## Output ##
;;
;; ~~~~~~~~~~~~
;; ./backend 0
;; Model: a b
;; Model: a b c
;; Model:
;; Model: a
;; Model: b
;; ~~~~~~~~~~~~
;;
;; ## Code ##

;; @defgroup ProgramBuilder Program Building
;; Add non-ground program representations (ASTs) to logic programs or extend the ground (aspif) program.
;; @ingroup Control
;;
;; For an example about ground logic programs, see @ref backend.c.
;; For an example about non-ground logic programs, see @ref ast.c and the @ref AST module.

;; @addtogroup ProgramBuilder
;; @{

;; Enumeration of theory sequence types.
(define _clingo-theory-sequence-type
  (_enum '(
    clingo-theory-sequence-type-tuple ;; Theory tuples "(t1,...,tn)".
    clingo-theory-sequence-type-list  ;; Theory lists "[t1,...,tn]".
    clingo-theory-sequence-type-set    ;; Theory sets "{t1,...,tn}".
  )))

;; Enumeration of different heuristic modifiers.
;; @ingroup ProgramInspection
(define _clingo-heuristic-type
  (_enum '(
    clingo-heuristic-type-level  = 0 ;; set the level of an atom
    clingo-heuristic-type-sign   = 1 ;; configure which sign to chose for an atom
    clingo-heuristic-type-factor = 2 ;; modify VSIDS factor of an atom
    clingo-heuristic-type-init   = 3 ;; modify the initial VSIDS score of an atom
    clingo-heuristic-type-true   = 4 ;; set the level of an atom and choose a positive sign
    clingo-heuristic-type-false  = 5  ;; set the level of an atom and choose a negative sign
  )))

;; Enumeration of different external statements.
;; @ingroup ProgramInspection
(define _clingo-external-type
  (_enum '(
    clingo-external-type-free    = 0 ;;< allow an external to be assigned freely
    clingo-external-type-true    = 1 ;;< assign an external to true
    clingo-external-type-false   = 2 ;;< assign an external to false
    clingo-external-type-release = 3 ;;< no longer treat an atom as external
  )))

(define _clingo-backend-pointer (_cpointer 'clingo-backend))



;; Prepare the backend for usage.
;;
;; @param[in] backend the target backend
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime
(define-clingo clingo-backend-begin
  (_fun _clingo-backend-pointer -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))
;; Finalize the backend after using it.
;;
;; @param[in] backend the target backend
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime
(define-clingo clingo-backend-end
  (_fun _clingo-backend-pointer -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))
;; Add a rule to the program.
;;
;; @param[in] backend the target backend
;; @param[in] choice determines if the head is a choice or a disjunction
;; @param[in] head the head atoms
;; @param[in] head_size the number of atoms in the head
;; @param[in] body the body literals
;; @param[in] body_size the number of literals in the body
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-backend-rule
  (_fun _clingo-backend-pointer _stdbool
        [als : (_list i _clingo-atom)]
        [_size = (length als)]
        [lls : (_list i _clingo-literal)]
        [_size = (length lls)] -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))
;; Add a weight rule to the program.
;;
;; @attention All weights and the lower bound must be positive.
;; @param[in] backend the target backend
;; @param[in] choice determines if the head is a choice or a disjunction
;; @param[in] head the head atoms
;; @param[in] head_size the number of atoms in the head
;; @param[in] lower_bound the lower bound of the weight rule
;; @param[in] body the weighted body literals
;; @param[in] body_size the number of weighted literals in the body
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-backend-weight-rule
  (_fun _clingo-backend-pointer _stdbool
        [als : (_list i _clingo-atom)] [_size = (length als)]
        _clingo-weight
        [wls : (_list i _clingo-weighted-literal)]
        [_size = (length wls)] -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))
;; Add a minimize constraint (or weak constraint) to the program.
;;
;; @param[in] backend the target backend
;; @param[in] priority the priority of the constraint
;; @param[in] literals the weighted literals whose sum to minimize
;; @param[in] size the number of weighted literals
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-backend-minimize
  (_fun _clingo-backend-pointer _clingo-weight
        [wls : (_list i _clingo-weighted-literal)]
        [_size = (length wls)] -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))
;; Add a projection directive.
;;
;; @param[in] backend the target backend
;; @param[in] atoms the atoms to project on
;; @param[in] size the number of atoms
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-backend-project
  (_fun _clingo-backend-pointer
        [als : (_list i _clingo-atom)]
        [_size = (length als)] -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error))))
;; Add an external statement.
;;
;; @param[in] backend the target backend
;; @param[in] atom the external atom
;; @param[in] type the type of the external statement
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-backend-external
  (_fun _clingo-backend-pointer _clingo-atom
        _clingo-external-type -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))
;; Add an assumption directive.
;;
;; @param[in] backend the target backend
;; @param[in] literals the literals to assume (positive literals are true and negative literals false for the next solve call)
;; @param[in] size the number of atoms
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-backend-assume
  (_fun _clingo-backend-pointer
        [wls : (_list i _clingo-literal)]
        [_size = (length wls)] -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))
;; Add an heuristic directive.
;;
;; @param[in] backend the target backend
;; @param[in] atom the target atom
;; @param[in] type the type of the heuristic modification
;; @param[in] bias the heuristic bias
;; @param[in] priority the heuristic priority
;; @param[in] condition the condition under which to apply the heuristic modification
;; @param[in] size the number of atoms in the condition
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-backend-heuristic
  (_fun
   _clingo-backend-pointer _clingo-atom
   _clingo-heuristic-type _int _uint
   [cls : (_list i _clingo-literal)]
   [_size = (length cls)] -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))
;; Add an edge directive.
;;
;; @param[in] backend the target backend
;; @param[in] node_u the start vertex of the edge
;; @param[in] node_v the end vertex of the edge
;; @param[in] condition the condition under which the edge is part of the graph
;; @param[in] size the number of atoms in the condition
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-backend-acyc-edge
  (_fun
   _clingo-backend-pointer _int _int
   [cls : (_list i _clingo-literal)]
   [_size = (length cls)] -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))
;; Get a fresh atom to be used in aspif directives.
;;
;; @param[in] backend the target backend
;; @param[in] symbol optional symbol to associate the atom with
;; @param[out] atom the resulting atom
;; @return whether the call was successful
(define-clingo clingo-backend-add-atom
  (_fun
   _clingo-backend-pointer
   (_ptr i _clingo-symbol)
   [atom : (_ptr o _clingo-atom)] -> (res : _stdbool) ->
      (if res atom (raise-clingo-error)) ))

;; @}


;; {{{1 configuration

;; @example configuration.c
;; The example shows how to configure the solver.
;;
;; @note It is also possible to loop over all configuration entries.
;; This can be done in a similar fashion as in the @ref statistics.c example.
;; But note that, unlike with statistics entries, a configuration entry can have more than one type.
;;
;; ## Output ##
;;
;; ~~~~~~~~
;; ./configuration
;; Model: a
;; Model: b
;; ~~~~~~~~
;;
;; ## Code ##

;; @defgroup Configuration Solver Configuration
;; Configuration of search and enumeration algorithms.
;;
;; Entries in a configuration are organized hierarchically.
;; Subentries are either accessed by name for map entries or by offset for array entries.
;; Value entries have a string value that can be inspected or modified.
;;
;; For an example, see @ref configuration.c.
;; @ingroup Control

;; @addtogroup Configuration
;; @{

(define _clingo-configuration-type
  (_enum '(
    clingo-configuration-type-value = 1 ;; the entry is a (string) value
    clingo-configuration-type-array = 2 ;; the entry is an array
    clingo-configuration-type-map   = 4  ;; the entry is a map
  )))

;; Bitset for values of type ::clingo_configuration_type_e.
(define _clingo-configuration-type-bitset _uint)

;; Handle for to the solver configuration.
(define _clingo-configuration-pointer (_cpointer 'clingo-configuration))

;; Get the root key of the configuration.
;;
;; @param[in] configuration the target configuration
;; @param[out] key the root key
;; @return whether the call was successful
(define-clingo clingo-configuration-root
  (_fun
   _clingo-configuration-pointer
   [key : (_ptr o _clingo-id)] -> (res : _stdbool) ->
      (if res key (raise-clingo-error))))
;; Get the type of a key.
;;
;; @note The type is bitset, an entry can have multiple (but at least one) type.
;;
;; @param[in] configuration the target configuration
;; @param[in] key the key
;; @param[out] type the resulting type
;; @return whether the call was successful
(define-clingo clingo-configuration-type
  (_fun _clingo-configuration-pointer _clingo-id
        [type : (_ptr o _clingo-configuration-type-bitset)] ->
        (res : _stdbool) ->
      (if res type (raise-clingo-error)) ))
;; Get the description of an entry.
;;
;; @param[in] configuration the target configuration
;; @param[in] key the key
;; @param[out] description the description
;; @return whether the call was successful
(define-clingo clingo-configuration-description
  (_fun
   _clingo-configuration-pointer _clingo-id
   [description : (_ptr o _string)] -> (res : _stdbool) ->
      (if res description (raise-clingo-error)) ))

;; @name Functions to access arrays
;; @{

;; Get the size of an array entry.
;;
;; @pre The @link clingo_configuration_type() type@endlink of the entry must be @ref ::clingo_configuration_type_array.
;; @param[in] configuration the target configuration
;; @param[in] key the key
;; @param[out] size the resulting size
;; @return whether the call was successful
(define-clingo clingo-configuration-array-size
  (_fun _clingo-configuration-pointer _clingo-id
        [size : (_ptr o _size)] -> (res : _stdbool) ->
      (if res size (raise-clingo-error)) ))
;; Get the subkey at the given offset of an array entry.
;;
;; @note Some array entries, like fore example the solver configuration, can be accessed past there actual size to add subentries.
;; @pre The @link clingo_configuration_type() type@endlink of the entry must be @ref ::clingo_configuration_type_array.
;; @param[in] configuration the target configuration
;; @param[in] key the key
;; @param[in] offset the offset in the array
;; @param[out] subkey the resulting subkey
;; @return whether the call was successful
(define-clingo clingo-configuration-array-at
  (_fun
   _clingo-configuration-pointer _clingo-id
   _size [subkey : (_ptr o _clingo-id)] -> (res : _stdbool) ->
      (if res subkey (raise-clingo-error)) ))
;; @}

;; @name Functions to access maps
;; @{

;; Get the number of subkeys of a map entry.
;;
;; @pre The @link clingo_configuration_type() type@endlink of the entry must be @ref ::clingo_configuration_type_map.
;; @param[in] configuration the target configuration
;; @param[in] key the key
;; @param[out] size the resulting number
;; @return whether the call was successful
(define-clingo clingo-configuration-map-size
  (_fun _clingo-configuration-pointer _clingo-id
        [size : (_ptr o _size)] -> (res : _stdbool) ->
      (if res size (raise-clingo-error)) ))
;; Query whether the map has a key.
;;
;; @pre The @link clingo_configuration_type() type@endlink of the entry must be @ref ::clingo_configuration_type_map.
;; @note Multiple levels can be looked up by concatenating keys with a period.
;; @param[in] configuration the target configuration
;; @param[in] key the key
;; @param[in] name the name to lookup the subkey
;; @param[out] result whether the key is in the map
;; @return whether the call was successful
(define-clingo clingo-configuration-map-has-subkey
  (_fun _clingo-configuration-pointer _clingo-id _string
        [result : (_ptr o _stdbool)] -> (res : _stdbool) ->
      (if res result (raise-clingo-error)) ))
;; Get the name associated with the offset-th subkey.
;;
;; @pre The @link clingo_configuration_type() type@endlink of the entry must be @ref ::clingo_configuration_type_map.
;; @param[in] configuration the target configuration
;; @param[in] key the key
;; @param[in] offset the offset of the name
;; @param[out] name the resulting name
;; @return whether the call was successful
(define-clingo clingo-configuration-map-subkey-name
  (_fun _clingo-configuration-pointer _clingo-id _size
        [name : (_ptr o _string)] -> (res : _stdbool) ->
      (if res name (raise-clingo-error)) ))
;; Lookup a subkey under the given name.
;;
;; @pre The @link clingo_configuration_type() type@endlink of the entry must be @ref ::clingo_configuration_type_map.
;; @note Multiple levels can be looked up by concatenating keys with a period.
;; @param[in] configuration the target configuration
;; @param[in] key the key
;; @param[in] name the name to lookup the subkey
;; @param[out] subkey the resulting subkey
;; @return whether the call was successful
(define-clingo clingo-configuration-map-at
  (_fun _clingo-configuration-pointer _clingo-id _string
        [subkey : (_ptr o _clingo-id)] -> (res : _stdbool) ->
      (if res subkey (raise-clingo-error)) ))
;; @}

;; @name Functions to access values
;; @{

;; Check whether a entry has a value.
;;
;; @pre The @link clingo_configuration_type() type@endlink of the entry must be @ref ::clingo_configuration_type_value.
;; @param[in] configuration the target configuration
;; @param[in] key the key
;; @param[out] assigned whether the entry has a value
;; @return whether the call was successful
(define-clingo clingo-configuration-value-is-assigned
  (_fun _clingo-configuration-pointer _clingo-id
        [assigned : (_ptr o _stdbool)] -> (res : _stdbool) ->
      (if res assigned (raise-clingo-error))))
;; Get the size of the string value of the given entry.
;;
;; @pre The @link clingo_configuration_type() type@endlink of the entry must be @ref ::clingo_configuration_type_value.
;; @param[in] configuration the target configuration
;; @param[in] key the key
;; @param[out] size the resulting size
;; @return whether the call was successful
(define-clingo clingo-configuration-value-get-size
  (_fun _clingo-configuration-pointer
        _clingo-id [size : (_ptr o _size)] -> (res : _stdbool) ->
      (if res size (raise-clingo-error)) ))
;; Get the string value of the given entry.
;;
;; @pre The @link clingo_configuration_type() type@endlink of the entry must be @ref ::clingo_configuration_type_value.
;; @pre The given size must be larger or equal to size of the value.
;; @param[in] configuration the target configuration
;; @param[in] key the key
;; @param[out] value the resulting string value
;; @param[in] size the size of the given char array
;; @return whether the call was successful
(define-clingo clingo-configuration-value-get-unsafe
  (_fun _clingo-configuration-pointer _clingo-id
        _bytes _size -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)))
  #:c-id clingo_configuration_value_get)
(define (clingo-configuration-value-get config key)
  (define size (clingo-configuration-value-get-size config key))
  (define buf (make-bytes size))
  (clingo-configuration-value-get-unsafe
   config key buf size)
  (bytes->string/utf-8 buf #f 0 (- size 1)))

;; Set the value of an entry.
;;
;; @pre The @link clingo_configuration_type() type@endlink of the entry must be @ref ::clingo_configuration_type_value.
;; @param[in] configuration the target configuration
;; @param[in] key the key
;; @param[in] value the value to set
;; @return whether the call was successful
(define-clingo clingo-configuration-value-set
  (_fun _clingo-configuration-pointer _clingo-id
        _string -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))
;; @}

;; @}

;; {{{1 statistics

;; @example statistics.c
;; The example shows how to inspect statistics.
;;
;; ## Output ##
;;
;; ~~~~~~~~
;; ./statistics 0
;; Model: a
;; Model: b
;; problem:
;;   lp:
;;     atoms:
;;       2
;;     atoms_aux:
;;       0
;;     ...
;; solving:
;;   ...
;; summary:
;;   ...
;; accu:
;;   times:
;;     ...
;;   models:
;;     ...
;;   solving:
;;     ...
;; ~~~~~~~~
;;
;; ## Code ##

;; @defgroup Statistics Statistics
;; Inspect search and problem statistics.
;;
;; @ingroup Control
;; For an example, see @ref statistics.c.

;; @addtogroup Statistics
;; @{

;; Enumeration for entries of the statistics.

(define _clingo-statistics-type
  (_enum '(
    clingo-statistics-type-empty = 0 ;; the entry is invalid (has neither of the types below)
    clingo-statistics-type-value = 1 ;; the entry is a (double) value
    clingo-statistics-type-array = 2 ;; the entry is an array
    clingo-statistics-type-map   = 3  ;; the entry is a map
  )))

;; Handle for the solver statistics.
(define _clingo-statistics-pointer (_cpointer 'clingo-statistics))

;; Get the root key of the statistics.
;;
;; @param[in] statistics the target statistics
;; @param[out] key the root key
;; @return whether the call was successful
(define-clingo clingo-statistics-root
  (_fun _clingo-statistics-pointer [key : (_ptr o _uint64)] -> (res : _stdbool) ->
      (if res key (raise-clingo-error)) ))
;; Get the type of a key.
;;
;; @param[in] statistics the target statistics
;; @param[in] key the key
;; @param[out] type the resulting type
;; @return whether the call was successful
(define-clingo clingo-statistics-type
  (_fun _clingo-statistics-pointer _uint64
        [type : (_ptr o _clingo-statistics-type)] -> (res : _stdbool) ->
      (if res type (raise-clingo-error)) ))

;; @name Functions to access arrays
;; @{

;; Get the size of an array entry.
;;
;; @pre The @link clingo_statistics_type() type@endlink of the entry must be @ref ::clingo_statistics_type_array.
;; @param[in] statistics the target statistics
;; @param[in] key the key
;; @param[out] size the resulting size
;; @return whether the call was successful
(define-clingo clingo-statistics-array-size
  (_fun _clingo-statistics-pointer _uint64 [size : (_ptr o _size)] -> (res : _stdbool) ->
      (if res size (raise-clingo-error)) ))
;; Get the subkey at the given offset of an array entry.
;;
;; @pre The @link clingo_statistics_type() type@endlink of the entry must be @ref ::clingo_statistics_type_array.
;; @param[in] statistics the target statistics
;; @param[in] key the key
;; @param[in] offset the offset in the array
;; @param[out] subkey the resulting subkey
;; @return whether the call was successful
(define-clingo clingo-statistics-array-at
  (_fun _clingo-statistics-pointer _uint64 _size
        [subkey : (_ptr o _uint64)] -> (res : _stdbool) ->
      (if res subkey (raise-clingo-error)) ))
;; Create the subkey at the end of an array entry.
;;
;; @pre The @link clingo_statistics_type() type@endlink of the entry must be @ref ::clingo_statistics_type_array.
;; @param[in] statistics the target statistics
;; @param[in] key the key
;; @param[in] type the type of the new subkey
;; @param[out] subkey the resulting subkey
;; @return whether the call was successful
(define-clingo clingo-statistics-array-push
  (_fun _clingo-statistics-pointer _uint64 _clingo-statistics-type
        [subkey : (_ptr o _uint64)] -> (res : _stdbool) ->
      (if res subkey (raise-clingo-error)) ))
;; @}

;; @name Functions to access maps
;; @{

;; Get the number of subkeys of a map entry.
;;
;; @pre The @link clingo_statistics_type() type@endlink of the entry must be @ref ::clingo_statistics_type_map.
;; @param[in] statistics the target statistics
;; @param[in] key the key
;; @param[out] size the resulting number
;; @return whether the call was successful
(define-clingo clingo-statistics-map-size
  (_fun _clingo-statistics-pointer _uint64 [size : (_ptr o _size)] -> (res : _stdbool) ->
      (if res size (raise-clingo-error)) ))
;; Test if the given map contains a specific subkey.
;;
;; @pre The @link clingo_statistics_type() type@endlink of the entry must be @ref ::clingo_statistics_type_map.
;; @param[in] statistics the target statistics
;; @param[in] key the key
;; @param[in] name name of the subkey
;; @param[out] result true if the map has a subkey with the given name
;; @return whether the call was successful
(define-clingo clingo-statistics-map-has-subkey
  (_fun _clingo-statistics-pointer _uint64 _string [result : (_ptr o _stdbool)] -> (res : _stdbool) ->
      (if res result (raise-clingo-error)) ))
;; Get the name associated with the offset-th subkey.
;;
;; @pre The @link clingo_statistics_type() type@endlink of the entry must be @ref ::clingo_statistics_type_map.
;; @param[in] statistics the target statistics
;; @param[in] key the key
;; @param[in] offset the offset of the name
;; @param[out] name the resulting name
;; @return whether the call was successful
(define-clingo clingo-statistics-map-subkey-name
  (_fun _clingo-statistics-pointer _uint64 _size [name : (_ptr o _string)] -> (res : _stdbool) ->
      (if res name (raise-clingo-error)) ))
;; Lookup a subkey under the given name.
;;
;; @pre The @link clingo_statistics_type() type@endlink of the entry must be @ref ::clingo_statistics_type_map.
;; @note Multiple levels can be looked up by concatenating keys with a period.
;; @param[in] statistics the target statistics
;; @param[in] key the key
;; @param[in] name the name to lookup the subkey
;; @param[out] subkey the resulting subkey
;; @return whether the call was successful
(define-clingo clingo-statistics-map-at
  (_fun _clingo-statistics-pointer _uint64 _string
        [subkey : (_ptr o _uint64)] -> (res : _stdbool) ->
      (if res subkey (raise-clingo-error)) ))
;; Add a subkey with the given name.
;;
;; @pre The @link clingo_statistics_type() type@endlink of the entry must be @ref ::clingo_statistics_type_map.
;; @param[in] statistics the target statistics
;; @param[in] key the key
;; @param[in] name the name of the new subkey
;; @param[in] type the type of the new subkey
;; @param[out] subkey the index of the resulting subkey
;; @return whether the call was successful
(define-clingo clingo-statistics-map-add-subkey
  (_fun _clingo-statistics-pointer _uint64 _string
        _clingo-statistics-type [subkey : (_ptr o  _uint64)] -> (res : _stdbool) ->
      (if res subkey (raise-clingo-error)) ))
;; @}

;; @name Functions to inspect and change values
;; @{

;; Get the value of the given entry.
;;
;; @pre The @link clingo_statistics_type() type@endlink of the entry must be @ref ::clingo_statistics_type_value.
;; @param[in] statistics the target statistics
;; @param[in] key the key
;; @param[out] value the resulting value
;; @return whether the call was successful
(define-clingo clingo-statistics-value-get
  (_fun _clingo-statistics-pointer _uint64 [value : (_ptr o _double)] -> (res : _stdbool) ->
      (if res value (raise-clingo-error)) ))
;; Set the value of the given entry.
;;
;; @pre The @link clingo_statistics_type() type@endlink of the entry must be @ref ::clingo_statistics_type_value.
;; @param[in] statistics the target statistics
;; @param[in] key the key
;; @param[out] value the new value
;; @return whether the call was successful
(define-clingo clingo-statistics-value-set
  (_fun _clingo-statistics-pointer _uint64 _double -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))
;; @}

;; @}


;; {{{1 model and solve control

;; @example model.c
;; The example shows how to inspect a model.
;;
;; ## Output ##
;;
;; ~~~~~~~~~~~~
;; $ ./model 0
;; Stable model:
;;   shown: c
;;   atoms: b
;;   terms: c
;;  ~atoms: a
;; Stable model:
;;   shown: a
;;   atoms: a
;;   terms:
;;  ~atoms: b
;; ~~~~~~~~~~~~
;;
;; ## Code ##

;; @defgroup Model Model Inspection
;; Inspection of models and a high-level interface to add constraints during solving.
;;
;; For an example, see @ref model.c.
;; @ingroup Control

;; @addtogroup Model
;; @{

;; Object to add clauses during search.
(define _clingo-solve-control-pointer (_cpointer 'clingo-solve-control));

;; Object representing a model.
(define _clingo-model-pointer (_cpointer/null 'clingo-model));

(define _clingo-model-type
  (_enum '(
    clingo-model-type-stable-model          = 0 ;; The model represents a stable model.
    clingo-model-type-brave-consequences    = 1 ;; The model represents a set of brave consequences.
    clingo-model-type-cautious-consequences = 2  ;; The model represents a set of cautious consequences.
  )))

(define _clingo-show-type
  (_enum '(
    clingo-show-type-shown      = 2   ;; Select shown atoms and terms.
    clingo-show-type-atoms      = 4   ;; Select all atoms.
    clingo-show-type-terms      = 8   ;; Select all terms.
    clingo-show-type-theory     = 16  ;; Select symbols added by theory.
    clingo-show-type-all        = 31  ;; Select everything.
    clingo-show-type-complement = 32  ;; Select false instead of true atoms (::clingo_show_type_atoms) or terms (::clingo_show_type_terms).
  )))

;; @name Functions for Inspecting Models
;; @{

;; Get the type of the model.
;;
;; @param[in] model the target
;; @param[out] type the type of the model
;; @return whether the call was successful
(define-clingo clingo-model-type
  (_fun _clingo-model-pointer [type : (_ptr o _clingo-model-type)] -> (res : _stdbool) ->
      (if res type (raise-clingo-error))))
;; Get the running number of the model.
;;
;; @param[in] model the target
;; @param[out] number the number of the model
;; @return whether the call was successful
(define-clingo clingo-model-number
  (_fun _clingo-model-pointer [number : (_ptr o _uint64)] -> (res : _stdbool) ->
      (if res number (raise-clingo-error)) ))
;; Get the number of symbols of the selected types in the model.
;;
;; @param[in] model the target
;; @param[in] show which symbols to select
;; @param[out] size the number symbols
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-model-symbols-size
  (_fun _clingo-model-pointer _clingo-show-type [size : (_ptr o _size)] -> (res : _stdbool) ->
      (if res size (raise-clingo-error))))
;; Get the symbols of the selected types in the model.
;;
;; @note CSP assignments are represented using functions with name "$"
;; where the first argument is the name of the CSP variable and the second one its
;; value.
;;
;; @param[in] model the target
;; @param[in] show which symbols to select
;; @param[out] symbols the resulting symbols
;; @param[in] size the number of selected symbols
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime if the size is too small
;;
;; @see clingo_model_symbols_size()
(define-clingo clingo-model-symbols-unsafe
  (_fun _clingo-model-pointer _clingo-show-type
        [symbols : (_list o _clingo-symbol size)] [size : _size] -> (res : _stdbool) ->
      (if res symbols (raise-clingo-error)))
  #:c-id clingo_model_symbols)
(define (clingo-model-symbols model show-ty)
  (define size (clingo-model-symbols-size model show-ty))
  (clingo-model-symbols-unsafe model show-ty size))
;; Constant time lookup to test whether an atom is in a model.
;;
;; @param[in] model the target
;; @param[in] atom the atom to lookup
;; @param[out] contained whether the atom is contained
;; @return whether the call was successful
(define-clingo clingo-model-contains
  (_fun _clingo-model-pointer _clingo-symbol [contained : (_ptr o _stdbool)] -> (res : _stdbool) ->
      (if res contained (raise-clingo-error)) ))
;; Check if a program literal is true in a model.
;;
;; @param[in] model the target
;; @param[in] literal the literal to lookup
;; @param[out] result whether the literal is true
;; @return whether the call was successful
(define-clingo clingo-model-is-true
  (_fun _clingo-model-pointer _clingo-literal [result : (_ptr o _stdbool)] -> (res : _stdbool) ->
      (if res result (raise-clingo-error))))
;; Get the number of cost values of a model.
;;
;; @param[in] model the target
;; @param[out] size the number of costs
;; @return whether the call was successful
(define-clingo clingo-model-cost-size
  (_fun _clingo-model-pointer [size : (_ptr o _size)] -> (res : _stdbool) ->
      (if res size (raise-clingo-error)) ))
;; Get the cost vector of a model.
;;
;; @param[in] model the target
;; @param[out] costs the resulting costs
;; @param[in] size the number of costs
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime if the size is too small
;;
;; @see clingo_model_cost_size()
;; @see clingo_model_optimality_proven()
(define-clingo clingo-model-cost-unsafe
  (_fun _clingo-model-pointer
        [costs : (_list o _int64 size)] [size : _size] -> (res : _stdbool) ->
      (if res costs (raise-clingo-error)))
  #:c-id clingo_model_cost)
(define (clingo-model-cost model)
  (define size (clingo-model-cost-size model))
  (clingo-model-cost-unsafe model size))
;; Whether the optimality of a model has been proven.
;;
;; @param[in] model the target
;; @param[out] proven whether the optimality has been proven
;; @return whether the call was successful
;;
;; @see clingo_model_cost()
(define-clingo clingo-model-optimality-proven
  (_fun _clingo-model-pointer [proven : (_ptr o _stdbool)] -> (res : _stdbool) ->
      (if res proven (raise-clingo-error))))
;; Get the id of the solver thread that found the model.
;;
;; @param[in] model the target
;; @param[out] id the resulting thread id
;; @return whether the call was successful
(define-clingo clingo-model-thread-id
  (_fun _clingo-model-pointer [id : (_ptr o _clingo-id)] -> (res : _stdbool) ->
      (if res id (raise-clingo-error)) ))
;; Add symbols to the model.
;;
;; These symbols will appear in clingo's output, which means that this
;; function is only meaningful if there is an underlying clingo application.
;; Only models passed to the ::clingo_solve_event_callback_t are extendable.
;;
;; @param[in] model the target
;; @param[in] symbols the symbols to add
;; @param[in] size the number of symbols to add
;; @return whether the call was successful
(define-clingo clingo-model-extend
  (_fun _clingo-model-pointer
        [symbols : (_list i _clingo-symbol)]
        [_size = (length symbols)] -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))
;; @}

;; @name Functions for Adding Clauses
;; @{

;; Get the associated solve control object of a model.
;;
;; This object allows for adding clauses during model enumeration.
;; @param[in] model the target
;; @param[out] control the resulting solve control object
;; @return whether the call was successful
(define-clingo clingo-model-context
  (_fun _clingo-model-pointer
        [control : (_ptr o _clingo-solve-control-pointer)] -> (res : _stdbool) ->
      (if res control (raise-clingo-error)) ))
;; Get an object to inspect the symbolic atoms.
;;
;; @param[in] control the target
;; @param[out] atoms the resulting object
;; @return whether the call was successful
(define-clingo clingo-solve-control-symbolic-atoms
  (_fun _clingo-solve-control-pointer
        [atoms : (_ptr o _clingo-symbolic-atoms-pointer)] -> (res : _stdbool) ->
      (if res atoms (raise-clingo-error)) ))
;; Add a clause that applies to the current solving step during model
;; enumeration.
;;
;; @note The @ref Propagator module provides a more sophisticated
;; interface to add clauses - even on partial assignments.
;;
;; @param[in] control the target
;; @param[in] clause array of literals representing the clause
;; @param[in] size the size of the literal array
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime if adding the clause fails
(define-clingo clingo-solve-control-add-clause
  (_fun _clingo-solve-control-pointer
        [clause : (_list i _clingo-literal)]
        [_size = (length clause)] -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error))))
;; @}

;; @}


;; {{{1 solve result

;; NOTE: documented in Control Module
(define _clingo-solve-result
  (_bitmask '(
    clingo-solve-result-satisfiable   = 1
    clingo-solve-result-unsatisfiable = 2
    clingo-solve-result-exhausted     = 4
    clingo-solve-result-interrupted   = 8
  )))

;; {{{1 solve handle

;; @example solve-async.c
;; The example shows how to solve in the background.
;;
;; ## Output (approximately) ##
;;
;; ~~~~~~~~~~~~
;; ./solve-async 0
;; pi = 3.
;; 1415926535 8979323846 2643383279 5028841971 6939937510 5820974944
;; 5923078164 0628620899 8628034825 3421170679 8214808651 3282306647
;; 0938446095 5058223172 5359408128 4811174502 8410270193 8521105559
;; 6446229489 5493038196 4428810975 6659334461 2847564823 3786783165
;; 2712019091 4564856692 3460348610 4543266482 1339360726 0249141273
;; 7245870066 0631558817 4881520920 9628292540 9171536436 7892590360
;; 0113305305 4882046652 1384146951 9415116094 3305727036 5759591953
;; 0921861173 8193261179 3105118548 0744623799 6274956735 1885752724
;; 8912279381 8301194912 ...
;; ~~~~~~~~~~~~
;;
;; ## Code ##

;; @defgroup SolveHandle Solving
;; Interact with a running search.
;;
;; A ::clingo_solve_handle_t objects can be used for both synchronous and asynchronous search,
;; as well as iteratively receiving models and solve results.
;;
;; For an example showing how to solve asynchronously, see @ref solve-async.c.
;; @ingroup Control

;; @addtogroup SolveHandle
;; @{

;; Enumeration of solve modes.
(define _clingo-solve-mode
  (_enum '(
    clingo-solve-mode-async = 1 ;; Enable non-blocking search.
    clingo-solve-mode-yield = 2 ;; Yield models in calls to clingo-solve-handle-model.
  )))

;; Enumeration of solve events.
(define _clingo-solve-event-type
  (_enum '(
    clingo-solve-event-type-model      = 0 ;; Issued if a model is found.
    clingo-solve-event-type-unsat      = 1 ;; Issued if an optimization problem is found unsatisfiable.
    clingo-solve-event-type-statistics = 2 ;; Issued when the statistics can be updated.
    clingo-solve-event-type-finish     = 3 ;; Issued if the search has completed.
  )))


;; Callback function called during search to notify when the search is finished or a model is ready.
;;
;; If a (non-recoverable) clingo API function fails in this callback, it must return false.
;; In case of errors not related to clingo, set error code ::clingo_error_unknown and return false to stop solving with an error.
;;
;; The event is either a pointer to a model, a pointer to an int64_t* and a size_t, a pointer to two statistics objects (per step and accumulated statistics), or a solve result.
;; @attention If the search is finished, the model is NULL.
;;
;; @param[in] event the current event.
;; @param[in] data user data of the callback
;; @param[out] goon can be set to false to stop solving
;; @return whether the call was successful
;;
;; @see clingo_control_solve()
(define _clingo-solve-event-callback
  (_fun
   _clingo-solve-event-type _pointer _pointer
   (_box _stdbool)  -> _stdbool))

;; Search handle to a solve call.
;;
;; @see clingo_control_solve()
(define _clingo-solve-handle-pointer (_cpointer 'clingo-solve-handle))


;; Get the next solve result.
;;
;; Blocks until the result is ready.
;; When yielding partial solve results can be obtained, i.e.,
;; when a model is ready, the result will be satisfiable but neither the search exhausted nor the optimality proven.
;;
;; @param[in] handle the target
;; @param[out] result the solve result
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime if solving fails
(define-clingo clingo-solve-handle-get
  (_fun _clingo-solve-handle-pointer
        [result : (_ptr o _clingo-solve-result)] -> (res : _stdbool) ->
      (if res result (raise-clingo-error)) ))
;; Wait for the specified amount of time to check if the next result is ready.
;;
;; If the time is set to zero, this function can be used to poll if the search is still active.
;; If the time is negative, the function blocks until the search is finished.
;;
;; @param[in] handle the target
;; @param[in] timeout the maximum time to wait
;; @param[out] result whether the search has finished
(define-clingo clingo-solve-handle-wait
  (_fun _clingo-solve-handle-pointer _double [result : (_ptr o _stdbool)] -> _void
        -> result))
;; Get the next model (or zero if there are no more models).
;;
;; @param[in] handle the target
;; @param[out] model the model (it is NULL if there are no more models)
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime if solving fails
(define-clingo clingo-solve-handle-model
  (_fun _clingo-solve-handle-pointer
        [model : (_ptr o _clingo-model-pointer)] -> (res : _stdbool) ->
      (if res model (raise-clingo-error)) ))

;; Discards the last model and starts the search for the next one.
;;
;; If the search has been started asynchronously, this function continues the search in the background.
;;
;; @note This function does not block.
;;
;; @param[in] handle the target
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime if solving fails
(define-clingo clingo-solve-handle-resume
  (_fun _clingo-solve-handle-pointer -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))
;; Stop the running search and block until done.
;;
;; @param[in] handle the target
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime if solving fails
(define-clingo clingo-solve-handle-cancel
  (_fun _clingo-solve-handle-pointer -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))
;; Stops the running search and releases the handle.
;;
;; Blocks until the search is stopped (as if an implicit cancel was called before the handle is released).
;;
;; @param[in] handle the target
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime if solving fails
(define-clingo clingo-solve-handle-close
  (_fun _clingo-solve-handle-pointer -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))

;; @}
;; {{{1 ground program observer

;; @defgroup ProgramInspection Program Inspection
;; Functions and data structures to inspect programs.
;; @ingroup Control

;; @addtogroup ProgramInspection
;; @{

;; An instance of this struct has to be registered with a solver to observe ground directives as they are passed to the solver.
;;
;; @note This interface is closely modeled after the aspif format.
;; For more information please refer to the specification of the aspif format.
;;
;; Not all callbacks have to be implemented and can be set to NULL if not needed.
;; If one of the callbacks in the struct fails, grounding is stopped.
;; If a non-recoverable clingo API call fails, a callback must return false.
;; Otherwise ::clingo_error_unknown should be set and false returned.
;;
;; @see clingo_control_register_observer()


(define-cstruct _clingo-ground-program-observer (
    ;; Called once in the beginning.
    ;;
    ;; If the incremental flag is true, there can be multiple calls to @ref clingo_control_solve().
    ;;
    ;; @param[in] incremental whether the program is incremental
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*init_program)(bool incremental, void *data);
    [init-program (_fun _stdbool _pointer -> _stdbool)]
    ;; Marks the beginning of a block of directives passed to the solver.
    ;;
    ;; @see @ref end_step
    ;;
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*begin_step)(void *data);
    [begin-step (_fun _pointer -> _stdbool)]
    ;; Marks the end of a block of directives passed to the solver.
    ;;
    ;; This function is called before solving starts.
    ;;
    ;; @see @ref begin_step
    ;;
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*end_step)(void *data);
    [end-step (_fun _pointer -> _stdbool)]

    ;; Observe rules passed to the solver.
    ;;
    ;; @param[in] choice determines if the head is a choice or a disjunction
    ;; @param[in] head the head atoms
    ;; @param[in] head_size the number of atoms in the head
    ;; @param[in] body the body literals
    ;; @param[in] body_size the number of literals in the body
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*rule)(bool choice, clingo_atom_t const *head, size_t head_size, clingo_literal_t const *body, size_t body_size, void *data);
    [rule (_fun _stdbool
                [head : (_list i _clingo-atom)] [_size = (length head)]
                [body : (_list i _clingo-literal)] [_size = (length body)]
                _pointer -> _stdbool)]
    ;; Observe weight rules passed to the solver.
    ;;
    ;; @param[in] choice determines if the head is a choice or a disjunction
    ;; @param[in] head the head atoms
    ;; @param[in] head_size the number of atoms in the head
    ;; @param[in] lower_bound the lower bound of the weight rule
    ;; @param[in] body the weighted body literals
    ;; @param[in] body_size the number of weighted literals in the body
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*weight_rule)(bool choice, clingo_atom_t const *head, size_t head_size, clingo_weight_t lower_bound, clingo_weighted_literal_t const *body, size_t body_size, void *data);
    [weight-rule
     (_fun _stdbool
           [head : (_list i _clingo-atom)] [_size = (length head)]
           [body : (_list i _clingo-weighted-literal)] [_size = (length body)]
                _pointer -> _stdbool)]
    ;; Observe minimize constraints (or weak constraints) passed to the solver.
    ;;
    ;; @param[in] priority the priority of the constraint
    ;; @param[in] literals the weighted literals whose sum to minimize
    ;; @param[in] size the number of weighted literals
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*minimize)(clingo_weight_t priority, clingo_weighted_literal_t const* literals, size_t size, void *data);
    [minimize (_fun _clingo-weight
                    [literals : (_list i _clingo-weighted-literal)]
                    [_size = (length literals)]
                    _pointer -> _stdbool)]
    
    ;; Observe projection directives passed to the solver.
    ;;
    ;; @param[in] atoms the atoms to project on
    ;; @param[in] size the number of atoms
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*project)(clingo_atom_t const *atoms, size_t size, void *data);
    [project (_fun [atoms : (_list i _clingo-atom)]
                   [_size = (length atoms)] _pointer -> _stdbool)]
    ;; Observe shown atoms passed to the solver.
    ;; \note Facts do not have an associated aspif atom.
    ;; The value of the atom is set to zero.
    ;;
    ;; @param[in] symbol the symbolic representation of the atom
    ;; @param[in] atom the aspif atom (0 for facts)
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*output_atom)(clingo_symbol_t symbol, clingo_atom_t atom, void *data);
    [output-atom (_fun _clingo-symbol _clingo-atom _pointer -> _stdbool)]
    ;; Observe shown terms passed to the solver.
    ;;
    ;; @param[in] symbol the symbolic representation of the term
    ;; @param[in] condition the literals of the condition
    ;; @param[in] size the size of the condition
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*output_term)(clingo_symbol_t symbol, clingo_literal_t const *condition, size_t size, void *data);
    [output-term (_fun _clingo-symbol
                       [condition : (_list i _clingo-literal)]
                       [_size = (length condition)]
                       _pointer -> _stdbool)]
    ;; Observe external statements passed to the solver.
    ;;
    ;; @param[in] atom the external atom
    ;; @param[in] type the type of the external statement
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*external)(clingo_atom_t atom, clingo_external_type_t type, void *data);
    [external (_fun _clingo-atom _clingo-external-type _pointer -> _stdbool)]
    ;; Observe assumption directives passed to the solver.
    ;;
    ;; @param[in] literals the literals to assume (positive literals are true and negative literals false for the next solve call)
    ;; @param[in] size the number of atoms
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*assume)(clingo_literal_t const *literals, size_t size, void *data);
    [assume (_fun [literals : (_list i _clingo-literal)]
                  [_size = (length literals)]
                  _pointer -> _stdbool)]
    ;; Observe heuristic directives passed to the solver.
    ;;
    ;; @param[in] atom the target atom
    ;; @param[in] type the type of the heuristic modification
    ;; @param[in] bias the heuristic bias
    ;; @param[in] priority the heuristic priority
    ;; @param[in] condition the condition under which to apply the heuristic modification
    ;; @param[in] size the number of atoms in the condition
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*heuristic)(clingo_atom_t atom, clingo_heuristic_type_t type, int bias, unsigned priority, clingo_literal_t const *condition, size_t size, void *data);
    [heuristic (_fun _clingo-atom _clingo-heuristic-type _int
                     _uint
                     [condition : (_list i _clingo-literal)]
                     [_size = (length condition)]
                     _pointer -> _stdbool)]
    ;; Observe edge directives passed to the solver.
    ;;
    ;; @param[in] node_u the start vertex of the edge
    ;; @param[in] node_v the end vertex of the edge
    ;; @param[in] condition the condition under which the edge is part of the graph
    ;; @param[in] size the number of atoms in the condition
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*acyc_edge)(int node_u, int node_v, clingo_literal_t const *condition, size_t size, void *data);
    [acyc-edge (_fun _int _int
                     [condition : (_list i _clingo-literal)]
                     [_size = (length condition)] _pointer -> _stdbool)]

    ;; Observe numeric theory terms.
    ;;
    ;; @param[in] term_id the id of the term
    ;; @param[in] number the value of the term
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*theory_term_number)(clingo_id_t term_id, int number, void *data);
    [theory-term-number (_fun _clingo-id _int _pointer -> _stdbool)]
    ;; Observe string theory terms.
    ;;
    ;; @param[in] term_id the id of the term
    ;; @param[in] name the value of the term
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*theory_term_string)(clingo_id_t term_id, char const *name, void *data);
    [theory-term-string (_fun _clingo-id _string _pointer -> _stdbool)]
    ;; Observe compound theory terms.
    ;;
    ;; The name_id_or_type gives the type of the compound term:
    ;; - if it is -1, then it is a tuple
    ;; - if it is -2, then it is a set
    ;; - if it is -3, then it is a list
    ;; - otherwise, it is a function and name_id_or_type refers to the id of the name (in form of a string term)
    ;;
    ;; @param[in] term_id the id of the term
    ;; @param[in] name_id_or_type the name or type of the term
    ;; @param[in] arguments the arguments of the term
    ;; @param[in] size the number of arguments
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*theory_term_compound)(clingo_id_t term_id, int name_id_or_type, clingo_id_t const *arguments, size_t size, void *data);
    [theory-term-compound
     (_fun _clingo-id _int
           [arguments : (_list i _clingo-id)]
           [_size = (length arguments)] _pointer -> _stdbool)]
    ;; Observe theory elements.
    ;;
    ;; @param element_id the id of the element
    ;; @param terms the term tuple of the element
    ;; @param terms_size the number of terms in the tuple
    ;; @param condition the condition of the elemnt
    ;; @param condition_size the number of literals in the condition
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*theory_element)(clingo_id_t element_id, clingo_id_t const *terms, size_t terms_size, clingo_literal_t const *condition, size_t condition_size, void *data);
    [theory-element
     (_fun _clingo-id
           [terms : (_list i _clingo-id)] [_size = (length terms)]
           [condition : (_list i _clingo-id)] [_size = (length condition)]
           _pointer -> _stdbool)]
    ;; Observe theory atoms without guard.
    ;;
    ;; @param[in] atom_id_or_zero the id of the atom or zero for directives
    ;; @param[in] term_id the term associated with the atom
    ;; @param[in] elements the elements of the atom
    ;; @param[in] size the number of elements
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*theory_atom)(clingo_id_t atom_id_or_zero, clingo_id_t term_id, clingo_id_t const *elements, size_t size, void *data);
    [theory-atom
     (_fun _clingo-id _clingo-id
           [elements : (_list i _clingo-id)] [_size = (length elements)]
           _pointer -> _stdbool)]
    ;; Observe theory atoms with guard.
    ;;
    ;; @param[in] atom_id_or_zero the id of the atom or zero for directives
    ;; @param[in] term_id the term associated with the atom
    ;; @param[in] elements the elements of the atom
    ;; @param[in] size the number of elements
    ;; @param[in] operator_id the id of the operator (a string term)
    ;; @param[in] right_hand_side_id the id of the term on the right hand side of the atom
    ;; @param[in] data user data for the callback
    ;; @return whether the call was successful
    ;; bool (*theory_atom_with_guard)(clingo_id_t atom_id_or_zero, clingo_id_t term_id, clingo_id_t const *elements, size_t size, clingo_id_t operator_id, clingo_id_t right_hand_side_id, void *data);
    [theory-atom-with-guard
     (_fun _clingo-id _clingo-id
           [elements : (_list i _clingo-id)]
           [_size = (length elements)]
           _clingo-id _clingo-id _pointer -> _stdbool)]
))
;; @}


;; {{{1 control

;; @example control.c
;; The example shows how to ground and solve a simple logic program, and print
;; its answer sets.
;;
;; ## Output ##
;;
;; ~~~~~~~~~~~~
;; ./control 0
;; Model: a
;; Model: b
;; ~~~~~~~~~~~~
;;
;; ## Code ##

;; @defgroup Control Grounding and Solving
;; Functions to control the grounding and solving process.
;;
;; For an example, see @ref control.c.

;; @addtogroup Control
;; @{

;; @enum clingo_solve_result_e
;; Enumeration of bit masks for solve call results.
;;
;; @note Neither ::clingo_solve_result_satisfiable nor
;; ::clingo_solve_result_exhausted is set if the search is interrupted and no
;; model was found.
;;
;; @var clingo_solve_result::clingo_solve_result_satisfiable
;; The last solve call found a solution.
;; @var clingo_solve_result::clingo_solve_result_unsatisfiable
;; The last solve call did not find a solution.
;; @var clingo_solve_result::clingo_solve_result_exhausted
;; The last solve call completely exhausted the search space.
;; @var clingo_solve_result::clingo_solve_result_interrupted
;; The last solve call was interrupted.
;;
;; @see clingo_control_interrupt()

;; @typedef clingo_solve_result_bitset_t
;; Corresponding type to ::clingo_solve_result_e.

;; Struct used to specify the program parts that have to be grounded.
;;
;; Programs may be structured into parts, which can be grounded independently with ::clingo_control_ground.
;; Program parts are mainly interesting for incremental grounding and multi-shot solving.
;; For single-shot solving, program parts are not needed.
;;
;; @note Parts of a logic program without an explicit <tt>\#program</tt>
;; specification are by default put into a program called `base` without
;; arguments.
;;
;; @see clingo_control_ground()
(define-cstruct _clingo-part (
    [name _string];              ;; name of the program part
    [params _pointer]            ;; array of parameters (_cvector _clingo-symbol size)
    [size _size];                ;; number of parameters
 ))

;; Callback function to implement external functions.
;;
;; If an external function of form <tt>\@name(parameters)</tt> occurs in a logic program,
;; then this function is called with its location, name, parameters, and a callback to inject symbols as arguments.
;; The callback can be called multiple times; all symbols passed are injected.
;;
;; If a (non-recoverable) clingo API function fails in this callback, for example, the symbol callback, the callback must return false.
;; In case of errors not related to clingo, this function can set error ::clingo_error_unknown and return false to stop grounding with an error.
;;
;; @param[in] location location from which the external function was called
;; @param[in] name name of the called external function
;; @param[in] arguments arguments of the called external function
;; @param[in] arguments_size number of arguments
;; @param[in] data user data of the callback
;; @param[in] symbol_callback function to inject symbols
;; @param[in] symbol_callback_data user data for the symbol callback
;;            (must be passed untouched)
;; @return whether the call was successful
;; @see clingo_control_ground()
;;
;; The following example implements the external function <tt>\@f()</tt> returning 42.
;; ~~~~~~~~~~~~~~~{.c}
;; bool
;; ground_callback(clingo_location_t const *location,
;;                 char const *name,
;;                 clingo_symbol_t const *arguments,
;;                 size_t arguments_size,
;;                 void *data,
;;                 clingo_symbol_callback_t symbol_callback,
;;                 void *symbol_callback_data) {
;;   if (strcmp(name, "f") == 0 && arguments_size == 0) {
;;     clingo_symbol_t sym;
;;     clingo_symbol_create_number(42, &sym);
;;     return symbol_callback(&sym, 1, symbol_callback_data);
;;   }
;;   clingo_set_error(clingo_error_runtime, "function not found");
;;   return false;
;; }
;; ~~~~~~~~~~~~~~~
(define _clingo-ground-callback
  (_fun
   (_box _clingo-location)
   _string
   [arguments : (_list io _clingo-symbol size)]
   [size : _size]
   _pointer _clingo-symbol-callback _pointer
   -> _stdbool))

;; Control object holding grounding and solving state.
(define _clingo-control-pointer (_cpointer 'clingo-control))

;; Create a new control object.
;;
;; A control object has to be freed using clingo_control_free().
;;
;; @note Only gringo options (without <code>\-\-output</code>) and clasp's options are supported as arguments,
;; except basic options such as <code>\-\-help</code>.
;; Furthermore, a control object is blocked while a search call is active;
;; you must not call any member function during search.
;;
;; If the logger is NULL, messages are printed to stderr.
;;
;; @param[in] arguments C string array of command line arguments
;; @param[in] arguments_size size of the arguments array
;; @param[in] logger callback functions for warnings and info messages
;; @param[in] logger_data user data for the logger callback
;; @param[in] message_limit maximum number of times the logger callback is called
;; @param[out] control resulting control object
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime if argument parsing fails
(define-clingo clingo-control-new
  (_fun [arguments : (_list i _string)] [_size = (length arguments)]
        _clingo-logger _pointer _uint
        [control : (_ptr o _clingo-control-pointer)]  -> (res : _stdbool) ->
      (if res control (raise-clingo-error)) ))

;; Free a control object created with clingo_control_new().
;; @param[in] control the target
(define-clingo clingo-control-free
  (_fun _clingo-control-pointer -> _void))

;; @name Grounding Functions
;; @{

;; Extend the logic program with a program in a file.
;;
;; @param[in] control the target
;; @param[in] file path to the file
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime if parsing or checking fails
(define-clingo clingo-control-load
  (_fun _clingo-control-pointer _string -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error))))

;; Extend the logic program with the given non-ground logic program in string form.
;;
;; This function puts the given program into a block of form: <tt>\#program name(parameters).</tt>
;;
;; After extending the logic program, the corresponding program parts are typically grounded with ::clingo_control_ground.
;;
;; @param[in] control the target
;; @param[in] name name of the program block
;; @param[in] parameters string array of parameters of the program block
;; @param[in] parameters_size number of parameters
;; @param[in] program string representation of the program
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime if parsing fails
(define-clingo clingo-control-add
  (_fun _clingo-control-pointer _string
        [parameters : (_list i _string)] [_size = (length parameters)]
        _string -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error))))

;; Ground the selected @link ::clingo_part parts @endlink of the current (non-ground) logic program.
;;
;; After grounding, logic programs can be solved with ::clingo_control_solve().
;;
;; @note Parts of a logic program without an explicit <tt>\#program</tt>
;; specification are by default put into a program called `base` without
;; arguments.
;;
;; @param[in] control the target
;; @param[in] parts array of parts to ground
;; @param[in] parts_size size of the parts array
;; @param[in] ground_callback callback to implement external functions
;; @param[in] ground_callback_data user data for ground_callback
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - error code of ground callback
;;
;; @see clingo_part
(define-clingo clingo-control-ground
  (_fun _clingo-control-pointer
        [parts : (_list i _clingo-part)] [_size = (length parts)]
        _clingo-ground-callback _pointer -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))

;; @}

;; @name Solving Functions
;; @{

;; Solve the currently @link ::clingo_control_ground grounded @endlink logic program enumerating its models.
;;
;; See the @ref SolveHandle module for more information.
;;
;; @param[in] control the target
;; @param[in] mode configures the search mode
;; @param[in] assumptions array of assumptions to solve under
;; @param[in] assumptions_size number of assumptions
;; @param[in] notify the event handler to register
;; @param[in] data the user data for the event handler
;; @param[out] handle handle to the current search to enumerate models
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;; - ::clingo_error_runtime if solving could not be started
(define-clingo clingo-control-solve
  (_fun _clingo-control-pointer _clingo-solve-mode
        [assumptions : (_list i _clingo-literal)]
        [_size = (length assumptions)]
        _clingo-solve-event-callback _pointer
        [handle : (_ptr o _clingo-solve-handle-pointer)] -> (res : _stdbool) ->
      (if res handle (raise-clingo-error))))
;; Clean up the domains of the grounding component using the solving
;; component's top level assignment.
;;
;; This function removes atoms from domains that are false and marks atoms as
;; facts that are true.  With multi-shot solving, this can result in smaller
;; groundings because less rules have to be instantiated and more
;; simplifications can be applied.
;;
;; @note It is typically not necessary to call this function manually because
;; automatic cleanups at the right time are enabled by default.
;; 
;; @param[in] control the target
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
;;
;; @see clingo_control_get_enable_cleanup()
;; @see clingo_control_set_enable_cleanup()
(define-clingo clingo-control-cleanup
  (_fun _clingo-control-pointer -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error))))
;; Assign a truth value to an external atom.
;;
;; If a negative literal is passed, the corresponding atom is assigned the
;; inverted truth value.
;;
;; If the atom does not exist or is not external, this is a noop.
;;
;; @param[in] control the target
;; @param[in] literal literal to assign
;; @param[in] value the truth value
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-control-assign-external
  (_fun _clingo-control-pointer _clingo-literal _clingo-truth-value -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error))))
;; Release an external atom.
;;
;; If a negative literal is passed, the corresponding atom is released.
;;
;; After this call, an external atom is no longer external and subject to
;; program simplifications.  If the atom does not exist or is not external,
;; this is a noop.
;;
;; @param[in] control the target
;; @param[in] literal literal to release
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-control-release-external
  (_fun _clingo-control-pointer _clingo-literal -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error))))
;; Register a custom propagator with the control object.
;;
;; If the sequential flag is set to true, the propagator is called
;; sequentially when solving with multiple threads.
;;
;; See the @ref Propagator module for more information.
;;
;; @param[in] control the target
;; @param[in] propagator the propagator
;; @param[in] data user data passed to the propagator functions
;; @param[in] sequential whether the propagator should be called sequentially
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-control-register-propagator
  (_fun _clingo-control-pointer
        _clingo-propagator-pointer _pointer _stdbool -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error))))
;; Check if the solver has determined that the internal program representation is conflicting.
;;
;; If this function returns true, solve calls will return immediately with an unsatisfiable solve result.
;; Note that conflicts first have to be detected, e.g. -
;; initial unit propagation results in an empty clause,
;; or later if an empty clause is resolved during solving.
;; Hence, the function might return false even if the problem is unsatisfiable.
;;
;; @param[in] control the target
;; @return whether the program representation is conflicting
(define-clingo clingo-control-is-conflicting
  (_fun _clingo-control-pointer -> _stdbool))

;; Get a statistics object to inspect solver statistics.
;;
;; Statistics are updated after a solve call.
;;
;; See the @ref Statistics module for more information.
;;
;; @attention
;; The level of detail of the statistics depends on the stats option
;; (which can be set using @ref Configuration module or passed as an option when @link clingo_control_new creating the control object@endlink).
;; The default level zero only provides basic statistics,
;; level one provides extended and accumulated statistics,
;; and level two provides per-thread statistics.
;; Furthermore, the statistics object is best accessed right after solving.
;; Otherwise, not all of its entries have valid values.
;;
;; @param[in] control the target
;; @param[out] statistics the statistics object
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-control-statistics
  (_fun _clingo-control-pointer
        [statistics : (_ptr o _clingo-statistics-pointer)] -> (res : _stdbool) ->
      (if res statistics (raise-clingo-error))))
;; Interrupt the active solve call (or the following solve call right at the beginning).
;;
;; @param[in] control the target
(define-clingo clingo-control-interrupt (_fun _clingo-control-pointer -> _void ))
;; Get low-level access to clasp.
;;
;; @attention
;; This function is intended for experimental use only and not part of the stable API.
;;
;; This function may return a <code>nullptr</code>.
;; Otherwise, the returned pointer can be casted to a ClaspFacade pointer.
;;
;; @param[in] control the target
;; @param[out] clasp pointer to the ClaspFacade object (may be <code>nullptr</code>)
;; @return whether the call was successful
(define-clingo clingo-control-clasp-facade
  (_fun _clingo-control-pointer [clasp : (_ptr o _pointer)] -> (res : _stdbool) ->
      (if res clasp (raise-clingo-error)) ))

;; @}

;; @name Configuration Functions
;; @{

;; Get a configuration object to change the solver configuration.
;;
;; See the @ref Configuration module for more information.
;;
;; @param[in] control the target
;; @param[out] configuration the configuration object
;; @return whether the call was successful
(define-clingo clingo-control-configuration
  (_fun _clingo-control-pointer
        [configuration : (_ptr o _clingo-configuration-pointer)] -> (res : _stdbool) ->
      (if res configuration (raise-clingo-error))))

;; @}

;; @name Program Inspection Functions
;; @{

;; Return the symbol for a constant definition of form: <tt>\#const name = symbol</tt>.
;;
;; @param[in] control the target
;; @param[in] name the name of the constant
;; @param[out] symbol the resulting symbol
;; @return whether the call was successful
(define-clingo clingo-control-get-const
  (_fun _clingo-control-pointer _string
        [symbol : (_ptr o _clingo-symbol)] -> (res : _stdbool) ->
      (if res symbol (raise-clingo-error))))
;; Check if there is a constant definition for the given constant.
;;
;; @param[in] control the target
;; @param[in] name the name of the constant
;; @param[out] exists whether a matching constant definition exists
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_runtime if constant definition does not exist
;;
;; @see clingo_control_get_const()
(define-clingo clingo-control-has-const
  (_fun _clingo-control-pointer _string
        [exists : (_ptr o _stdbool)] -> (res : _stdbool) ->
      (if res exists (raise-clingo-error))))
;; Get an object to inspect symbolic atoms (the relevant Herbrand base) used
;; for grounding.
;;
;; See the @ref SymbolicAtoms module for more information.
;;
;; @param[in] control the target
;; @param[out] atoms the symbolic atoms object
;; @return whether the call was successful
(define-clingo clingo-control-symbolic-atoms
  (_fun _clingo-control-pointer
        [atoms : (_ptr o _clingo-symbolic-atoms-pointer)] -> (res : _stdbool) ->
      (if res atoms (raise-clingo-error))))
;; Get an object to inspect theory atoms that occur in the grounding.
;;
;; See the @ref TheoryAtoms module for more information.
;;
;; @param[in] control the target
;; @param[out] atoms the theory atoms object
;; @return whether the call was successful
(define-clingo clingo-control-theory-atoms
  (_fun _clingo-control-pointer
        [atoms : (_ptr o _clingo-theory-atoms-pointer)] -> (res : _stdbool) ->
      (if res atoms (raise-clingo-error))))
;; Register a program observer with the control object.
;;
;; @param[in] control the target
;; @param[in] observer the observer to register
;; @param[in] replace just pass the grounding to the observer but not the solver
;; @param[in] data user data passed to the observer functions
;; @return whether the call was successful
(define-clingo clingo-control-register-observer
  (_fun _clingo-control-pointer _clingo-ground-program-observer-pointer _stdbool _pointer -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error))))
;; @}

;; @name Program Modification Functions
;; @{

;; Get an object to add ground directives to the program.
;;
;; See the @ref ProgramBuilder module for more information.
;;
;; @param[in] control the target
;; @param[out] backend the backend object
;; @return whether the call was successful; might set one of the following error codes:
;; - ::clingo_error_bad_alloc
(define-clingo clingo-control-backend
  (_fun _clingo-control-pointer
        [backend : (_ptr o _clingo-backend-pointer)] -> (res : _stdbool) ->
      (if res backend (raise-clingo-error))))
;; @}

;; @}

;; {{{1 extending clingo

;; @example application.c
;; The example shows how to extend the clingo application.
;;
;; It behaves like a normal normal clingo but adds one option to override the default program part to ground.
;; ## Example calls ##
;;
;; ~~~~~~~~~~~~
;; $ cat example.lp
;; b.
;; #program test.
;; t.
;;
;; $ ./application --program test example.lp
;; example version 1.0.0
;; Reading from example.lp
;; Solving...
;; Answer: 1
;; t
;; SATISFIABLE
;;
;; Models       : 1+
;; Calls        : 1
;; Time         : 0.004s (Solving: 0.00s 1st Model: 0.00s Unsat: 0.00s)
;; CPU Time     : 0.004s
;; ~~~~~~~~~~~~
;;
;; ## Code ##

;; @defgroup ExtendingClingo Extending Clingo
;; Functions to customize clingo's main function.
;;
;; This module allows for customizing the clingo application.
;; For example, this can be used to register custom propagators and command line options with clingo.
;;
;; Warning: This part of the API is not yet finalized and might change in the future.

;; @addtogroup ExtendingClingo
;; @{

;; Object to add command-line options.
(define _clingo-options-pointer (_cpointer 'clingo-options-pointer))

;; Callback to customize clingo main function.
;;
;; @param[in] control corresponding control object
;; @param[in] files files passed via command line arguments
;; @param[in] size number of files
;; @param[in] data user data for the callback
;;
;; @return whether the call was successful
(define _clingo-main-function
  (_fun _clingo-control-pointer
        [files : (_list i _string)]
        [_size = (length files)] _pointer -> _stdbool))

;; Callback to print a model in default format.
;;
;; @param[in] data user data for the callback
;;
;; @return whether the call was successful
(define _clingo-default-model-printer
  (_fun _pointer -> _stdbool))


;; Callback to customize model printing.
;;
;; @param[in] model the model
;; @param[in] printer the default model printer
;; @param[in] printer_data user data for the printer
;; @param[in] data user data for the callback
;;
;; @return whether the call was successful
(define
  _clingo-model-printer
  (_fun _clingo-model-pointer _clingo-default-model-printer _pointer _pointer -> _stdbool))

;; This struct contains a set of functions to customize the clingo application.
(define-cstruct _clingo-application
 (
   [program-name (_fun _pointer -> _string)]                        ;; callback to obtain program name
   [version (_fun _pointer -> _string)]                             ;; callback to obtain version information
   [message-limit (_fun _pointer -> _uint)]                          ;; callback to obtain message limit
   [main _clingo-main-function]                                     ;; callback to override clingo's main function
   [logger _clingo-logger]                                          ;; callback to override default logger
   [printer _clingo-model-printer]                                  ;; callback to override default model printing
   [register-options (_fun _clingo-options-pointer _pointer -> _stdbool)] ;; callback to register options
   [validate-options (_fun _pointer -> _stdbool)]                         ;; callback validate options
))


;; Add an option that is processed with a custom parser.
;;
;; Note that the parser also has to take care of storing the semantic value of
;; the option somewhere.
;;
;; Parameter option specifies the name(s) of the option.
;; For example, "ping,p" adds the short option "-p" and its long form "--ping".
;; It is also possible to associate an option with a help level by adding ",@l" to the option specification.
;; Options with a level greater than zero are only shown if the argument to help is greater or equal to l.
;;
;; @param[in] options object to register the option with
;; @param[in] group options are grouped into sections as given by this string
;; @param[in] option specifies the command line option
;; @param[in] description the description of the option
;; @param[in] parse callback to parse the value of the option
;; @param[in] data user data for the callback
;; @param[in] multi whether the option can appear multiple times on the command-line
;; @param[in] argument optional string to change the value name in the generated help output
;; @return whether the call was successful
(define-clingo clingo-options-add
  (_fun _clingo-options-pointer _string _string _string
        (_fun _string _pointer -> _stdbool) _pointer _stdbool _string -> (res : _stdbool) ->
      (if res (void) (raise-clingo-error)) ))
;; Add an option that is a simple flag.
;;
;; This function is similar to @ref clingo_options_add() but simpler because it only supports flags, which do not have values.
;; If a flag is passed via the command-line the parameter target is set to true.
;;
;; @param[in] options object to register the option with
;; @param[in] group options are grouped into sections as given by this string
;; @param[in] option specifies the command line option
;; @param[in] description the description of the option
;; @param[in] target boolean set to true if the flag is given on the command-line
;; @return whether the call was successful
(define-clingo clingo-options-add-flag
  (_fun _clingo-options-pointer _string _string _string
        [target : (_ptr o _stdbool)] -> (res : _stdbool) ->
      (if res target (raise-clingo-error)) ))

;; Run clingo with a customized main function (similar to python and lua embedding).
;;
;; @param[in] application struct with callbacks to override default clingo functionality
;; @param[in] arguments command line arguments
;; @param[in] size number of arguments
;; @param[in] data user data to pass to callbacks in application
;; @return exit code to return from main function
(define-clingo clingo-main
  (_fun _clingo-application-pointer
        [arguments : (_list i _string)]
        [_size = (length arguments)] _pointer -> _int))


;; Custom scripting language to run functions during grounding.
(define-cstruct _clingo-script (
    ;; Evaluate the given source code.
    ;; @param[in] location the location in the logic program of the source code
    ;; @param[in] code the code to evaluate
    ;; @param[in] data user data as given when registering the script
    ;; @return whether the function call was successful
    ;; bool (*execute) (clingo_location_t const *location, char const *code, void *data);
    [execute (_fun _clingo-location-pointer _string _pointer -> _stdbool)]
    ;; Call the function with the given name and arguments.
    ;; @param[in] location the location in the logic program of the function call
    ;; @param[in] name the name of the function
    ;; @param[in] arguments the arguments to the function
    ;; @param[in] arguments_size the number of arguments
    ;; @param[in] symbol_callback callback to return a pool of symbols
    ;; @param[in] symbol_callback_data user data for the symbol callback
    ;; @param[in] data user data as given when registering the script
    ;; @return whether the function call was successful
    ;; bool (*call) (clingo_location_t const *location, char const *name, clingo_symbol_t const *arguments, size_t arguments_size, clingo_symbol_callback_t symbol_callback, void *symbol_callback_data, void *data);
    [call (_fun _clingo-location-pointer _string
                [arguments : (_list i _clingo-symbol)] [_size = (length arguments)]
                _clingo-symbol-callback _pointer _pointer -> _stdbool)]
    ;; Check if the given function is callable.
    ;; @param[in] name the name of the function
    ;; @param[out] result whether the function is callable
    ;; @param[in] data user data as given when registering the script
    ;; @return whether the function call was successful
    ;; bool (*callable) (char const * name, bool *result, void *data);
    [callable (_fun _string [result : (_ptr o _stdbool)]
                    _pointer -> (res : _stdbool) ->
                    (if res result (raise-clingo-error)))]
    ;; Run the main function.
    ;; @param[in] control the control object to pass to the main function
    ;; @param[in] data user data as given when registering the script
    ;; @return whether the function call was successful
    ;; bool (*main) (clingo_control_t *control, void *data);
    [main (_fun _clingo-control-pointer _pointer -> _stdbool)]
    ;; This function is called once when the script is deleted.
    ;; @param[in] data user data as given when registering the script
    ;; void (*free) (void *data);
    [free (_fun _pointer -> _void)]
    ;; char const *version;
    [version _string]
))


;; @}

;; }}}1

(module+ latest
  (provide
   clingo-propagate-init-add-literal
   clingo-propagate-init-add-weight-constraint
   clingo-propagate-init-add-minimize
   clingo-propagate-init-propagate
   clingo-backend-theory-term-number
   clingo-backend-theory-term-string
   clingo-backend-theory-term-sequence
   clingo-backend-theory-term-function
   clingo-backend-theory-term-symbol
   clingo-backend-theory-element
   clingo-backend-theory-atom
   clingo-backend-theory-atom-with-guard   
   clingo-solve-handle-core
   clingo-control-set-enable-enumeration-assumption
   clingo-control-get-enable-enumeration-assumption
   clingo-control-set-enable-cleanup
   clingo-control-get-enable-cleanup
   clingo-register-script
   clingo-get-script-version)
  ;; The (positive) literal at the given offset in the assignment.
  ;;
  ;; @param[in] assignment the target
  ;; @param[in] offset the offset of the literal
  ;; @param[out] literal the literal
  ;; @return whether the call was successful
  (define-clingo clingo-assignment-at
    (_fun _clingo-assignment-pointer _size [literal : (_ptr o _clingo-literal)] -> (res : _stdbool)
          -> (if res literal (raise-clingo-error))))
  ;; Returns the number of literals in the trail, i.e., the number of assigned literals.
  ;;
  ;; @param[in] assignment the target
  ;; @param[out] size the number of literals in the trail
  ;; @return whether the call was successful
  (define-clingo clingo-assignment-trail-size
    (_fun _clingo-assignment-pointer [size : (_ptr o _uint32)] -> (res : _stdbool)
          -> (if res size (raise-clingo-error)) ))
  ;; Returns the offset of the decision literal with the given decision level in
  ;; the trail.
  ;;
  ;; @note Literals in the trail are ordered by decision levels, where the first
  ;; literal with a larger level than the previous literals is a decision; the
  ;; following literals with same level are implied by this decision literal.
  ;; Each decision level up to and including the current decision level has a
  ;; valid offset in the trail.
  ;;
  ;; @param[in] assignment the target
  ;; @param[in] level the decision level
  ;; @param[out] offset the offset of the decision literal
  ;; @return whether the call was successful
  (define-clingo clingo-assignment-trail-begin
    (_fun _clingo-assignment-pointer _uint32 [offset : (_ptr o _uint32)] -> (res : _stdbool)
          -> (if res offset (raise-clingo-error))))
  ;; Returns the offset following the last literal with the given decision level.
  ;;
  ;; @note This function is the counter part to clingo_assignment_trail_begin().
  ;;
  ;; @param[in] assignment the target
  ;; @param[in] level the decision level
  ;; @param[out] offset the offset
  ;; @return whether the call was successful
  (define-clingo clingo-assignment-trail-end
    (_fun _clingo-assignment-pointer _uint32 [offset : (_ptr o _uint32)] -> (res : _stdbool)
          -> (if res offset (raise-clingo-error))))
  ;; Returns the literal at the given position in the trail.
  ;;
  ;; @param[in] assignment the target
  ;; @param[in] offset the offset of the literal
  ;; @param[out] literal the literal
  ;; @return whether the call was successful
  (define-clingo clingo-assignment-trail-at
    (_fun _clingo-assignment-pointer _uint32 [literal : (_ptr o _clingo-literal)] -> (res : _stdbool)
          -> (if res literal (raise-clingo-error))))

  ;; Freeze the given solver literal.
  ;;
  ;; Any solver literal that is not frozen is subject to simplification and might be removed in a preprocessing step after propagator initialization.
  ;; A propagator should freeze all literals over which it might add clauses during propagation.
  ;; Note that any watched literal is automatically frozen and that it does not matter which phase of the literal is frozen.
  ;;
  ;; @param[in] init the target
  ;; @param[in] solver_literal the solver literal
  ;; @return whether the call was successful
  (define-clingo clingo-propagate-init-freeze-literal
    (_fun _clingo-propagate-init-pointer _clingo-literal -> (res : _stdbool) ->
          (if res (void) (raise-clingo-error)) ))
  ;; Remove the watch for the solver literal in the given phase.
  ;;
  ;; @param[in] init the target
  ;; @param[in] solver_literal the solver literal
  ;; @return whether the call was successful
  (define-clingo clingo-propagate-init-remove-watch
    (_fun _clingo-propagate-init-pointer _clingo-literal -> (res : _stdbool) ->
          (if res (void) (raise-clingo-error))))
  ;; Remove the watch for the solver literal in the given phase from the given solver thread.
  ;;
  ;; @param[in] init the target
  ;; @param[in] solver_literal the solver literal
  ;; @param[in] thread_id the id of the solver thread
  ;; @return whether the call was successful
  (define-clingo clingo-propagate-init-remove-watch-from-thread
    (_fun _clingo-propagate-init-pointer _clingo-literal _uint32 -> (res : _stdbool) ->
          (if res (void) (raise-clingo-error)) ))
  

  ;; Add the given weight constraint to the solver.
  ;;
  ;; This function adds a constraint of form `literal <=> { lit=weight | (lit, weight) in literals } >= bound` to the solver.
  ;; Depending on the type the `<=>` connective can be either a left implication, right implication, or equivalence.
  ;;
  ;; @attention No further calls on the init object or functions on the assignment should be called when the result of this method is false.
  ;;
  ;; @param[in] init the target
  ;; @param[in] literal the literal of the constraint
  ;; @param[in] literals the weighted literals
  ;; @param[in] size the number of weighted literals
  ;; @param[in] bound the bound of the constraint
  ;; @param[in] type the type of the weight constraint
  ;; @param[in] compare_equal if true compare equal instead of less than equal
  ;; @param[out] result result indicating whether the problem became unsatisfiable
  ;; @return whether the call was successful; might set one of the following error codes:
  ;; - ::clingo_error_bad_alloc
  (define-clingo clingo-propagate-init-add-weight-constraint
    (_fun _clingo-propagate-init-pointer _clingo-literal
          [ls : (_list i _clingo-weighted-literal)]
          [_size = (length ls)]
          _clingo-weight
          _clingo-weight-constraint-type
          _stdbool
          [result : (_ptr o _stdbool)] -> (res : _stdbool) ->
          (if res result (raise-clingo-error))))
  ;; Add the given literal to minimize to the solver.
  ;;
  ;; This corresponds to a weak constraint of form `:~ literal. [weight@priority]`.
  ;;
  ;; @param[in] init the target
  ;; @param[in] literal the literal to minimize
  ;; @param[in] weight the weight of the literal
  ;; @param[in] priority the priority of the literal
  ;; @return whether the call was successful; might set one of the following error codes:
  ;; - ::clingo_error_bad_alloc
  (define-clingo clingo-propagate-init-add-minimize
    (_fun _clingo-propagate-init-pointer _clingo-literal
          _clingo-weight
          _clingo-weight -> (res : _stdbool) ->
          (if res (void) (raise-clingo-error))))
  ;; Propagates consequences of the underlying problem excluding registered propagators.
  ;;
  ;; @note The function has no effect if SAT-preprocessing is enabled.
  ;; @attention No further calls on the init object or functions on the assignment should be called when the result of this method is false.
  ;;
  ;; @param[in] init the target
  ;; @param[out] result result indicating whether the problem became unsatisfiable
  ;; @return whether the call was successful; might set one of the following error codes:
  ;; - ::clingo_error_bad_alloc
  (define-clingo clingo-propagate-init-propagate
    (_fun _clingo-propagate-init-pointer [result : (_ptr o _stdbool)] -> (res : _stdbool) ->
          (if res result (raise-clingo-error)) ))
  ;; Add a literal to the solver.
  ;;
  ;; To be able to use the variable in clauses during propagation or add watches to it, it has to be frozen.
  ;; Otherwise, it might be removed during preprocessing.
  ;;
  ;; @attention If varibales were added, subsequent calls to functions adding constraints or ::clingo_propagate_init_propagate() are expensive.
  ;; It is best to add varables in batches.
  ;;
  ;; @param[in] init the target
  ;; @param[in] freeze whether to freeze the literal
  ;; @param[out] result the added literal
  ;; @return whether the call was successful; might set one of the following error codes:
  ;; - ::clingo_error_bad_alloc
  (define-clingo clingo-propagate-init-add-literal
    (_fun _clingo-propagate-init-pointer _stdbool [result : (_ptr o _clingo-literal)] -> (res : _stdbool) ->
          (if res result (raise-clingo-error)) ))

  ;; Add a numeric theory term.
  ;;
  ;; @param[in] backend the target backend
  ;; @param[in] number the value of the term
  ;; @param[out] term_id the resulting term id
  ;; @return whether the call was successful; might set one of the following error codes:
  ;; - ::clingo_error_bad_alloc
  (define-clingo clingo-backend-theory-term-number
    (_fun
     _clingo-backend-pointer _int
     [term-id : (_ptr o _clingo-id)] -> (res : _stdbool) ->
     (if res term-id (raise-clingo-error)) ))
  ;; Add a theory term representing a string.
  ;;
  ;; @param[in] backend the target backend
  ;; @param[in] string the value of the term
  ;; @param[out] term_id the resulting term id
  ;; @return whether the call was successful; might set one of the following error codes:
  ;; - ::clingo_error_bad_alloc
  (define-clingo clingo-backend-theory-term-string
    (_fun _clingo-backend-pointer _string
          [term-id : (_ptr o _clingo-id)] -> (res : _stdbool) ->
          (if res term-id (raise-clingo-error)) ))
  ;; Add a theory term representing a sequence of theory terms.
  ;;
  ;; @param[in] backend the target backend
  ;; @param[in] type the type of the sequence
  ;; @param[in] arguments the term ids of the terms in the sequence
  ;; @param[in] size the number of elements of the sequence
  ;; @param[out] term_id the resulting term id
  ;; @return whether the call was successful; might set one of the following error codes:
  ;; - ::clingo_error_bad_alloc
  (define-clingo clingo-backend-theory-term-sequence
    (_fun _clingo-backend-pointer _clingo-theory-sequence-type
          [ils : (_list i _clingo-id)]
          [_size = (length ils)]
          [term-id : (_ptr o _clingo-id)]  -> (res : _stdbool) ->
          (if res term-id (raise-clingo-error)) ))
  ;; Add a theory term representing a function.
  ;;
  ;; @param[in] backend the target backend
  ;; @param[in] name the name of the function
  ;; @param[in] arguments an array of term ids for the theory terms in the arguments
  ;; @param[in] size the number of arguments
  ;; @param[out] term_id the resulting term id
  ;; @return whether the call was successful; might set one of the following error codes:
  ;; - ::clingo_error_bad_alloc
  (define-clingo clingo-backend-theory-term-function
    (_fun _clingo-backend-pointer _string
          [arguments : (_list i _clingo-id)]
          [_size = (length arguments)]
          [term-id : (_ptr o _clingo-id)] -> (res : _stdbool) ->
          (if res term-id (raise-clingo-error)) ))
  ;; Convert the given symbol into a theory term.
  ;;
  ;; @param[in] backend the target backend
  ;; @param[in] symbol the symbol to convert
  ;; @param[out] term_id the resulting term id
  ;; @return whether the call was successful; might set one of the following error codes:
  ;; - ::clingo_error_bad_alloc
  (define-clingo clingo-backend-theory-term-symbol
    (_fun _clingo-backend-pointer _clingo-symbol
          [term-id : (_ptr o _clingo-id)] -> (res : _stdbool) ->
          (if res term-id (raise-clingo-error)) ))

  ;; Add a theory atom element.
  ;;
  ;; @param[in] backend the target backend
  ;; @param[in] tuple the array of term ids represeting the tuple
  ;; @param[in] tuple_size the size of the tuple
  ;; @param[in] condition an array of program literals represeting the condition
  ;; @param[in] condition_size the size of the condition
  ;; @param[out] element_id the resulting element id
  ;; @return whether the call was successful; might set one of the following error codes:
  ;; - ::clingo_error_bad_alloc
  (define-clingo clingo-backend-theory-element
    (_fun _clingo-backend-pointer
          [tuple : (_list i _clingo-id)] [_size = (length tuple)]
          [condition : (_list i _clingo-literal)]
          [_size = (length condition)]
          [element-id : (_ptr o _clingo-id)] -> (res : _stdbool) ->
          (if res element-id (raise-clingo-error)) ))
  ;; Add a theory atom without a guard.
  ;;
  ;; @param[in] backend the target backend
  ;; @param[in] atom_id_or_zero a program atom or zero for theory directives
  ;; @param[in] term_id the term id of the term associated with the theory atom
  ;; @param[in] elements an array of element ids for the theory atoms's elements
  ;; @param[in] size the number of elements
  ;; @return whether the call was successful; might set one of the following error codes:
  ;; - ::clingo_error_bad_alloc
  (define-clingo clingo-backend-theory-atom
    (_fun
     _clingo-backend-pointer
     _clingo-atom
     _clingo-id
     [elements : (_list i _clingo-id)]
     [_size = (length elements)] -> (res : _stdbool) ->
     (if res (void) (raise-clingo-error)) ))
  ;; Add a theory atom with a guard.
  ;;
  ;; @param[in] backend the target backend
  ;; @param[in] atom_id_or_zero a program atom or zero for theory directives
  ;; @param[in] term_id the term id of the term associated with the theory atom
  ;; @param[in] elements an array of element ids for the theory atoms's elements
  ;; @param[in] size the number of elements
  ;; @param[in] operator_name the string representation of a theory operator
  ;; @param[in] right_hand_side_id the term id of the right hand side term
  ;; @return whether the call was successful; might set one of the following error codes:
  ;; - ::clingo_error_bad_alloc
  (define-clingo clingo-backend-theory-atom-with-guard
    (_fun
     _clingo-backend-pointer
     _clingo-atom
     _clingo-id
     [elements : (_list i _clingo-id)]
     [_size = (length elements)]
     _string _clingo-id -> (res : _stdbool) ->
     (if res (void) (raise-clingo-error))))


  ;; When a problem is unsatisfiable, get a subset of the assumptions that made the problem unsatisfiable.
  ;;
  ;; If the program is not unsatisfiable, core is set to NULL and size to zero.
  ;;
  ;; @param[in] handle the target
  ;; @param[out] core pointer where to store the core
  ;; @param[out] size size of the given array
  ;; @return whether the call was successful; might set one of the following error codes:
  ;; - ::clingo_error_bad_alloc
  (define-clingo clingo-solve-handle-core-unsafe
    (_fun _clingo-solve-handle-pointer
          [core : (_ptr o _pointer)] ;; clingo_literal_t const **core,
          [size : (_ptr o _size)] -> (res : _stdbool) ->
          (if res (values core size) (raise-clingo-error)) )
    #:c-id clingo_solve_handle_core)
  (define (clingo-solve-handle-core solve-handle)
    (define-values (core size) (clingo-solve-handle-core-unsafe solve-handle))
    (cast core _pointer (_list o _clingo-literal size)))
  ;; Configure how learnt constraints are handled during enumeration.
  ;;
  ;; If the enumeration assumption is enabled, then all information learnt from
  ;; the solver's various enumeration modes is removed after a solve call. This
  ;; includes enumeration of cautious or brave consequences, enumeration of
  ;; answer sets with or without projection, or finding optimal models, as well
  ;; as clauses added with clingo_solve_control_add_clause().
  ;;
  ;; @attention For practical purposes, this option is only interesting for single-shot solving
  ;; or before the last solve call to squeeze out a tiny bit of performance.
  ;; Initially, the enumeration assumption is enabled.
  ;;
  ;; @param[in] control the target
  ;; @param[in] enable whether to enable the assumption
  ;; @return whether the call was successful
  (define-clingo clingo-control-set-enable-enumeration-assumption
    (_fun _clingo-control-pointer _stdbool -> (res : _stdbool) ->
          (if res (void) (raise-clingo-error))))
  ;; Check whether the enumeration assumption is enabled.
  ;;
  ;; See ::clingo_control_set_enable_enumeration_assumption().
  ;; @param[in] control the target
  ;; @return whether using the enumeration assumption is enabled
  (define-clingo clingo-control-get-enable-enumeration-assumption
    (_fun _clingo-control-pointer -> _stdbool))
  ;; Enable automatic cleanup after solving.
  ;;
  ;; @note Cleanup is enabled by default.
  ;;
  ;; @param[in] control the target
  ;; @param[in] enable whether to enable cleanups
  ;; @return whether the call was successful
  ;;
  ;; @see clingo_control_cleanup()
  ;; @see clingo_control_get_enable_cleanup()
  (define-clingo clingo-control-set-enable-cleanup
    (_fun _clingo-control-pointer _stdbool -> (res : _stdbool) ->
          (if res (void) (raise-clingo-error))))
  ;; Check whether automatic cleanup is enabled.
  ;;
  ;; See ::clingo_control_set_enable_cleanup().
  ;;
  ;; @param[in] control the target
  ;;
  ;; @see clingo_control_cleanup()
  ;; @see clingo_control_set_enable_cleanup()
  (define-clingo clingo-control-get-enable-cleanup
    (_fun _clingo-control-pointer -> _stdbool))
  ;; Add a custom scripting language to clingo.
  ;;
  ;; @param[in] name the name of the scripting language
  ;; @param[in] script struct with functions implementing the language
  ;; @param[in] data user data to pass to callbacks in the script
  ;; @return whether the call was successful
  (define-clingo clingo-register-script
    (_fun _string _clingo-script-pointer _pointer -> _stdbool))
  ;; Get the version of the registered scripting language.
  ;;
  ;; @param[in] name the name of the scripting language
  ;; @return the version
  (define-clingo clingo-get-script-version (_fun _string -> _string)
    #:c-id clingo_script_version)
  )
