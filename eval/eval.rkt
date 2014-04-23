#lang racket

(require racket/match)
(require srfi/26)

(define *global-env* '())

(define *evaluating-predicate* (make-parameter #f))

(define (assocm var env)
  (if (null? env)
      env
      (if (eq? var (mcar (car env)))
          (car env)
          (assocm var (cdr env)))))

(define (lookup-variable var env)
  (let ((x (assocm var env)))
    (if x
        (mcdr x)
        (error "Could not look up" var))))

(define (eval-set! var val env)
  (let ((cell (assocm var env)))
    (if cell
        (begin (set-mcdr! cell val) val)
        (error "Could not look up" var))))

(define (eval-begin stmts env)
  (if (null? (cdr stmts))
      (eval (car stmts) env)
      (begin (eval (car stmts) env)
             (eval-begin (cdr stmts) env))))

(define (eval-let binds body env)
  (let* ([nams (map car binds)]
         [exps (map cdr binds)]
         [vals (map (cut eval-begin <> env) exps)]
         [frame (map mcons nams vals)])
    (eval-begin body (append frame env))))

(define (eval-letrec binds body env)
  (let* ([nams (map car binds)]
         [exps (map cdr binds)]
         [vals (map (cut eval-begin <> env) exps)]
         [frame (map mcons nams vals)])
    (set! env (append frame env))
    (eval-begin body env)))

(define (improper-bind vars rest real-args)
  (if (null? vars)
      (list (mcons rest real-args))
      (cons (mcons (car vars) (car real-args))
            (improper-bind (cdr vars) rest (cdr real-args)))))

(define (eval-lambda args bod real-args env)
  (match args
    [(list vars ...) 
     (unless (= (length real-args) (length vars))
       (apply (curry raise-arity-error 'lambda (length vars)) real-args))
     (eval-begin bod (append (map mcons vars real-args) env))]
    [(list-rest vars ... rest)
     (unless (>= (length real-args) (length vars))
       (apply (curry raise-arity-error 'lambda (make-arity-at-least (length vars))) real-args))
     (eval-begin bod (append (improper-bind vars rest real-args) env))]
    [any
     (eval-begin bod (cons (mcons any real-args) env))]))

(define (eval-predicate pred env)
  (match pred
    [(list 'or preds ...)
     (for/or ([p preds])
       (eval-predicate p env))]
    [(list 'and preds ...)
     (for/and ([p preds])
       (eval-predicate p env))]
    [(list fun ref labels ...)
     (eval `(,fun ,ref) env)]))

(define *tick-count* 0)
(define (tick)
  (unless (*evaluating-predicate*)
    (set! *tick-count* (+ *tick-count* 1))))

(define (report-tick-for lab)
  'todo)

(define (eval exp env)
  (when (pair? exp) (tick))
  (match exp
    [(list 'quote exp) exp]
    [(list 'if cond cons alt)
     (if (eval cond env) (eval cons env) (eval alt env))]
    [(list 'let bnds bod ..1)
     (eval-let bnds bod env)]
    [(list 'letrec bnds bod ..1)
     (eval-letrec bnds bod env)]
    [(list 'lambda args bod ..1)
     (lambda real-args
       (eval-lambda args bod real-args env))]
    [(list 'check pred bod)
     (parameterize [(*evaluating-predicate* #t)]
       (unless (eval-predicate pred env)
         (error "Check failed" pred)))
     (eval bod env)]
    [(list 'time exps ...)
     (eval-begin exps env)]
    [(list 'set! var exp)
     (eval-set! var (eval exp env) env)]
    [(list 'begin)
     (void)]
    [(list 'begin exp)
     (eval exp env)]
    [(list 'begin exp exps ...)
     (eval exp env)
     (eval `(begin ,@exps) env)]
    [(list '@ lab fun args ...)
     (report-tick-for lab)
     (let ([fval (eval fun env)]
           [vals (map (cut eval <> env) args)])
       (apply fval vals))]
    [(list fun args ...)
     (let ([fval (eval fun env)]
           [vals (map (cut eval <> env) args)])
       (apply fval vals))]
    [(? symbol? var) (lookup-variable var env)]
    [self-evaluating self-evaluating]
    [unknown (error "Cannot evaluate " unknown)]))

(define (our-string-chop str len)
  (for/list ([idx (in-range 0 (string-length str) len)])
    (substring str idx (min (string-length str) (+ idx len)))))

(define (our-string-reverse str)
  (list->string (reverse (string->list str))))

(define (our-vector-resize orig n [init (void)])
  (let ([ret (make-vector n init)])
    (for ([(el i) (in-indexed (in-vector orig))])
      (vector-set! ret i el))
    ret))

(define (our-write-line str [port (current-output-port)])
  (write-string str port)
  (newline port))


(set! *global-env*
      (list
       (mcons '= =)
       (mcons '+ +)
       (mcons '* *)
       (mcons '- -)
       (mcons '/ /)
       (mcons '< <)
       (mcons '> >)
       (mcons '>= >=)
       (mcons '<= <=)
       (mcons 'abs abs)
       (mcons 'append append)
       (mcons 'apply apply)
       (mcons 'assoc assoc)
       (mcons 'assq assq)
       (mcons 'assv assv)
       (mcons 'atan atan)
       (mcons 'boolean? boolean?)
       (mcons 'car car)
       (mcons 'cdr cdr)
       (mcons 'char? char?)
       (mcons 'char->integer char->integer)
       (mcons 'char-alphabetic? char-alphabetic?)
       (mcons 'char-downcase char-downcase)
       (mcons 'char-lower-case? char-lower-case?)
       (mcons 'char-numeric? char-numeric?)
       (mcons 'char-upcase char-upcase)
       (mcons 'char-upper-case? char-upper-case?)
       (mcons 'char-whitespace? char-whitespace?)
       (mcons 'char-ci<=? char-ci<=?)
       (mcons 'char-ci<? char-ci<?)
       (mcons 'char-ci=? char-ci=?)
       (mcons 'char-ci>=? char-ci>=?)
       (mcons 'char-ci>? char-ci>?)
       (mcons 'char<=? char<=?)
       (mcons 'char<? char<?)
       (mcons 'char=? char=?)
       (mcons 'char>=? char>=?)
       (mcons 'char>? char>?)
       (mcons 'char? char?)
       (mcons 'cons cons)
       (mcons 'cos cos)
       (mcons 'current-input-port current-input-port)
       (mcons 'current-output-port current-output-port)
       (mcons 'display display)
       (mcons 'eof-object? eof-object?)
       (mcons 'eq? eq?)
       (mcons 'equal? equal?)
       (mcons 'eqv? eqv?)
       (mcons 'error error)
       (mcons 'even? even?)
       (mcons 'exact->inexact exact->inexact)
       (mcons 'expt expt)
       (mcons 'for-each for-each)
       (mcons 'format format)
       (mcons 'fp= =)
       (mcons 'fp+ +)
       (mcons 'fp* *)
       (mcons 'fp- -)
       (mcons 'fp/ /)
       (mcons 'fp< <)
       (mcons 'fp> >)
       (mcons 'fp>= >=)
       (mcons 'fp<= <=)
       (mcons 'fx= =)
       (mcons 'fx+ +)
       (mcons 'fx* *)
       (mcons 'fx- -)
       (mcons 'fx/ /)
       (mcons 'fx< <)
       (mcons 'fx> >)
       (mcons 'fx>= >=)
       (mcons 'fx<= <=)
       (mcons 'fxmin min)
       (mcons 'fxmod modulo)
       (mcons 'gcd gcd)
       (mcons 'gensym gensym)
       (mcons 'inexact->exact inexact->exact)
       (mcons 'integer? integer?)
       (mcons 'integer->char integer->char)
       (mcons 'lcm lcm)
       (mcons 'length length)
       (mcons 'list list)
       (mcons 'list->vector list->vector)
       (mcons 'list-ref list-ref)
       (mcons 'make-string make-string)
       (mcons 'make-vector make-vector)
       (mcons 'make-vector make-vector)
       (mcons 'map map)
       (mcons 'max max)
       (mcons 'member member)
       (mcons 'memq memq)
       (mcons 'memv memv)
       (mcons 'min min)
       (mcons 'modulo modulo)
       (mcons 'negative? negative?)
       (mcons 'newline newline)
       (mcons 'not not)
       (mcons 'null? null?)
       (mcons 'number? number?)
       (mcons 'number->string number->string)
       (mcons 'odd? odd?)
       (mcons 'pair? pair?)
       (mcons 'port? port?)
       (mcons 'positive? positive?)
       (mcons 'procedure? procedure?)
       (mcons 'print print)
       (mcons 'printf printf)
       (mcons 'quotient quotient)
       (mcons 'read read)
       (mcons 'read-char read-char)
       (mcons 'read-line read-line)
       (mcons 'remainder remainder)
       (mcons 'reverse reverse)
       (mcons 'round round)
       ;(mcons 'set-car! set-car!)
       ;(mcons 'set-cdr! set-cdr!)
       (mcons 'sin sin)
       (mcons 'sqrt sqrt)
       (mcons 'string-append string-append)
       (mcons 'string? string?)
       (mcons 'string=? string=?)
       (mcons 'string-chop our-string-chop)
       (mcons 'string->number string->number)
       (mcons 'string-downcase string-downcase)
       ;(mcons 'string-downcase! string-downcase!)
       (mcons 'string-length string-length)
       (mcons 'string-ref string-ref)
       (mcons 'string-reverse our-string-reverse)
       ;(mcons 'string-set! string-set!)
       (mcons 'string-upcase string-upcase)
       ;(mcons 'string-upcase! string-upcase!)
       (mcons 'substring substring)
       (mcons 'symbol? symbol?)
       (mcons 'symbol->string symbol->string)
       (mcons 'vector->list vector->list)
       (mcons 'vector-length vector-length)
       (mcons 'vector-ref vector-ref)
       (mcons 'vector-resize our-vector-resize)
       (mcons 'vector-set! vector-set!)
       (mcons 'vector vector)
       (mcons 'vector? vector?)
       (mcons 'void? void?)
       (mcons 'write write)
       (mcons 'write-char write-char)
       (mcons 'write-line our-write-line)
       (mcons 'zero? zero?)
       ))

(define (start-eval exp)
  (eval exp *global-env*))

(define (main . args)
  (match args
    [(list filename)
     (with-input-from-file filename
       (thunk (start-eval (read))))]
    ['() (start-eval (read))]))