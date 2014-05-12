#lang racket/base

(require racket/cmdline)
(require racket/function)
(require racket/match)
(require racket/set)
(require srfi/26)

(define *global-env* '())

(define *evaluating-predicate* (make-parameter #f))
(define *counting-distance* (make-parameter #t))
(define *tick-count* 0)
(define (tick)
  (unless (*evaluating-predicate*)
    (set! *tick-count* (+ *tick-count* 1))))

(define *check-count* 0)
(define *counting-checks* (make-parameter #f))
(define *report-timings* (make-parameter #f))

(struct binding 
  (name
   (value #:mutable)
   def-time
   (check-time #:auto #:mutable)
   (check-labs #:auto #:mutable)
   (use-time   #:auto #:mutable))
  #:auto-value #f)

(define (new-binding name value)
  (binding name value *tick-count*))

(define (assocm var env)
  (if (null? env)
      #f
      (if (eq? var (binding-name (car env)))
          (car env)
          (assocm var (cdr env)))))

(define (lookup-variable var env)
  (let ((x (assocm var env)))
    (if x
        (binding-value x)
        (error "Could not look up" var))))

(define (eval-set! var val env)
  (let ((cell (assocm var env)))
    (if cell
        (begin (set-binding-value! cell val) val)
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
         [frame (map new-binding nams vals)])
    (eval-begin body (append frame env))))

(define (eval-let* binds body env)
  (match binds
    ['() (eval-begin body env)]
    [(list (list nam exp ...) binds ...)
     (let* ([val (eval-begin exp env)]
            [frame (new-binding nam val)])
       (eval-let* binds body (cons frame env)))]))

(define (eval-letrec binds body env)
  (let* ([nams (map car binds)]
         [exps (map cdr binds)]
         [env  (append (map (cut new-binding <> #f) nams) env)])
    (for ([nam (in-list nams)]
          [exp (in-list exps)])
      (let ([cell (assocm nam env)])
        (set-binding-value! cell (eval-begin exp env))))
    (eval-begin body env)))

(define (improper-bind vars rest real-args)
  (if (null? vars)
      (list (new-binding rest real-args))
      (cons (new-binding (car vars) (car real-args))
            (improper-bind (cdr vars) rest (cdr real-args)))))

(define (eval-lambda args bod real-args env)
  (match args
    [(list vars ...) 
     (unless (= (length real-args) (length vars))
       (apply (curry raise-arity-error 'lambda (length vars)) real-args))
     (eval-begin bod (append (map new-binding vars real-args) env))]
    [(list-rest vars ... rest)
     (unless (>= (length real-args) (length vars))
       (apply (curry raise-arity-error 'lambda (make-arity-at-least (length vars))) real-args))
     (eval-begin bod (append (improper-bind vars rest real-args) env))]
    [any
     (eval-begin bod (cons (new-binding any real-args) env))]))

(define (eval-predicate pred env)
  (match pred
    [(list 'or preds ...)
     (for/or ([p preds])
       (eval-predicate p env))]
    [(list 'and preds ...)
     (for/and ([p preds])
       (eval-predicate p env))]
    [(list fun var labels ...)
     (when (symbol? var)
       (let ((cell (assocm var env)))
         (if cell 
           (begin
             (set-binding-check-labs! cell
                                      (set-union
                                       (or (binding-check-labs cell) (set))
                                       (apply set labels)))
             (set-binding-check-time! cell *tick-count*)
             (eval `(,fun ,var) env))
             (error "Unknown binding: " var))))]))


(define (report-tick-for lab env vars)
  (when (*counting-distance*)
    (for ([var (in-list vars)]
          #:when (symbol? var)
          [cell (in-value (assocm var env))]
          #:when cell
          [labs (in-value (binding-check-labs cell))]
          #:when (set? labs))
      (set-binding-use-time! cell *tick-count*)
      (let ([def (binding-def-time cell)]
            [check (binding-check-time cell)]
            [use (binding-use-time cell)]) 
      (eprintf "~a ~a ~a~%" var (- use def) (- check def))))))

(define (eval exp env)
  (when (pair? exp) (tick))
  (match exp
    [(list 'quote exp) exp]
    [(list 'if cond cons)
     (if (eval cond env) (eval cons env) (void))]
    [(list 'if cond cons alt)
     (if (eval cond env) (eval cons env) (eval alt env))]
    [(list 'let bnds bod ..1)
     (eval-let bnds bod env)]
    [(list 'let* bnds bod ..1)
     (eval-let* bnds bod env)]
    [(list 'letrec bnds bod ..1)
     (eval-letrec bnds bod env)]
    [(list 'lambda args bod ..1)
     (lambda real-args
       (eval-lambda args bod real-args env))]
    [(list 'check pred bod)
     (parameterize [(*evaluating-predicate* #t)]
       (when (*counting-checks*)
         (set! *check-count* (+ *check-count* 1)))
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
     (report-tick-for lab env (cons fun args))
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

(define (our-print . args)
  (for-each display args))

(define (our-format print? fmt . args)
  (set! fmt (regexp-replace* #rx"~,?[0-9][Ff]" fmt "~A"))
  (set! fmt (regexp-replace* #rx"~[Ff]" fmt "~A"))
  (set! fmt (regexp-replace* #rx"~[Dd]" fmt "~A"))
  (define str (apply (curry format fmt) args))
  (if print?
      (write-string str)
      str))

(define (our-for-each fun . args)
  (define fun_ (lambda xs (tick) (apply fun xs)))
  (apply for-each (cons fun_ args)))

(define (our-map fun . args)
  (define fun_ (lambda xs (tick) (apply fun xs)))
  (apply map (cons fun_ args)))

(define (our-1+ x) (+ x 1))
(define (our-1- x) (- x 1))

(set! *global-env*
      (list
       (new-binding '1+ our-1+)
       (new-binding '1- our-1-)
       (new-binding '= =)
       (new-binding '+ +)
       (new-binding '* *)
       (new-binding '- -)
       (new-binding '/ /)
       (new-binding '< <)
       (new-binding '> >)
       (new-binding '>= >=)
       (new-binding '<= <=)
       (new-binding 'abs abs)
       (new-binding 'arithmetic-shift arithmetic-shift)
       (new-binding 'append append)
       (new-binding 'apply apply)
       (new-binding 'assoc assoc)
       (new-binding 'assq assq)
       (new-binding 'assv assv)
       (new-binding 'atan atan)
       (new-binding 'boolean? boolean?)
       (new-binding 'car car)
       (new-binding 'call-with-input-file call-with-input-file)
       (new-binding 'call-with-output-file call-with-output-file)
       (new-binding 'cdr cdr)
       (new-binding 'char? char?)
       (new-binding 'char->integer char->integer)
       (new-binding 'char-alphabetic? char-alphabetic?)
       (new-binding 'char-downcase char-downcase)
       (new-binding 'char-lower-case? char-lower-case?)
       (new-binding 'char-numeric? char-numeric?)
       (new-binding 'char-upcase char-upcase)
       (new-binding 'char-upper-case? char-upper-case?)
       (new-binding 'char-whitespace? char-whitespace?)
       (new-binding 'char-ci<=? char-ci<=?)
       (new-binding 'char-ci<? char-ci<?)
       (new-binding 'char-ci=? char-ci=?)
       (new-binding 'char-ci>=? char-ci>=?)
       (new-binding 'char-ci>? char-ci>?)
       (new-binding 'char<=? char<=?)
       (new-binding 'char<? char<?)
       (new-binding 'char=? char=?)
       (new-binding 'char>=? char>=?)
       (new-binding 'char>? char>?)
       (new-binding 'char? char?)
       (new-binding 'close-input-port close-input-port)
       (new-binding 'close-output-port close-output-port)
       (new-binding 'cons cons)
       (new-binding 'cos cos)
       (new-binding 'current-input-port current-input-port)
       (new-binding 'current-output-port current-output-port)
       (new-binding 'display display)
       (new-binding 'eof-object? eof-object?)
       (new-binding 'eq? eq?)
       (new-binding 'equal? equal?)
       (new-binding 'eqv? eqv?)
       (new-binding 'error error)
       (new-binding 'even? even?)
       (new-binding 'exact->inexact exact->inexact)
       (new-binding 'expt expt)
       (new-binding 'for-each our-for-each)
       (new-binding 'format our-format)
       (new-binding 'fp= =)
       (new-binding 'fp+ +)
       (new-binding 'fp* *)
       (new-binding 'fp- -)
       (new-binding 'fp/ /)
       (new-binding 'fp< <)
       (new-binding 'fp> >)
       (new-binding 'fp>= >=)
       (new-binding 'fp<= <=)
       (new-binding 'fx= =)
       (new-binding 'fx+ +)
       (new-binding 'fx* *)
       (new-binding 'fx- -)
       (new-binding 'fx/ /)
       (new-binding 'fx< <)
       (new-binding 'fx> >)
       (new-binding 'fx>= >=)
       (new-binding 'fx<= <=)
       (new-binding 'fxmin min)
       (new-binding 'fxmod modulo)
       (new-binding 'gcd gcd)
       (new-binding 'gensym gensym)
       (new-binding 'inexact->exact inexact->exact)
       (new-binding 'integer? integer?)
       (new-binding 'integer->char integer->char)
       (new-binding 'lcm lcm)
       (new-binding 'length length)
       (new-binding 'list list)
       (new-binding 'list? list?)
       (new-binding 'list->vector list->vector)
       (new-binding 'list-ref list-ref)
       (new-binding 'make-string make-string)
       (new-binding 'make-vector make-vector)
       (new-binding 'make-vector make-vector)
       (new-binding 'map our-map)
       (new-binding 'max max)
       (new-binding 'member member)
       (new-binding 'memq memq)
       (new-binding 'memv memv)
       (new-binding 'min min)
       (new-binding 'modulo modulo)
       (new-binding 'negative? negative?)
       (new-binding 'newline newline)
       (new-binding 'not not)
       (new-binding 'null? null?)
       (new-binding 'number? number?)
       (new-binding 'number->string number->string)
       (new-binding 'odd? odd?)
       (new-binding 'open-input-file open-input-file)
       (new-binding 'open-output-file open-output-file)
       (new-binding 'pair? pair?)
       (new-binding 'port? port?)
       (new-binding 'positive? positive?)
       (new-binding 'procedure? procedure?)
       (new-binding 'print our-print)
       (new-binding 'printf printf)
       (new-binding 'quotient quotient)
       (new-binding 'read read)
       (new-binding 'read-char read-char)
       (new-binding 'read-line read-line)
       (new-binding 'remainder remainder)
       (new-binding 'reverse reverse)
       (new-binding 'round round)
       ;(new-binding 'set-car! set-car!)
       ;(new-binding 'set-cdr! set-cdr!)
       (new-binding 'sin sin)
       (new-binding 'sqrt sqrt)
       (new-binding 'string-append string-append)
       (new-binding 'string? string?)
       (new-binding 'string=? string=?)
       (new-binding 'string-chop our-string-chop)
       (new-binding 'string->list string->list)
       (new-binding 'string->number string->number)
       (new-binding 'string->symbol string->symbol)
       (new-binding 'string-downcase string-downcase)
       ;(new-binding 'string-downcase! string-downcase!)
       (new-binding 'string-length string-length)
       (new-binding 'string-ref string-ref)
       (new-binding 'string-reverse our-string-reverse)
       (new-binding 'string-set! string-set!)
       (new-binding 'string-upcase string-upcase)
       ;(new-binding 'string-upcase! string-upcase!)
       (new-binding 'substring substring)
       (new-binding 'symbol? symbol?)
       (new-binding 'symbol->string symbol->string)
       (new-binding 'vector->list vector->list)
       (new-binding 'vector-length vector-length)
       (new-binding 'vector-ref vector-ref)
       (new-binding 'vector-resize our-vector-resize)
       (new-binding 'vector-set! vector-set!)
       (new-binding 'vector vector)
       (new-binding 'vector? vector?)
       (new-binding 'void? void?)
       (new-binding 'void void)
       (new-binding 'with-input-from-file with-input-from-file)
       (new-binding 'with-output-to-file with-output-to-file)
       (new-binding 'write write)
       (new-binding 'write-char write-char)
       (new-binding 'write-line our-write-line)
       (new-binding 'zero? zero?)
       ))

(define (start-eval exp)
  (call-with-values
    (thunk (time-apply eval (list exp *global-env*)))
    (lambda (ret cpu real gc)
      (when (*counting-checks*)
        (eprintf "~a\t" *check-count*))
      (when (*report-timings*)
        (eprintf "~a\t" cpu))
      (eprintf "~%"))))


(define (read-code l)
  (if (null? l)
    (read)
    (with-input-from-file (car l) (thunk (read)))))

(provide main)
(define (main . args)
  (command-line
    #:program "eval"
    #:once-each
    [("-t" "--timings") "Report timings" (*report-timings* #t)]
    [("-c" "--count-checks") "Report number of checks made" (*counting-checks* #t) (*counting-distance* #f)]
    #:args args
    (start-eval (read-code args))))
