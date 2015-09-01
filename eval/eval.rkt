#lang racket/base

(require racket/cmdline)
(require racket/function)
(require racket/list)
(require racket/match)
(require racket/set)
(require srfi/26)
(require compatibility/mlist)

(require (prefix-in r5rs: r5rs))

(define *global-env* '())
(define *timeout*
	(let ([timeout-env (getenv "TIMEOUT")])
		(if timeout-env
			(string->number timeout-env)
			3600)))

(define *evaluating-predicate* (make-parameter #f))
(define *counting-distance* (make-parameter #f))
(define *current-function* (make-parameter "main"))
(define *tick-count* 0)
(define (tick)
  (unless (*evaluating-predicate*)
    (set! *tick-count* (+ *tick-count* 1))))

(define *check-count* 0)
(define *enable-checks* (make-parameter #t))
(define *counting-checks* (make-parameter #f))
(define *report-timings* (make-parameter #f))
(define *report-time-to-fail* (make-parameter #f))

(struct binding 
  (name
   (value #:mutable)
   def-time
   function
   (check-time #:auto #:mutable)
   (check-labs #:auto #:mutable)
   (use-time   #:auto #:mutable))
  #:auto-value #f)

(define (new-binding name value)
  (binding name value *tick-count* (*current-function*)))

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

(define (extract-names stmts nams)
  (match (car stmts)
    [(list 'define (list nam args ...) bod ..1)
     (extract-names (cdr stmts) (cons nam nams))]
    [(list 'define nam _)
     (extract-names (cdr stmts) (cons nam nams))]
    [_ (reverse nams)]))

(define (eval-begin-defines stmts env)
  (let ([names (extract-names stmts '())])
    (set! env (append (map (lambda (name) (new-binding name #f)) names) env))
    (for ([nam (in-list names)]
          [stmt (in-list stmts)])
       (let ((cell (assocm nam env)))
         (match stmt
           [(list 'define (list nam args ...) bod ..1)
            (set-binding-value! cell (create-named-function nam args bod env))]
           [(list 'define nam val)
            (set-binding-value! cell (eval val env))])))
    (eval (last stmts) env)))

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
        (match exp
          [(list (and l (list 'lambda args bod ...)))
           (set-binding-value! cell
             (create-named-function nam args bod env))]
          [_ 
           (set-binding-value! cell
            (eval-begin exp env))])))
    (eval-begin body env)))

(define (improper-bind vars rest real-args)
  (if (null? vars)
      (list (new-binding rest (list->mlist real-args)))
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
     (eval-begin bod (cons (new-binding any (list->mlist real-args)) env))]))

(define (find-vars-in-pred pred)
  (match pred
    [(list 'or preds ...)
     (flatten (map find-vars-in-pred preds))]
    [(list 'and preds ...)
     (flatten (map find-vars-in-pred preds))]
    [(list fun var labels ...)
     (list var)]))

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
      (let ([fun (binding-function cell)]
            [def (binding-def-time cell)]
            [check (binding-check-time cell)]
            [use (binding-use-time cell)]) 
      (eprintf "~a ~a ~a ~a~%" fun var (- use def) (- check def))))))

(define (to-mutable v)
    (cond
     [(pair? v) (mcons (to-mutable (car v))
                       (to-mutable (cdr v)))]
     [(vector? v) (list->vector
                   (map to-mutable (vector->list v)))]
     [else v]))

(define (create-named-function function-name args bod env)
  (lambda real-args
              (eval-lambda args bod real-args env)))

(define (eval exp env)
  (match exp
    [(list 'quote exp) (to-mutable exp)]
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
     (define function-name (gensym))
     (create-named-function function-name args bod env)]
    [(list 'check pred exps ..1)
     (parameterize [(*evaluating-predicate* #t)]
       (when (*counting-checks*)
         (set! *check-count* (+ *check-count* 1)))
       (when (and (*enable-checks*) (not (eval-predicate pred env)))
         (let* ([vars (find-vars-in-pred pred)]
                [pairs (foldr (lambda (var rest) (append (list (symbol->string var) (lookup-variable var env)) rest)) '() vars)])
           (apply raise-arguments-error 'check  (format "Check failed: ~a" pred) pairs))))
     (eval-begin exps env)]
    [(list 'time exps ...)
     (eval-begin exps env)]
    [(list 'set! var exp)
     (eval-set! var (eval exp env) env)]
    [(list 'begin)
     (void)]
    [(list 'begin exps ..1)
     (eval-begin exps env)]
    [(list 'begin-defines exps ..1)
     (eval-begin-defines exps env)]
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
  (for-each r5rs:display args))

(define (our-format print? fmt . args)
  (set! fmt (regexp-replace* #rx"~,?[0-9][Ff]" fmt "~A"))
  (set! fmt (regexp-replace* #rx"~[Ff]" fmt "~A"))
  (set! fmt (regexp-replace* #rx"~[Dd]" fmt "~A"))
  (define str (apply (curry format fmt) args))
  (if print?
      (write-string str)
      str))

(define (our-for-each fun . args)
  (apply r5rs:for-each (cons fun args)))

(define (our-map fun . args)
  (apply r5rs:map (cons fun args)))

(define (our-1+ x) (+ x 1))
(define (our-1- x) (- x 1))

(set! *global-env*
	(map
		(lambda (p) (new-binding (car p)
		                         (lambda args (tick) (apply (cdr p) args))))
      (list
       (cons '1+ our-1+)
       (cons '1- our-1-)
       (cons '= =)
       (cons '+ +)
       (cons '* *)
       (cons '- -)
       (cons '/ /)
       (cons '< <)
       (cons '> >)
       (cons '>= >=)
       (cons '<= <=)
       (cons 'abs abs)
			 (cons 'acos acos)
       (cons 'arithmetic-shift arithmetic-shift)
       (cons 'append r5rs:append)
       (cons 'apply r5rs:apply)
			 (cons 'asin asin)
       (cons 'assoc r5rs:assoc)
       (cons 'assq r5rs:assq)
       (cons 'assv r5rs:assv)
       (cons 'atan atan)
       (cons 'boolean? boolean?)
       (cons 'call-with-input-file call-with-input-file)
       (cons 'call-with-output-file call-with-output-file)
			 (cons 'ceiling ceiling)
       (cons 'char? char?)
       (cons 'char->integer char->integer)
       (cons 'char-alphabetic? char-alphabetic?)
       (cons 'char-downcase char-downcase)
       (cons 'char-lower-case? char-lower-case?)
       (cons 'char-numeric? char-numeric?)
       (cons 'char-upcase char-upcase)
       (cons 'char-upper-case? char-upper-case?)
       (cons 'char-whitespace? char-whitespace?)
       (cons 'char-ci<=? char-ci<=?)
       (cons 'char-ci<? char-ci<?)
       (cons 'char-ci=? char-ci=?)
       (cons 'char-ci>=? char-ci>=?)
       (cons 'char-ci>? char-ci>?)
       (cons 'char<=? char<=?)
       (cons 'char<? char<?)
       (cons 'char=? char=?)
       (cons 'char>=? char>=?)
       (cons 'char>? char>?)
       (cons 'char? char?)
       (cons 'close-input-port close-input-port)
       (cons 'close-output-port close-output-port)
			 (cons 'complex? complex?)
       (cons 'cons r5rs:cons)
       (cons 'cos cos)
       (cons 'current-input-port current-input-port)
       (cons 'current-output-port current-output-port)
       (cons 'display r5rs:display)
       (cons 'eof-object? eof-object?)
       (cons 'eq? eq?)
       (cons 'equal? equal?)
       (cons 'eqv? eqv?)
       (cons 'error error)
       (cons 'even? even?)
			 (cons 'exact? exact?)
       (cons 'exact->inexact exact->inexact)
       (cons 'expt expt)
			 (cons 'exp exp)
			 (cons 'floor floor)
       (cons 'for-each our-for-each)
       (cons 'format our-format)
       (cons 'fp= =)
       (cons 'fp+ +)
       (cons 'fp* *)
       (cons 'fp- -)
       (cons 'fp/ /)
       (cons 'fp< <)
       (cons 'fp> >)
       (cons 'fp>= >=)
       (cons 'fp<= <=)
       (cons 'fx= =)
       (cons 'fx+ +)
       (cons 'fx* *)
       (cons 'fx- -)
       (cons 'fx/ /)
       (cons 'fx< <)
       (cons 'fx> >)
       (cons 'fx>= >=)
       (cons 'fx<= <=)
       (cons 'fxmin min)
       (cons 'fxmod modulo)
       (cons 'gcd gcd)
       (cons 'gensym gensym)
			 (cons 'inexact? inexact?)
       (cons 'inexact->exact inexact->exact)
			 (cons 'input-port? input-port?)
       (cons 'integer? integer?)
       (cons 'integer->char integer->char)
       (cons 'lcm lcm)
       (cons 'length r5rs:length)
       (cons 'list r5rs:list)
       (cons 'list? r5rs:list?)
       (cons 'list->vector r5rs:list->vector)
       (cons 'list-ref r5rs:list-ref)
			 (cons 'log log)
       (cons 'make-string make-string)
       (cons 'make-vector make-vector)
       (cons 'map our-map)
       (cons 'max max)
       (cons 'member r5rs:member)
       (cons 'memq r5rs:memq)
       (cons 'memv r5rs:memv)
       (cons 'min min)
       (cons 'modulo modulo)
       (cons 'negative? negative?)
       (cons 'newline newline)
       (cons 'not not)
       (cons 'null? null?)
       (cons 'number? number?)
       (cons 'number->string number->string)
       (cons 'odd? odd?)
       (cons 'open-input-file open-input-file)
       (cons 'open-output-file open-output-file)
			 (cons 'output-port? output-port?)
       (cons 'pair? r5rs:pair?)
       (cons 'pair r5rs:cons)
			 (cons 'peek-char peek-char)
       (cons 'port? port?)
       (cons 'positive? positive?)
       (cons 'procedure? procedure?)
       (cons 'print our-print)
       (cons 'printf printf)
       (cons 'quotient quotient)
			 (cons 'rational? rational?)
       (cons 'read r5rs:read)
       (cons 'read-char read-char)
       (cons 'read-line read-line)
			 (cons 'real? real?)
       (cons 'remainder remainder)
       (cons 'reverse r5rs:reverse)
       (cons 'round round)
       (cons 'set-car! r5rs:set-car!)
       (cons 'set-cdr! r5rs:set-cdr!)
       (cons 'sin sin)
       (cons 'sqrt sqrt)
			 (cons 'string string)
       (cons 'string-append string-append)
       (cons 'string? string?)
			 (cons 'string<=? string<=?)
			 (cons 'string<? string<?)
			 (cons 'string=? string=?)
			 (cons 'string>=? string>=?)
			 (cons 'string>? string>?)
			 (cons 'string-ci<=? string-ci<=?)
			 (cons 'string-ci<? string-ci<?)
			 (cons 'string-ci=? string-ci=?)
			 (cons 'string-ci>=? string-ci>=?)
			 (cons 'string-ci>? string-ci>?)
       (cons 'string-chop our-string-chop)
       (cons 'string->list r5rs:string->list)
       (cons 'string->number string->number)
       (cons 'string->symbol string->symbol)
       (cons 'string-downcase string-downcase)
       ;(cons 'string-downcase! string-downcase!)
       (cons 'string-length string-length)
       (cons 'string-ref string-ref)
       (cons 'string-reverse our-string-reverse)
       (cons 'string-set! string-set!)
       (cons 'string-upcase string-upcase)
       ;(cons 'string-upcase! string-upcase!)
       (cons 'substring substring)
       (cons 'symbol? symbol?)
       (cons 'symbol->string symbol->string)
			 (cons 'tan tan)
			 (cons 'truncate truncate)
       (cons 'vector->list r5rs:vector->list)
       (cons 'vector-length r5rs:vector-length)
       (cons 'vector-ref r5rs:vector-ref)
       (cons 'vector-resize our-vector-resize)
       (cons 'vector-set! r5rs:vector-set!)
       (cons 'vector r5rs:vector)
       (cons 'vector? r5rs:vector?)
       (cons 'void? void?)
       (cons 'void void)
       (cons 'with-input-from-file with-input-from-file)
       (cons 'with-output-to-file with-output-to-file)
       (cons 'write r5rs:write)
       (cons 'write-char write-char)
       (cons 'write-line our-write-line)
       (cons 'zero? zero?)

       (cons 'car r5rs:car)
       (cons 'cdr r5rs:cdr)
       (cons 'caar r5rs:caar)
       (cons 'cadr r5rs:cadr)
       (cons 'cdar r5rs:cdar)
       (cons 'cddr r5rs:cddr)
       (cons 'caaar r5rs:caaar)
       (cons 'caadr r5rs:caadr)
       (cons 'cadar r5rs:cadar)
       (cons 'caddr r5rs:caddr)
       (cons 'cdaar r5rs:cdaar)
       (cons 'cdadr r5rs:cdadr)
       (cons 'cddar r5rs:cddar)
       (cons 'cdddr r5rs:cdddr)
       (cons 'caaaar r5rs:caaaar)
       (cons 'caaadr r5rs:caaadr)
       (cons 'caadar r5rs:caadar)
       (cons 'caaddr r5rs:caaddr)
       (cons 'cadaar r5rs:cadaar)
       (cons 'cadadr r5rs:cadadr)
       (cons 'caddar r5rs:caddar)
       (cons 'cadddr r5rs:cadddr)
       (cons 'cdaaar r5rs:cdaaar)
       (cons 'cdaadr r5rs:cdaadr)
       (cons 'cdadar r5rs:cdadar)
       (cons 'cdaddr r5rs:cdaddr)
       (cons 'cddaar r5rs:cddaar)
       (cons 'cddadr r5rs:cddadr)
       (cons 'cdddar r5rs:cdddar)
       (cons 'cddddr r5rs:cddddr)
       )))

(define (start-eval exp)
  (define main-thread (current-thread))
  (thread (thunk (sleep *timeout*) (eprintf "TIMEOUT\tDNF~%") (kill-thread main-thread)))
  (call-with-exception-handler
    (lambda (v)
      (when (*report-time-to-fail*)
        (eprintf "ERROR\t~a~%" *tick-count*))
      v)
    (thunk
      (call-with-values
        (thunk (time-apply eval (list `(begin-defines ,@exp) *global-env*)))
        (lambda (ret cpu real gc)
          (when (*report-time-to-fail*)
            (eprintf "SUCCESS\t~a~%" *tick-count*))
          (when (*counting-checks*)
            (eprintf "~a\t" *check-count*))
          (when (*report-timings*)
            (eprintf "~a\t" cpu))
          (when (or (*counting-checks*) (*report-timings*))
            (eprintf "~%")))))))


(define (read-code)
  (let ([x (read)])
    (if (eof-object? x)
      '()
      (cons x (read-code)))))

(provide main)
(define (main . args)
  (command-line
    #:program "eval"
    #:once-each
    [("-f" "--time-to-fail") "Report time to fail (implies \"Count checks\")" (*counting-checks* #t) (*report-time-to-fail* #t)]
    [("-t" "--timings") "Report timings" (*report-timings* #t)]
    [("-c" "--count-checks") "Report number of checks made" (*counting-checks* #t)]
    [("-d" "--count-distance") "Report define--check and check--use distance" (*counting-distance* #t)]
    [("--nc") "Disable checks" (*enable-checks* #f)]
    #:args l
    (start-eval (if (null? l) (read-code) (with-input-from-file (car l) (thunk (read-code)))))))
