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
(define *timeout* 3600)

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
     (tick)
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
       (tick)
       (apply fval vals))]
    [(list fun args ...)
     (let ([fval (eval fun env)]
           [vals (map (cut eval <> env) args)])
       (tick)
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
  (define fun_ (lambda xs (tick) (apply fun xs)))
  (apply r5rs:for-each (cons fun_ args)))

(define (our-map fun . args)
  (define fun_ (lambda xs (tick) (apply fun xs)))
  (apply r5rs:map (cons fun_ args)))

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
			 (new-binding 'acos acos)
       (new-binding 'arithmetic-shift arithmetic-shift)
       (new-binding 'append r5rs:append)
       (new-binding 'apply r5rs:apply)
			 (new-binding 'asin asin)
       (new-binding 'assoc r5rs:assoc)
       (new-binding 'assq r5rs:assq)
       (new-binding 'assv r5rs:assv)
       (new-binding 'atan atan)
       (new-binding 'boolean? boolean?)
       (new-binding 'call-with-input-file call-with-input-file)
       (new-binding 'call-with-output-file call-with-output-file)
			 (new-binding 'ceiling ceiling)
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
			 (new-binding 'complex? complex?)
       (new-binding 'cons r5rs:cons)
       (new-binding 'cos cos)
       (new-binding 'current-input-port current-input-port)
       (new-binding 'current-output-port current-output-port)
       (new-binding 'display r5rs:display)
       (new-binding 'eof-object? eof-object?)
       (new-binding 'eq? eq?)
       (new-binding 'equal? equal?)
       (new-binding 'eqv? eqv?)
       (new-binding 'error error)
       (new-binding 'even? even?)
			 (new-binding 'exact? exact?)
       (new-binding 'exact->inexact exact->inexact)
       (new-binding 'expt expt)
			 (new-binding 'exp exp)
			 (new-binding 'floor floor)
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
			 (new-binding 'inexact? inexact?)
       (new-binding 'inexact->exact inexact->exact)
			 (new-binding 'input-port? input-port?)
       (new-binding 'integer? integer?)
       (new-binding 'integer->char integer->char)
       (new-binding 'lcm lcm)
       (new-binding 'length r5rs:length)
       (new-binding 'list r5rs:list)
       (new-binding 'list? r5rs:list?)
       (new-binding 'list->vector r5rs:list->vector)
       (new-binding 'list-ref r5rs:list-ref)
			 (new-binding 'log log)
       (new-binding 'make-string make-string)
       (new-binding 'make-vector make-vector)
       (new-binding 'map our-map)
       (new-binding 'max max)
       (new-binding 'member r5rs:member)
       (new-binding 'memq r5rs:memq)
       (new-binding 'memv r5rs:memv)
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
			 (new-binding 'output-port? output-port?)
       (new-binding 'pair? r5rs:pair?)
       (new-binding 'pair r5rs:cons)
			 (new-binding 'peek-char peek-char)
       (new-binding 'port? port?)
       (new-binding 'positive? positive?)
       (new-binding 'procedure? procedure?)
       (new-binding 'print our-print)
       (new-binding 'printf printf)
       (new-binding 'quotient quotient)
			 (new-binding 'rational? rational?)
       (new-binding 'read r5rs:read)
       (new-binding 'read-char read-char)
       (new-binding 'read-line read-line)
			 (new-binding 'real? real?)
       (new-binding 'remainder remainder)
       (new-binding 'reverse r5rs:reverse)
       (new-binding 'round round)
       (new-binding 'set-car! r5rs:set-car!)
       (new-binding 'set-cdr! r5rs:set-cdr!)
       (new-binding 'sin sin)
       (new-binding 'sqrt sqrt)
			 (new-binding 'string string)
       (new-binding 'string-append string-append)
       (new-binding 'string? string?)
			 (new-binding 'string<=? string<=?)
			 (new-binding 'string<? string<?)
			 (new-binding 'string=? string=?)
			 (new-binding 'string>=? string>=?)
			 (new-binding 'string>? string>?)
			 (new-binding 'string-ci<=? string-ci<=?)
			 (new-binding 'string-ci<? string-ci<?)
			 (new-binding 'string-ci=? string-ci=?)
			 (new-binding 'string-ci>=? string-ci>=?)
			 (new-binding 'string-ci>? string-ci>?)
       (new-binding 'string-chop our-string-chop)
       (new-binding 'string->list r5rs:string->list)
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
			 (new-binding 'tan tan)
			 (new-binding 'truncate truncate)
       (new-binding 'vector->list r5rs:vector->list)
       (new-binding 'vector-length r5rs:vector-length)
       (new-binding 'vector-ref r5rs:vector-ref)
       (new-binding 'vector-resize our-vector-resize)
       (new-binding 'vector-set! r5rs:vector-set!)
       (new-binding 'vector r5rs:vector)
       (new-binding 'vector? r5rs:vector?)
       (new-binding 'void? void?)
       (new-binding 'void void)
       (new-binding 'with-input-from-file with-input-from-file)
       (new-binding 'with-output-to-file with-output-to-file)
       (new-binding 'write r5rs:write)
       (new-binding 'write-char write-char)
       (new-binding 'write-line our-write-line)
       (new-binding 'zero? zero?)

       (new-binding 'car r5rs:car)
       (new-binding 'cdr r5rs:cdr)
       (new-binding 'caar r5rs:caar)
       (new-binding 'cadr r5rs:cadr)
       (new-binding 'cdar r5rs:cdar)
       (new-binding 'cddr r5rs:cddr)
       (new-binding 'caaar r5rs:caaar)
       (new-binding 'caadr r5rs:caadr)
       (new-binding 'cadar r5rs:cadar)
       (new-binding 'caddr r5rs:caddr)
       (new-binding 'cdaar r5rs:cdaar)
       (new-binding 'cdadr r5rs:cdadr)
       (new-binding 'cddar r5rs:cddar)
       (new-binding 'cdddr r5rs:cdddr)
       (new-binding 'caaaar r5rs:caaaar)
       (new-binding 'caaadr r5rs:caaadr)
       (new-binding 'caadar r5rs:caadar)
       (new-binding 'caaddr r5rs:caaddr)
       (new-binding 'cadaar r5rs:cadaar)
       (new-binding 'cadadr r5rs:cadadr)
       (new-binding 'caddar r5rs:caddar)
       (new-binding 'cadddr r5rs:cadddr)
       (new-binding 'cdaaar r5rs:cdaaar)
       (new-binding 'cdaadr r5rs:cdaadr)
       (new-binding 'cdadar r5rs:cdadar)
       (new-binding 'cdaddr r5rs:cdaddr)
       (new-binding 'cddaar r5rs:cddaar)
       (new-binding 'cddadr r5rs:cddadr)
       (new-binding 'cdddar r5rs:cdddar)
       (new-binding 'cddddr r5rs:cddddr)
       ))

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
