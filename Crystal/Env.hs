module Crystal.Env where

import qualified Data.Map as M

import Crystal.AST
import Crystal.Tuple
import Crystal.Type

import Data.Monoid

type Env = M.Map Ident TypedLabel

-- TODO: Factor in effects of functions passed to higher-order primitives
-- TODO: Support for floats
main_env :: Env
main_env = M.fromListWith or [
    "="             --> makeNumericVarFun "="  TBool,
    "+"             --> makeNumericVarFun "+"  TInt,
    "*"             --> makeNumericVarFun "*"  TInt,
    "-"             --> makeNumericVarFun "-"  TInt,
    "/"             --> makeNumericVarFun "/"  TInt,
    "<"             --> makeNumericVarFun "<"  TBool,
    ">"             --> makeNumericVarFun ">"  TBool,
    ">="            --> makeNumericVarFun ">=" TBool,
    "<="            --> makeNumericVarFun "<=" TBool,
    "abs"           --> TFun [1..1] emptyEffect . require [(TInt,1)] TInt,
    "append"        --> TFun [1..2] emptyEffect . require [(TPair,1), (TPair,2)] TPair,
    "apply"         --> TFun [1..2] emptyEffect . require [] TAny, -- todo function
    "assoc"         --> TFun [1..2] emptyEffect . require [(TPair,2)] (Tor [TPair, TBool]),
    "assq"          --> TFun [1..2] emptyEffect . require [(TPair,2)] (Tor [TPair, TBool]),
    "assv"          --> TFun [1..2] emptyEffect . require [(TPair,2)] (Tor [TPair, TBool]),
    "atan"          --> TFun [1..2] emptyEffect . require [(TInt,1), (TInt,2)] TInt,
    "boolean?"      --> TFun [1..1] emptyEffect . require [] TBool,
    "car"           --> TFun [1..1] emptyEffect . require [(TPair,1)] TAny,
    "cdr"           --> TFun [1..1] emptyEffect . require [(TPair,1)] TAny,
    "char?"         --> TFun [1..1] emptyEffect . require [] TBool,
    "char->integer" --> TFun [1..1] emptyEffect . require [(TChar, 1)] TInt,
    "char-alphabetic?" --> TFun [1..1] emptyEffect . require [(TChar,1)] TBool,
    "char-downcase" --> TFun [1..1] emptyEffect . require [(TChar,1)] TChar,
    "char-lower-case?" --> TFun [1..1] emptyEffect . require [(TChar,1)] TBool,
    "char-numeric?" --> TFun [1..1] emptyEffect . require [(TChar,1)] TBool,
    "char-upcase"   --> TFun [1..1] emptyEffect . require [(TChar,1)] TChar,
    "char-upper-case?" --> TFun [1..1] emptyEffect . require [(TChar,1)] TBool,
    "char-whitespace?" --> TFun [1..1] emptyEffect . require [(TChar,1)] TBool,
    "char-ci<=?"    --> TFun [1..2] emptyEffect . require [(TChar,1),(TChar,2)] TBool,
    "char-ci<?"     --> TFun [1..2] emptyEffect . require [(TChar,1),(TChar,2)] TBool,
    "char-ci=?"     --> TFun [1..2] emptyEffect . require [(TChar,1),(TChar,2)] TBool,
    "char-ci>=?"    --> TFun [1..2] emptyEffect . require [(TChar,1),(TChar,2)] TBool,
    "char-ci>?"     --> TFun [1..2] emptyEffect . require [(TChar,1),(TChar,2)] TBool,
    "char<=?"       --> TFun [1..2] emptyEffect . require [(TChar,1),(TChar,2)] TBool,
    "char<?"        --> TFun [1..2] emptyEffect . require [(TChar,1),(TChar,2)] TBool,
    "char=?"        --> TFun [1..2] emptyEffect . require [(TChar,1),(TChar,2)] TBool,
    "char>=?"       --> TFun [1..2] emptyEffect . require [(TChar,1),(TChar,2)] TBool,
    "char>?"        --> TFun [1..2] emptyEffect . require [(TChar,1),(TChar,2)] TBool,
    "char?"         --> TFun [1..1] emptyEffect . require [] TBool,
    "cons"          --> TFun [1..2] emptyEffect . require [] TPair,
    "cos"           --> TFun [1..1] emptyEffect . require [(TInt,1)] TInt,
    "current-input-port" --> TFun [1..1] emptyEffect . require [] TPort,
    "current-output-port" --> TFun [1..1] emptyEffect . require [] TPort,
    "display"       --> TFun [1..1] emptyEffect . require [] TVoid,
    "eof-object?"   --> TFun [1..1] emptyEffect . require [] TBool,
    "eq?"           --> TFun [1..2] emptyEffect . require [] TBool,
    "equal?"        --> TFun [1..2] emptyEffect . require [] TBool,
    "eqv?"          --> TFun [1..2] emptyEffect . require [] TBool,
    "error"         --> TFun [1..1] emptyEffect . require [(TString,1)] TAny,
    "even?"         --> TFun [1..1] emptyEffect . require [] TBool,
    "exact->inexact"--> TFun [1..1] emptyEffect . require [(TInt,1)] TInt,
    "expt"          --> TFun [1..2] emptyEffect . require [(TInt,1), (TInt,2)] TInt,
    "for-each"      --> TFun [1..2] emptyEffect . require [(TFun [3] emptyEffect TAny,1), (TPair,2)] TVoid,
    "format"        --> makeVarFun "format" (\args -> require [] TString),
    "fp="           --> makeNumericVarFun "="  TBool,
    "fp+"           --> makeNumericVarFun "+"  TInt,
    "fp*"           --> makeNumericVarFun "*"  TInt,
    "fp-"           --> makeNumericVarFun "-"  TInt,
    "fp/"           --> makeNumericVarFun "/"  TInt,
    "fp<"           --> makeNumericVarFun "<"  TBool,
    "fp>"           --> makeNumericVarFun ">"  TBool,
    "fp>="          --> makeNumericVarFun ">=" TBool,
    "fp<="          --> makeNumericVarFun "<=" TBool,
    "fx="           --> makeNumericVarFun "="  TBool,
    "fx+"           --> makeNumericVarFun "+"  TInt,
    "fx*"           --> makeNumericVarFun "*"  TInt,
    "fx-"           --> makeNumericVarFun "-"  TInt,
    "fx/"           --> makeNumericVarFun "/"  TInt,
    "fx<"           --> makeNumericVarFun "<"  TBool,
    "fx>"           --> makeNumericVarFun ">"  TBool,
    "fx>="          --> makeNumericVarFun ">=" TBool,
    "fx<="          --> makeNumericVarFun "<=" TBool,
    "fxmin"         --> TFun [1..2] emptyEffect . require [(TInt,1), (TInt,2)] TInt,
    "fxmod"         --> TFun [1..2] emptyEffect . require [(TInt,1), (TInt,2)] TInt,
    "gcd"           --> TFun [1..2] emptyEffect . require [(TInt,1), (TInt,2)] TInt,
    "gensym"        --> TFun []     emptyEffect . require [] TSymbol,
    "inexact->exact"--> TFun [1..1] emptyEffect . require [(TInt,1)] TInt,
    "integer?"      --> TFun [1..1] emptyEffect . require [] TBool,
    "integer->char" --> TFun [1..1] emptyEffect . require [(TInt,1)] TChar,
    "lcm"           --> TFun [1..2] emptyEffect . require [(TInt,1), (TInt,2)] TInt,
    "length"        --> TFun [1..1] emptyEffect . require [(TPair,1)] TInt,
    "list"          --> makeVarFun "list" (\args -> require [] (if null args then TNull else TPair)),
    "list->vector"  --> TFun [1..1] emptyEffect . require [(TPair,1)] TVec,
    "list-ref"      --> TFun [1..2] emptyEffect . require [(TPair,1), (TInt,2)] TAny,
    "make-string"   --> TFun [1..1] emptyEffect . require [(TInt,1)] TString,
    "make-vector"   --> TFun [1..1] emptyEffect . require [(TInt,1)] TVec,
    "make-vector"   --> TFun [1..2] emptyEffect . require [(TInt,1)] TVec,
    "map"           --> TFun [1..2] emptyEffect . require [(TFun [3] emptyEffect TAny,1), (TPair,2)] TPair,
    "max"           --> TFun [1..2] emptyEffect . require [(TInt,1), (TInt,2)] TBool,
    "member"        --> TFun [1..2] emptyEffect . require [(TPair, 2)] (Tor [TPair, TBool]),
    "memq"          --> TFun [1..2] emptyEffect . require [(TPair, 2)] (Tor [TPair, TBool]),
    "memv"          --> TFun [1..2] emptyEffect . require [(TPair, 2)] (Tor [TPair, TBool]),
    "min"           --> TFun [1..2] emptyEffect . require [(TInt,1), (TInt,2)] TBool,
    "modulo"        --> TFun [1..2] emptyEffect . require [(TInt,1), (TInt,2)] TInt,
    "negative?"     --> TFun [1..1] emptyEffect . require [] TBool,
    "newline"       --> TFun []     emptyEffect . require [] TVoid,
    "not"           --> TFun [1..1] emptyEffect . require [] TBool,
    "null?"         --> TFun [1..1] emptyEffect . require [] TBool,
    "number?"       --> TFun [1..1] emptyEffect . require [] TBool,
    "number->string"--> TFun [1..1] emptyEffect . require [(TInt,1)] TString,
    "odd?"          --> TFun [1..1] emptyEffect . require [] TBool,
    "pair?"         --> TFun [1..1] emptyEffect . require [] TBool,
    "port?"         --> TFun [1..1] emptyEffect . require [] TBool,
    "positive?"     --> TFun [1..1] emptyEffect . require [] TBool,
    "procedure?"    --> TFun [1..1] emptyEffect . require [] TBool,
    "print"        --> makeVarFun "print" (\args -> require [] TVoid),
    "printf"        --> makeVarFun "printf" (\args -> require [] TVoid),
    "quotient"      --> TFun [1..2] emptyEffect . require [(TInt,1), (TInt,2)] TInt,
    "read"          --> TFun []     emptyEffect . require [] TAny,
    "read-char"     --> TFun [1..1] emptyEffect . require [(TPort, 1)] TChar,
    "read-line"     --> TFun [1..1] emptyEffect . require [(TPort, 1)] TString,
    "remainder"     --> TFun [1..2] emptyEffect . require [(TInt,1), (TInt,2)] TInt,
    "reverse"       --> TFun [1..1] emptyEffect . require [(TPair,1)] TPair,
    "round"         --> TFun [1..1] emptyEffect . require [(TInt,1)] TInt,
    "set-car!"      --> TFun [1..2] emptyEffect . require [(TPair, 1)] TVoid,
    "set-cdr!"      --> TFun [1..2] emptyEffect . require [(TPair, 1)] TVoid,
    "sin"           --> TFun [1..1] emptyEffect . require [(TInt,1)] TInt,
    "sqrt"          --> TFun [1..1] emptyEffect . require [(TInt,1)] TInt,
    "string-append" --> TFun [1..2] emptyEffect . require [(TString,1), (TString,2)] TString,
    "string?"       --> TFun [1..1] emptyEffect . require [] TBool,
    "string=?"      --> TFun [1..2] emptyEffect . require [(TString,1), (TString,2)] TBool,
    "string-chop"   --> TFun [1..2] emptyEffect . require [(TString,1), (TInt, 2)] TPair,
    "string->number"--> TFun [1..1] emptyEffect . require [(TString,1)] TInt,
    "string-downcase"--> TFun [1..1] emptyEffect . require [(TString,1)] TString,
    "string-downcase!" --> TFun [1..1] emptyEffect . require [(TString,1)] TVoid,
    "string-length" --> TFun [1..1] emptyEffect . require [(TString,1)] TInt,
    "string-ref"    --> TFun [1..2] emptyEffect . require [(TString,1), (TInt, 2)] TChar,
    "string-reverse" --> TFun [1..1] emptyEffect . require [(TString,1)] TString,
    "string-set!"   --> TFun [1..3] emptyEffect . require [(TString,1), (TInt, 2), (TChar, 3)] TVoid,
    "string-upcase" --> TFun [1..1] emptyEffect . require [(TString,1)] TString,
    "string-upcase!"--> TFun [1..1] emptyEffect . require [(TString,1)] TVoid,
    "substring"     --> TFun [1..3] emptyEffect . require [(TString,1), (TInt, 2), (TInt, 3)] TString,
    "symbol?"       --> TFun [1..1] emptyEffect . require [] TBool,
    "symbol->string"--> TFun [1..1] emptyEffect . require [(TSymbol,1)] TString,
    "time"          --> TFun [1..1] emptyEffect . require [] TAny,
    "vector->list"  --> TFun [1..1] emptyEffect . require [(TVec,1)] TPair,
    "vector-length" --> TFun [1..1] emptyEffect . require [(TVec,1)] TInt,
    "vector-ref"    --> TFun [1..2] emptyEffect . require [(TVec,1), (TInt,2)] TAny,
    "vector-resize" --> TFun [1..3] emptyEffect . require [(TVec,1), (TInt,2)] TVec,
    "vector-set!"   --> TFun [1..3] emptyEffect . require [(TVec,1), (TInt,2)] TVoid,
    "vector"        --> makeVarFun "vector" (\args -> require [] TVec),
    "vector?"       --> TFun [1..1] emptyEffect . require [] TBool,
    "void?"         --> TFun [1..1] emptyEffect . require [] TBool,
    "with-input-from-file" --> TFun [1..2] emptyEffect . require [(TString,1)] TVoid,
    "with-output-to-file"  --> TFun [1..2] emptyEffect . require [(TString,1)] TVoid,
    "write"         --> TFun [1..1] emptyEffect . require [(TString,1)] TVoid,
    "write-char"    --> TFun [1..1] emptyEffect . require [(TChar,1)] TVoid,
    "write-line"    --> TFun [1..1] emptyEffect . require [(TString,1)] TVoid,
    "zero?"         --> TFun [1..1] emptyEffect . require [] TBool
  ] where (-->) nam fun = (nam, LPrim nam :*: fun (LPrim nam) :*: emptyEffect)
          infix 5 -->
          require tests return blame       = foldr f return tests
            where f (prim, cause) return = TIf (blame, LVar cause) prim (TVar cause) return
          requireVF tests return blame     = foldr f return tests
            where f (prim, cause :*: typ) return = TIf (blame, cause) prim typ return
          makeVarFun name vf blame         = TVarFun (VarFun name blame vf)
          makeNumericVarFun name ret blame = TVarFun (VarFun name blame (\args blame -> requireVF [ (TInt, a) | a <- args ] ret blame))
          (LPrim nam :*: fun1 :*: ef1) `or` (LPrim _ :*: fun2 :*: ef2) = LPrim nam :*: Tor [fun1, fun2] :*: ef1 `mappend` ef2


extend :: Ident -> TypedLabel -> Env -> Env
extend = M.insert
