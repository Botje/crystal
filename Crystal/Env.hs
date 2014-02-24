module Crystal.Env where

import qualified Data.Map as M

import Crystal.AST
import Crystal.Tuple
import Crystal.Type

type Env = M.Map Ident TypedLabel

main_env :: Env
main_env = M.fromListWith or [
    "="             --> TFun [1..2] . require [(TInt,1), (TInt,2)] TBool,
    "+"             --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "*"             --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "-"             --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "/"             --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "<"             --> TFun [1..2] . require [(TInt,1), (TInt,2)] TBool,
    ">"             --> TFun [1..2] . require [(TInt,1), (TInt,2)] TBool,
    ">="            --> TFun [1..2] . require [(TInt,1), (TInt,2)] TBool,
    "<="            --> TFun [1..2] . require [(TInt,1), (TInt,2)] TBool,
    "append"        --> TFun [1..2] . require [(TPair,1), (TPair,2)] TPair,
    "apply"         --> TFun [1..2] . require [] TAny, -- todo function
    "assoc"         --> TFun [1..2] . require [(TPair,2)] (Tor [TPair, TBool]),
    "assq"          --> TFun [1..2] . require [(TPair,2)] (Tor [TPair, TBool]),
    "assv"          --> TFun [1..2] . require [(TPair,2)] (Tor [TPair, TBool]),
    "atan"          --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "boolean?"      --> TFun [1..1] . require [] TBool,
    "car"           --> TFun [1..1] . require [(TPair,1)] TAny,
    "cdr"           --> TFun [1..1] . require [(TPair,1)] TAny,
    "char?"         --> TFun [1..1] . require [] TBool,
    "char->integer" --> TFun [1..1] . require [(TChar, 1)] TInt,
    "char-alphabetic?" --> TFun [1..1] . require [(TChar,1)] TBool,
    "char-downcase" --> TFun [1..1] . require [(TChar,1)] TChar,
    "char-lower-case?" --> TFun [1..1] . require [(TChar,1)] TBool,
    "char-numeric?" --> TFun [1..1] . require [(TChar,1)] TBool,
    "char-upcase"   --> TFun [1..1] . require [(TChar,1)] TChar,
    "char-upper-case?" --> TFun [1..1] . require [(TChar,1)] TBool,
    "char-whitespace?" --> TFun [1..1] . require [(TChar,1)] TBool,
    "char-ci<=?"    --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char-ci<?"     --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char-ci=?"     --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char-ci>=?"    --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char-ci>?"     --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char<=?"       --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char<?"        --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char=?"        --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char>=?"       --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char>?"        --> TFun [1..2] . require [(TChar,1),(TChar,2)] TBool,
    "char?"         --> TFun [1..1] . require [] TBool,
    "cons"          --> TFun [1..2] . require [] TPair,
    "cos"           --> TFun [1..1] . require [(TInt,1)] TInt,
    "display"       --> TFun [1..1] . require [(TString,1)] TAny,
    "eq?"           --> TFun [1..2] . require [] TBool,
    "equal?"        --> TFun [1..2] . require [] TBool,
    "eqv?"          --> TFun [1..2] . require [] TBool,
    "error"         --> TFun [1..1] . require [(TString,1)] TAny,
    "even?"         --> TFun [1..1] . require [] TBool,
    "expt"          --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "for-each"      --> TFun [1..2] . require [(TFun [3] TAny,1), (TPair,2)] TVoid,
    "gcd"           --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "gensym"        --> TFun []     . require [] TSymbol,
    "lcm"           --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "length"        --> TFun [1..1] . require [(TPair,1)] TInt,
    "list"          --> makeVarFun "list" (\args -> require [] (if null args then TNull else TPair)),
    "list->vector"  --> TFun [1..1] . require [(TPair,1)] TVec,
    "make-vector"   --> TFun [1..1] . require [(TInt,1)] TVec,
    "make-vector"   --> TFun [1..2] . require [(TInt,1)] TVec,
    "map"           --> TFun [1..2] . require [(TFun [3] TAny,1), (TPair,2)] TPair,
    "max"           --> TFun [1..2] . require [(TInt,1), (TInt,2)] TBool,
    "member"        --> TFun [1..2] . require [(TPair, 2)] (Tor [TPair, TBool]),
    "memq"          --> TFun [1..2] . require [(TPair, 2)] (Tor [TPair, TBool]),
    "memv"          --> TFun [1..2] . require [(TPair, 2)] (Tor [TPair, TBool]),
    "min"           --> TFun [1..2] . require [(TInt,1), (TInt,2)] TBool,
    "modulo"        --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "negative?"     --> TFun [1..1] . require [] TBool,
    "newline"       --> TFun []     . require [] TVoid,
    "not"           --> TFun [1..1] . require [] TBool,
    "null?"         --> TFun [1..1] . require [] TBool,
    "number?"       --> TFun [1..1] . require [] TBool,
    "odd?"          --> TFun [1..1] . require [] TBool,
    "pair?"         --> TFun [1..1] . require [] TBool,
    "port?"         --> TFun [1..1] . require [] TBool,
    "positive?"     --> TFun [1..1] . require [] TBool,
    "procedure?"    --> TFun [1..1] . require [] TBool,
    "quotient"      --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "read"          --> TFun []     . require [] TAny,
    "remainder"     --> TFun [1..2] . require [(TInt,1), (TInt,2)] TInt,
    "reverse"       --> TFun [1..1] . require [(TPair,1)] TPair,
    "set!"          --> TFun [1..1] . require [] TVoid,
    "set-car!"      --> TFun [1..2] . require [(TPair, 1)] TVoid,
    "set-cdr!"      --> TFun [1..2] . require [(TPair, 1)] TVoid,
    "sin"           --> TFun [1..1] . require [(TInt,1)] TInt,
    "string-append" --> TFun [1..2] . require [(TString,1), (TString,2)] TString,
    "string?"       --> TFun [1..1] . require [] TBool,
    "symbol?"       --> TFun [1..1] . require [] TBool,
    "symbol->string"--> TFun [1..1] . require [(TSymbol,1)] TString,
    "time"          --> TFun [1..1] . require [] TAny,
    "vector->list"  --> TFun [1..1] . require [(TVec,1)] TPair,
    "vector-length" --> TFun [1..1] . require [(TVec,1)] TInt,
    "vector-ref"    --> TFun [1..2] . require [(TVec,1), (TInt,2)] (TAny),
    "vector-set!"   --> TFun [1..3] . require [(TVec,1), (TInt,2)] (TVar 3),
    "vector"        --> makeVarFun "vector" (\args -> require [] TVec),
    "vector?"       --> TFun [1..1] . require [] TBool,
    "void?"         --> TFun [1..1] . require [] TBool,
    "write"         --> TFun [1..1] . require [(TString,1)] TAny,
    "zero?"         --> TFun [1..1] . require [] TBool
  ] where (-->) nam fun = (nam, LPrim nam :*: fun (LPrim nam))
          infix 5 -->
          require tests return blame = foldr (f blame) return tests
          f blame (prim, cause) return = TIf (blame, LVar cause) prim (TVar cause) return
          makeVarFun name vf blame = TVarFun (VarFun name blame vf)
          (LPrim nam :*: fun1) `or` (LPrim _ :*: fun2) = LPrim nam :*: Tor [fun1, fun2]


extend :: Ident -> TypedLabel -> Env -> Env
extend = M.insert
