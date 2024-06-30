type varName = string 
type value = N of int | B of bool | Pair of value*value | VClos of varName*(opcode list)*(environment) 
and environment = ((varName*value) list)
and opcode = 
  LOOKUP of varName
| LOAD of value 
| MKCLOS of varName*(opcode list)
| IFTPLE of (opcode list)*(opcode list)
| APP 
| RET 

| ADD 
| SUB 
| MUL 
| DIV 
| MOD 
| EXP 

| GRTR 
| GRTREQ 
| LSR 
| LSREQ 
| EQUAL 

| AND 
| OR 
| NOT 

| FIRST 
| SECOND 
| MKPAIR

type expr = 
| V of value 
| Var of varName 

| Add of expr*expr 
| Sub of expr*expr 
| Mul of expr*expr 
| Div of expr*expr 
| Mod of expr*expr 
| Exp of expr*expr 

| Grtr of expr*expr 
| Lsr of expr*expr
| Equal of expr*expr 
| GrtrEq of expr*expr 
| LsrEq of expr*expr

| And of expr*expr 
| Or of expr*expr 
| Not of expr 

| Abs of varName*expr 
| App of expr*expr 

| Let of varName*expr*expr 
| SeqLet of ((varName*expr) list)*expr

| MkPair of expr*expr 
| First of expr 
| Second of expr 
| Tuple of expr list

| IfThEl of expr*expr*expr

| Case of expr*((expr*expr) list)*(expr) (*In the case statement first expression is what we will run the selection on
                                          additionaly the last expression is the default case which is made necessary here 
                                          eventhough it may be unused in some pieces of code*)
exception InvalidTupleExpression
(*choose variable name not allowed in language like !*)
let rec transCaseStmntHelper vName caseList defaultCaseExpr = match caseList with 
| (val1Exp,exp1):: rem -> IfThEl(Equal(Var vName,transpile val1Exp),transpile exp1,transCaseStmntHelper vName rem defaultCaseExpr)
| [] -> transpile defaultCaseExpr
and transCaseStmnt inputExpr caseList defaultCaseExpr =  
  let tempVarName = "!" in 
    let tempExpr = Let(tempVarName,transpile inputExpr,transCaseStmntHelper tempVarName caseList defaultCaseExpr) in 
      transpile tempExpr
and transpileTuple tupleBody = match tupleBody with 
| exp1::[] -> exp1 
| exp1::rem -> MkPair(exp1,transpileTuple rem)
| [] -> raise InvalidTupleExpression
and transpileSeqLeft defList innerExpr = match defList with 
| []  -> innerExpr
| (vName,exp)::rem -> Let(vName,exp,transpileSeqLeft rem innerExpr) 
and transpile e = match e with 
| Let (vName,exp1,exp2) -> App(Abs(vName,transpile exp2),transpile exp1)
| SeqLet (defList,innerExp) -> transpile (transpileSeqLeft defList innerExp) 
| Case (inputExpr,caseList,defaultCaseExpr) -> transCaseStmnt inputExpr caseList defaultCaseExpr
| Abs(vName,exp2) -> Abs(vName,transpile exp2)
| App(exp1,exp2) -> App(transpile exp1,transpile exp2)
| Add(exp1,exp2) -> Add(transpile exp1,transpile exp2)
| Sub(exp1,exp2) -> Sub(transpile exp1,transpile exp2)
| Mul(exp1,exp2) -> Mul(transpile exp1,transpile exp2)
| Div(exp1,exp2) -> Div(transpile exp1,transpile exp2)
| Mod(exp1,exp2) -> Mod(transpile exp1,transpile exp2)
| Exp(exp1,exp2) -> Exp(transpile exp1,transpile exp2)

| IfThEl(exp1,exp2,exp3) -> IfThEl(transpile exp1,transpile exp2,transpile exp3)
| First(exp1) -> First(transpile exp1)
| Second(exp1) -> Second(transpile exp1)
| MkPair(exp1,exp2) -> MkPair(transpile exp1,transpile exp2)
| Tuple(exprList) -> transpileTuple exprList 

| And(exp1,exp2) -> And(transpile exp1,transpile exp2)
| Or(exp1,exp2) -> Or(transpile exp1,transpile exp2)
| Not(exp1) -> Not(transpile exp1)

| Grtr(exp1,exp2) -> Grtr(transpile exp1,transpile exp2)
| Lsr(exp1,exp2) -> Lsr(transpile exp1,transpile exp2)
| Equal(exp1,exp2) -> Equal(transpile exp1,transpile exp2)
| GrtrEq(exp1,exp2) -> GrtrEq(transpile exp1,transpile exp2)
| LsrEq(exp1,exp2) -> LsrEq(transpile exp1,transpile exp2)

| V v -> V v 
| Var vName -> Var vName

exception TranspileExprFirst of string*expr

let rec compile e = match e with 
| V v -> [LOAD v]
| Var x -> [LOOKUP x]
| Add(e1,e2) -> (compile e1)@(compile e2)@[ADD]
| Sub(e1,e2) -> (compile e1)@(compile e2)@[SUB]
| Mul(e1,e2) -> (compile e1)@(compile e2)@[MUL]
| Div(e1,e2) -> (compile e1)@(compile e2)@[DIV]
| Mod(e1,e2) -> (compile e1)@(compile e2)@[MOD]
| Exp(e1,e2) -> (compile e1)@(compile e2)@[EXP]

| Grtr(e1,e2) -> (compile e1)@(compile e2)@[GRTR]
| Lsr(e1,e2) -> (compile e1)@(compile e2)@[LSR]
| Equal(e1,e2) -> (compile e1)@(compile e2)@[EQUAL]
| GrtrEq(e1,e2) -> (compile e1)@(compile e2)@[GRTREQ]
| LsrEq(e1,e2) -> (compile e1)@(compile e2)@[LSREQ]

| And(e1,e2) -> (compile e1)@(compile e2)@[AND]
| Or(e1,e2) -> (compile e1)@(compile e2)@[OR]
| Not(e1) -> (compile e1)@[NOT]

| Abs(vName,e1) -> [MKCLOS (vName,(compile e1)@[RET])]
| App(e1,e2) -> (compile e1)@(compile e2)@[APP]

| Let (vName,exp1,exp2) -> raise (TranspileExprFirst ("Must transpile code beofre passing to the compiler let expression not allowed",e))
| Case (inputExpr,caseList,defaultCaseExpr) -> raise (TranspileExprFirst ("Must transpile code before passing to the compiler Case statement not allowed",e))
| Tuple (exprList) -> raise(TranspileExprFirst ("Must transpile code before passing to compiler Typle statement not allowed",e))
| SeqLet (defList,innerExp) -> raise(TranspileExprFirst ("Must transpile code before passing to compiler SeqLet statement not allowed",e))

| First(e) -> (compile e)@[FIRST]
| Second(e) -> (compile e)@[SECOND]
| MkPair(e1,e2) -> (compile e1)@(compile e2)@[MKPAIR]

| IfThEl(e1,e2,e3) -> (compile e1)@[IFTPLE((compile e2)@[RET],(compile e3)@[RET])]


exception InvalidTypesForOpr
type stack = value list 
type environment = (varName*value) list
type code = opcode list 
type dump = (stack*environment*code) list
exception InvalidSECDstate of stack*environment*code*dump
exception ZeroPowerZero
let intFunc val1 val2 opr = match val1,val2 with 
| N n1,N n2 -> N (opr n1 n2)
| _,_ -> raise InvalidTypesForOpr
let boolFunc val1 val2 opr = match val1,val2 with 
| B b1,B b2 -> B(opr b1 b2) 
| _,_ -> raise InvalidTypesForOpr
let int2BoolFunc val1 val2 opr = match val1,val2 with 
| N n1,N n2 -> B(opr n1 n2)
| _,_ -> raise InvalidTypesForOpr
let mul val1 val2 = val1*val2
let rec exp num pow = match pow with 
| 0 -> if num=0 then raise ZeroPowerZero else 1
| x -> let temp = exp num (pow/2) in 
          if pow mod 2 == 0 then 
            temp*temp else temp*temp*num
let addVarValPair lst var value = (var,value)::lst
exception VariableNotInEnvironment of string
let rec lookup varName arr = match arr with 
| [] -> raise (VariableNotInEnvironment varName)
| (vName,value)::rem -> if varName = vName then value else lookup varName rem

let rec printValue v = match v with 
| N n -> Printf.printf "Result is: %d" n 
| B b -> Printf.printf "Result is: %b" b 
| VClos (x,y,z) -> Printf.printf "Result was a function cannot easily print to console"
| Pair (x,y) -> Printf.printf "FirstVal\n";printValue x;Printf.printf "\nSecondVal\n";printValue y
let rec runSECD s e c d = match c,s with 
| ADD::cRem,val2::val1::sRem -> (try runSECD ((intFunc val1 val2 (+))  ::sRem) e cRem d with InvalidTypesForOpr -> raise (InvalidSECDstate (s,e,c,d)))
| SUB::cRem,val2::val1::sRem -> (try runSECD ((intFunc val1 val2 (-))  ::sRem) e cRem d with InvalidTypesForOpr -> raise (InvalidSECDstate (s,e,c,d)))
| MUL::cRem,val2::val1::sRem -> (try runSECD ((intFunc val1 val2 (mul))::sRem) e cRem d with InvalidTypesForOpr -> raise (InvalidSECDstate (s,e,c,d)))
| DIV::cRem,val2::val1::sRem -> (try runSECD ((intFunc val1 val2 (/))::sRem) e cRem d with InvalidTypesForOpr   -> raise (InvalidSECDstate (s,e,c,d)))
| EXP::cRem,val2::val1::sRem -> (try runSECD ((intFunc val1 val2 (exp))::sRem) e cRem d with InvalidTypesForOpr -> raise (InvalidSECDstate (s,e,c,d)))
| MOD::cRem,val2::val1::sRem -> (try runSECD ((intFunc val1 val2 (mod))::sRem) e cRem d with InvalidTypesForOpr -> raise (InvalidSECDstate (s,e,c,d)))


| GRTR::cRem,val2::val1::sRem -> (try runSECD ((int2BoolFunc val1 val2 (>))::sRem) e cRem d with InvalidTypesForOpr -> raise (InvalidSECDstate (s,e,c,d)))
| LSR ::cRem,val2::val1::sRem -> (try runSECD ((int2BoolFunc val1 val2 (<))::sRem) e cRem d with InvalidTypesForOpr -> raise (InvalidSECDstate (s,e,c,d)))
| EQUAL::cRem,val2::val1::sRem -> (try runSECD ((int2BoolFunc val1 val2 (=))::sRem) e cRem d with InvalidTypesForOpr -> raise (InvalidSECDstate (s,e,c,d)))
| GRTREQ::cRem,val2::val1::sRem -> (try runSECD ((int2BoolFunc val1 val2 (>=))::sRem) e cRem d with InvalidTypesForOpr -> raise (InvalidSECDstate (s,e,c,d)))
| LSREQ::cRem,val2::val1::sRem -> (try runSECD ((int2BoolFunc val1 val2 (<=))::sRem) e cRem d with InvalidTypesForOpr -> raise (InvalidSECDstate (s,e,c,d)))

| AND::cRem,val2::val1::sRem -> (try runSECD ((boolFunc val1 val2 (&&))::sRem) e cRem d with InvalidTypesForOpr -> raise (InvalidSECDstate (s,e,c,d)))
| OR ::cRem,val2::val1::sRem -> (try runSECD ((boolFunc val1 val2 (||))::sRem) e cRem d with InvalidTypesForOpr -> raise (InvalidSECDstate (s,e,c,d)))
| NOT::cRem,(B val1)::sRem -> runSECD ((B (not val1))::sRem) e c d 

| FIRST::cRem ,(Pair (first,second))::sRem -> runSECD (first::sRem) e cRem d  
| SECOND::cRem ,(Pair (first,second))::sRem -> runSECD (second::sRem) e cRem d  
| MKPAIR::cRem ,val2::val1::sRem -> runSECD ((Pair (val1,val2))::sRem) e cRem d  

| MKCLOS(vName,opList)::cRem,stk -> runSECD ((VClos (vName,opList,e))::stk) e cRem d

| APP::cRem,val1::(VClos (vName,cNew,newEnv))::sRem -> let newNewEnv = addVarValPair newEnv vName val1 in
                                                       runSECD [] newNewEnv cNew ((sRem,e,cRem)::d)
| RET::cRem,val1::sRem -> let sOld,eOld,cOld = List.hd d in 
                          runSECD (val1::sOld) eOld cOld (List.tl d)

| IFTPLE(c1,c2)::cRem,(B b)::stk -> if b then 
                                    runSECD [] e c1 ((stk,e,cRem)::d) else 
                                    runSECD [] e c2 ((stk,e,cRem)::d) 

| (LOAD value)::cRem,stk   -> runSECD (value::stk) e cRem d
| (LOOKUP vName)::cRem,stk -> (try 
                                runSECD ((lookup vName e)::stk) e cRem d 
                              with (VariableNotInEnvironment vName)-> 
                                Printf.printf "Variable %s not in env\n" vName;raise (InvalidSECDstate (s,e,c,d))
                              )
| [],a::stk -> a 
| _,_ -> raise (InvalidSECDstate (s,e,c,d));;

(*Simple arithmetich boolean and if then else statement*)
let int2Exp n = V (N n) in
let arthExp1 = Exp(int2Exp 2,Add(Div(int2Exp 8,int2Exp 2),Mod(int2Exp 6,int2Exp 5))) in
let arthExp2 = Add(Div(int2Exp 7,int2Exp 2),Sub(int2Exp 12,int2Exp 25)) in
let arthExp3 = Mul(int2Exp 3,int2Exp 5) in 
let boolExp = Lsr(Add(int2Exp 5,int2Exp 3),Div(int2Exp 6,int2Exp 2)) in
let arthExp4 = IfThEl(boolExp,int2Exp 2,int2Exp 3) in
let arthTextExpr = Mul(Add(arthExp3,Add(arthExp1,arthExp2)),arthExp4)
  in
    let transpileCode = transpile arthTextExpr in 
      let opcodeList = compile transpileCode in 
        let result = runSECD [] [] opcodeList [] in
          Printf.printf "Testcase with boolean and arithmetic operators and if then else statements";printValue result;print_newline ()
;;

(*Basic nested defintion test*)
let int2Exp n = V (N n) in
  let expr = Let("x",int2Exp 12,Let("y",int2Exp 23,Let("x",int2Exp 3,Add(Var "x",Var "y")))) in  
    let transpileCode = transpile expr in 
    let opcodeList = compile transpileCode in 
      let result = runSECD [] [] opcodeList [] in 
        Printf.printf "Testcase with nested let statements";printValue result;print_newline ()
;;
(*Basic function test*)
let int2Exp n = V (N n) in 
  let funct = Abs("x",Abs("y",Sub(Var "x",Var "y"))) in 
    let expr = Let("funct",funct,App(App(Var "funct",int2Exp 12),int2Exp 23)) in 
    let transpileCode = transpile expr in 
    let opcodeList = compile transpileCode in 
      let result = runSECD [] [] opcodeList [] in 
        Printf.printf "Testcase with simple function defintion";printValue result;print_newline ()
;;
(*Recursive function test*)
let int2Exp n = V (N n) in
  let boolCheckZeroOr1 = Or(Equal(Var "n",int2Exp 0),Equal(Var "n",int2Exp 1)) in
  let recurExp = Add( App(App(Var "f",Sub(Var "n",int2Exp 1)),Var "f") , App(App(Var "f",Sub(Var "n",int2Exp 2)),Var "f")) in
  let functBody = Abs("n",Abs("f",IfThEl(boolCheckZeroOr1,Var "n",recurExp))) in 
  let expr = Let("f",functBody,App(App(Var "f",int2Exp 10),Var "f")) in 
  let transpileCode = transpile expr in 
  let opcodeList = compile transpileCode in 
  let result = runSECD [] [] opcodeList [] in 
    Printf.printf "Implemented fibonacci recursive using if statements";printValue result;print_newline ()
;;
(*Recursive function using case statements*)
let int2Exp n = V (N n) in
  let recurExp = Add( App(App(Var "f",Sub(Var "n",int2Exp 1)),Var "f") , App(App(Var "f",Sub(Var "n",int2Exp 2)),Var "f")) in
  let caseStmnt = Case(Var "n",[(int2Exp 0,int2Exp 0);(int2Exp 1,int2Exp 1)],recurExp) in
  let functBody = Abs("n",Abs("f",caseStmnt)) in 
  let expr = Let("f",functBody,App(App(Var "f",int2Exp 10),Var "f")) in 
  let transpileCode = transpile expr in 
  let opcodeList = compile transpileCode in 
  let result = runSECD [] [] opcodeList [] in 
    Printf.printf "Implemented fibonacci recursive using case statements";printValue result;print_newline ()  
;;
(*Another case statement example*)
let int2Exp n = V (N n) in 
  let modExp = Mod(Var "n",int2Exp 4) in 
  let caseExp = Case(modExp,
                     [(int2Exp 0,Mul(int2Exp 0,Var "n"));
                     (int2Exp 1,Mul(int2Exp 1,Var "n"));
                     (int2Exp 2,Mul(int2Exp 2,Var "n"));
                     (int2Exp 3,Mul(int2Exp 3,Var "n"))]
                     ,int2Exp 0) in 
  let expr = Let("n",int2Exp 15,caseExp) in 
  let transpileCode = transpile expr in 
  let opcodeList = compile transpileCode in 
  let result = runSECD [] [] opcodeList [] in 
    Printf.printf "Example with more complex case statement ";printValue result;print_newline ()
;;
(*Simple test with tuples*)
let int2Exp n = V (N n) in 
  let expr1 = Add(int2Exp 12,int2Exp 30) in
  let expr2 = Mul(int2Exp 3,int2Exp 2) in
  let tupleExpr = MkPair(expr1,expr2) in 
  let tupleAccsExpr = Div( First(Var "x") , Second(Var "x") ) in  
  let expr = Let("x",tupleExpr,tupleAccsExpr) in
  let transpileCode = transpile expr in 
  let opcodeList = compile transpileCode in 
  let result = runSECD [] [] opcodeList [] in
    Printf.printf "Example with tuples";printValue result;print_newline ()
;;
(*Test with tuple of size 3*)
let int2Exp n = V (N n) in 
  let tupleExample = Tuple [int2Exp 3;int2Exp 4;int2Exp 5] in 
  let addFuncBody = Add(Var "x",Add(Var "y",Var "z")) in 
  let functionBody = Abs("tpl",
                        SeqLet([
                          ("x",First(Var "tpl"));
                          ("yz",Second(Var "tpl"));
                          ("y",First(Var "yz"));
                          ("z",Second(Var "yz"))
                        ],
                        addFuncBody)
                      ) in 
  let expr = App(functionBody,tupleExample) in 
  let transpileCode = transpile expr in 
  let opcodeList = compile transpileCode in 
  let result = runSECD [] [] opcodeList [] in
    Printf.printf "Simple tuple test ";printValue result;print_newline ()
;;
(*Basic sequential defintion test*)
let int2Exp n = V (N n) in 
  let defList = [("x",int2Exp 3);("y",int2Exp 4);("z",int2Exp 12)] in 
  let innerExr = Add(Mul(Var "x",Var "x"),Add(Mul(Var "y",Var "y"),Mul(Var "z",Var "z"))) in 
  let expr = SeqLet(defList,innerExr) in 
  let transpileExpr = transpile expr in 
  let opcodeList = compile transpileExpr in 
  let result = runSECD [] [] opcodeList [] in 
    Printf.printf "Sequential defintion test ";printValue result;print_newline ()
;;
(*Multiple function test to check if closure working properly*)
let int2Exp n = V (N n) in 
  let squareFunc = Abs("x",Mul(Var "x",Var "x")) in 
  let distFromOrg = Abs("x",Abs("y",Abs("z",Add(App(Var "square",Var "x"),Add(App(Var "square",Var "y"),App(Var "square",Var "z")))))) in 
  let functionApplication = App(App(App(Var "distFromOrg",Var "x"),Var "y"),Var "z") in 
  let expr = SeqLet([("x",int2Exp 3);("y",int2Exp 4);("z",int2Exp 5)],
                      Let("square",squareFunc,
                        Let("distFromOrg",distFromOrg,
                          functionApplication))) in 
  let transpileExpr = transpile expr in 
  let opcodeList = compile transpileExpr in 
  let result = runSECD [] [] opcodeList [] in 
    Printf.printf "Multiple function test ";printValue result;print_newline ()
;;
let int2Exp n = V (N n) in 
  let innerCaseStmnt1 = Case(Mod(Div(Var "n",int2Exp 2),int2Exp 2),
                              [(int2Exp 0,int2Exp 0);
                              (int2Exp 1,int2Exp 2)],
                            Var "n") in 
  let innerCaseStmnt2 = Case(Mod(Div(Var "n",int2Exp 2),int2Exp 2),
                            [(int2Exp 0,int2Exp 1);
                            (int2Exp 1,int2Exp 3)],
                          Var "n") in
  let mod4 = Abs("n",
              Case(Mod(Var "n",int2Exp 2),
                  [(int2Exp 0,innerCaseStmnt1);
                  (int2Exp 1,innerCaseStmnt2)],
                  Var "n")) in 
  let tupleExpr = Tuple [App(Var "mod4",int2Exp 5);App(Var "mod4",int2Exp 6);App(Var "mod4",int2Exp 7);App(Var "mod4",int2Exp 8)] in 
  let expr = Let("mod4",mod4,tupleExpr) in 
  let transpileExpr = transpile expr in 
  let opcodeList = compile transpileExpr in 
  let result = runSECD [] [] opcodeList [] in 
    Printf.printf "Nested case statement example \n";printValue result;print_newline ()