open List;;

type varName = string 
type value = N of int | B of bool
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
| LsrEq of expr*expr 
| GrtrEq of expr*expr 
| Equal of expr*expr 

| And of expr*expr 
| Or of expr*expr 
| Not of expr 

| Abs of varName*expr 
| App of expr*expr 

| IfThEl of expr*expr*expr
| Let of varName*expr*expr

| SeqLet of ((varName*expr) list)*expr
| Case of expr*((expr*expr) list)*expr (*In the case statement first expression is what we will run the selection on
                                         additionaly the last expression is the default case which is made necessary here 
                                         eventhough it may be unused in some pieces of code*)
| MkPair of expr*expr 
| Tuple of expr list
| First of expr 
| Second of expr 



and clos = C of expr*table 
and table = (varName*clos) list 

type krivineState = clos*(clos list)

let lamdaCalTrue = Abs("!",Abs("!!",Var "!"))
let lamdaCalFalse = Abs("!",Abs("!!",Var "!!")) 
let boolToLambdaCal b = if b then lamdaCalTrue else lamdaCalFalse

let rec transpileSeqLeft defList innerExpr = match defList with 
| []  -> innerExpr
| (vName,exp)::rem -> Let(vName,exp,transpileSeqLeft rem innerExpr) 
let rec transCaseStmntHelper vName caseList defaultCaseExpr = match caseList with 
| (val1Exp,exp1):: rem -> IfThEl(Equal(Var vName,val1Exp),exp1,transCaseStmntHelper vName rem defaultCaseExpr)
| [] -> defaultCaseExpr
and transCaseStmnt inputExpr caseList defaultCaseExpr =  
  let tempVarName = "!" in 
    let tempExpr = Let(tempVarName,inputExpr,transCaseStmntHelper tempVarName caseList defaultCaseExpr) in 
      tempExpr

exception InvalidEmptyTuple

let rec transpileTuple exprList = match exprList with 
| exp1::[] -> exp1 
| exp1::rem -> MkPair(exp1,transpileTuple rem)
| [] -> raise InvalidEmptyTuple
let rec transpile expr = match expr with
| V(N n) -> V(N n)
| V(B b) -> boolToLambdaCal b 
| Var x  -> Var x 

| Add(expr1,expr2) -> Add(transpile expr1,transpile expr2)
| Sub(expr1,expr2) -> Sub(transpile expr1,transpile expr2)
| Mul(expr1,expr2) -> Mul(transpile expr1,transpile expr2)
| Div(expr1,expr2) -> Div(transpile expr1,transpile expr2)
| Mod(expr1,expr2) -> Mod(transpile expr1,transpile expr2)
| Exp(expr1,expr2) -> Exp(transpile expr1,transpile expr2)

| Grtr(expr1,expr2) -> Grtr(transpile expr1,transpile expr2)
| Lsr(expr1,expr2) -> Lsr(transpile expr1,transpile expr2)
| Equal(expr1,expr2) -> Equal(transpile expr1,transpile expr2)
| GrtrEq(expr1,expr2) -> GrtrEq(transpile expr1,transpile expr2)
| LsrEq(expr1,expr2) -> LsrEq(transpile expr1,transpile expr2)

| IfThEl(expr1,expr2,expr3) -> let expr1 = transpile expr1 in 
                               let expr2 = transpile expr2 in 
                               let expr3 = transpile expr3 in 
                               let ifThElLambda = Abs("x",Abs("y",Abs("z",App(App(Var "x",Var "y"),Var "z")))) in 
                                 App(App(App(ifThElLambda,expr1),expr2),expr3)

| Case(inputExpr,caseList,defaultCaseExpr) -> transpile (transCaseStmnt inputExpr caseList defaultCaseExpr)
(*cross check can remove transpile for expr1 expr2*)
| And(expr1,expr2) -> let expr1 = transpile expr1 in 
                      let expr2 = transpile expr2 in
                      transpile (IfThEl(expr1,expr2,V(B false)))
| Or(expr1,expr2) -> let expr1 = transpile expr1 in 
                     let expr2 = transpile expr2 in
                     transpile (IfThEl(expr1,V(B true),expr2))
| Not(expr1) -> transpile (IfThEl(transpile expr1,V(B false),V(B true)))

| Abs(vName,expr2) -> Abs(vName,transpile expr2)
| App(expr1,expr2) -> App(transpile expr1,transpile expr2)
| Let(varName,expr1,expr2) -> App(Abs(varName,transpile expr2),transpile expr1) 
| SeqLet(defList,innerExp) -> transpile (transpileSeqLeft defList innerExp)

| MkPair(expr1,expr2) -> Abs("#",App(App(Var "#",transpile expr1),transpile expr2))
| First(tplExpr) -> App(transpile tplExpr,Abs("#",Abs("##",Var "#")))
| Second(tplExpr) -> App(transpile tplExpr,Abs("#",Abs("##",Var "##")))
| Tuple(exprList) -> transpile(transpileTuple exprList)

exception VarNotFound of string
let rec lookup varName env = match env with
| [] -> raise (VarNotFound varName)
| (vName,clos)::rem -> if vName = varName then 
                        clos 
                       else 
                        (lookup varName rem)
let exprToCls e = C (e,[])

exception ExpectedInt of value

let extractIntFromValue value = match value with 
| N n -> n 
| B b -> raise (ExpectedInt value)
exception ExpectedIntClos of clos
exception ExpectedBooleanLambda of expr
let extractIntFromClos clos = match clos with
| C(V(N n),_) -> n 
| _ -> raise (ExpectedIntClos clos)
let isLambdaFuncBool expr = if (expr=lamdaCalTrue) || (expr=lamdaCalFalse) then true else false 
let intToVal n = V(N n)
let boolToVal b = V(B b)
(*
(*not completely sure why this is not working*)
let lamdaFuncToBool expr = match expr with 
| lamdaCalTrue  -> true
| lamdaCalFalse -> false 
| _ -> raise (ExpectedBooleanLambda expr)
*)
let lambdaFuncToBool expr = if expr=lamdaCalTrue then 
                              true 
                            else 
                              if expr=lamdaCalFalse then 
                                 false 
                              else
                                 raise (ExpectedBooleanLambda expr)
exception NoArgumentForFunction
exception TranspileExprFirst of expr
exception ZeroPowerZero
let rec exp num pow = match pow with 
| 0 -> if num=0 then raise ZeroPowerZero else 1
| x -> let temp = exp num (pow/2) in 
          if pow mod 2 == 0 then 
            temp*temp else temp*temp*num
let extractExprFromClos clos = (match clos with |C(e,_) -> e)
(*Assumes always returns a value*)
let rec runKirvine exprAsClos closStk = match exprAsClos,closStk with 
| C(App(e1,e2),env),_       -> let funcClosure = C(e1,env) in 
                             let newClosStk = (C(e2,env))::closStk in 
                                runKirvine funcClosure newClosStk
| C(Var varName,env),_       -> let varValue = lookup varName env in
                                runKirvine varValue closStk
(*Add special case to deal with exprAsClos*)
| C(Abs(varName,exp),env),[] -> exprAsClos
| C(Abs(varName,exp),env),_  -> let argument = hd closStk in 
                             let newEnv = (varName,argument)::env in 
                             let newClos = C(exp,newEnv) in 
                                runKirvine newClos (tl closStk)
| C(Add(expr1,expr2),env),_  -> let val1 = extractIntFromClos(runKirvine (C(expr1,env)) closStk) in 
                             let val2 = extractIntFromClos(runKirvine (C(expr2,env)) closStk) in 
                                runKirvine (C(intToVal (val1+val2),env)) closStk
| C(Sub(expr1,expr2),env),_  -> let val1 = extractIntFromClos(runKirvine (C(expr1,env)) closStk) in 
                             let val2 = extractIntFromClos(runKirvine (C(expr2,env)) closStk) in 
                                runKirvine (C(intToVal (val1-val2),env)) closStk
| C(Mul(expr1,expr2),env),_  -> let val1 = extractIntFromClos(runKirvine (C(expr1,env)) closStk) in 
                             let val2 = extractIntFromClos(runKirvine (C(expr2,env)) closStk) in 
                                runKirvine (C(intToVal (val1*val2),env)) closStk
| C(Div(expr1,expr2),env),_  -> let val1 = extractIntFromClos(runKirvine (C(expr1,env)) closStk) in 
                             let val2 = extractIntFromClos(runKirvine (C(expr2,env)) closStk) in 
                                runKirvine (C(intToVal (val1/val2),env)) closStk
| C(Mod(expr1,expr2),env),_  -> let val1 = extractIntFromClos(runKirvine (C(expr1,env)) closStk) in 
                             let val2 = extractIntFromClos(runKirvine (C(expr2,env)) closStk) in 
                                runKirvine (C(intToVal (val1 mod val2),env)) closStk
| C(Exp(expr1,expr2),env),_  -> let val1 = extractIntFromClos(runKirvine (C(expr1,env)) closStk) in 
                             let val2 = extractIntFromClos(runKirvine (C(expr2,env)) closStk) in 
                                runKirvine (C(intToVal (exp val1 val2),env)) closStk
| C(Grtr(expr1,expr2),env),_  -> let val1 = extractIntFromClos(runKirvine (C(expr1,env)) closStk) in 
                             let val2 = extractIntFromClos(runKirvine (C(expr2,env)) closStk) in 
                                runKirvine (C(boolToLambdaCal (val1>val2),env)) closStk
| C(Lsr(expr1,expr2),env),_  -> let val1 = extractIntFromClos(runKirvine (C(expr1,env)) closStk) in 
                             let val2 = extractIntFromClos(runKirvine (C(expr2,env)) closStk) in 
                                runKirvine (C(boolToLambdaCal (val1<val2),env)) closStk
| C(Equal(expr1,expr2),env),_  -> let val1 = extractIntFromClos(runKirvine (C(expr1,env)) closStk) in 
                             let val2 = extractIntFromClos(runKirvine (C(expr2,env)) closStk) in 
                                runKirvine (C(boolToLambdaCal (val1=val2),env)) closStk
| C(LsrEq(expr1,expr2),env),_  -> let val1 = extractIntFromClos(runKirvine (C(expr1,env)) closStk) in 
                             let val2 = extractIntFromClos(runKirvine (C(expr2,env)) closStk) in 
                                runKirvine (C(boolToLambdaCal (val1<=val2),env)) closStk
| C(GrtrEq(expr1,expr2),env),_  -> let val1 = extractIntFromClos(runKirvine (C(expr1,env)) closStk) in 
                             let val2 = extractIntFromClos(runKirvine (C(expr2,env)) closStk) in 
                                runKirvine (C(boolToLambdaCal (val1>=val2),env)) closStk

| C(IfThEl(_,_,_),_),_  -> raise (TranspileExprFirst (extractExprFromClos exprAsClos))
| C(And(_,_),_),_  -> raise (TranspileExprFirst (extractExprFromClos exprAsClos))
| C(Or(_,_),_),_  -> raise (TranspileExprFirst (extractExprFromClos exprAsClos))
| C(Not(_),_),_  -> raise (TranspileExprFirst (extractExprFromClos exprAsClos))
| C(Let(_,_,_),_),_ -> raise (TranspileExprFirst (extractExprFromClos exprAsClos))
| C(SeqLet(_,_),_),_ -> raise (TranspileExprFirst (extractExprFromClos exprAsClos))
| C(Case(_,_,_),_),_ -> raise (TranspileExprFirst (extractExprFromClos exprAsClos))
| C(MkPair(_,_),_),_ -> raise (TranspileExprFirst (extractExprFromClos exprAsClos))
| C(First(_),_),_ -> raise (TranspileExprFirst (extractExprFromClos exprAsClos))
| C(Second(_),_),_ -> raise (TranspileExprFirst (extractExprFromClos exprAsClos))
| C(Tuple(_),_),_ -> raise (TranspileExprFirst (extractExprFromClos exprAsClos))
| C(V _,_),_ -> exprAsClos

exception CannotPrintFinalCls of clos 
exception ExpectedTupleHere of expr
(*add print capabilities for tuple and general closures as well*)
let isTuple e = match e with 
| Abs("#",App(App(Var "#",_),_)) -> true
| _ -> false
let extractTuplePair e = match e with 
| Abs("#",App(App(Var "#",e1),e2)) -> (e1,e2)
| _ -> raise (ExpectedTupleHere e)
let printTabs tabLvl = Printf.printf "%s" (String.make (tabLvl*3) ' ')
let rec printResultClos tabLvl clos = let expr = (match clos with | C(e,_) -> e) in
match expr with 
| V(N n) -> printTabs tabLvl;Printf.printf "%d\n" n
| expr -> if (isLambdaFuncBool expr) then 
                  (printTabs tabLvl;Printf.printf "%b\n" (lambdaFuncToBool expr))
               else 
                  if isTuple expr then 
                     printTuple tabLvl clos
                  else
                     let env = (match clos with | C(_,env) -> env) in 
                        printTabs tabLvl;Printf.printf "Expr is:\n";
                        printExpr (tabLvl+1) expr; 
                        printTabs tabLvl;Printf.printf "Env is:\n";
                        printEnv (tabLvl+1) env 
and printTuple tabLvl clos = 
   let expr = (match clos with| C(e,_) -> e) in 
   let env = (match clos with| C(_,env) -> env) in
      let e1,e2 = extractTuplePair expr in 
         printTabs tabLvl;Printf.printf "Tuple\n"; (*choosing not to print out the environment here may change that (Assumption is that would be printed downstream anyways)*)
         printResultClos (tabLvl+1) (C(e1,env));
         printResultClos (tabLvl+1) (C(e2,env))
and printEnv tabLvl env = printTabs tabLvl;Printf.printf "[";printEnvHelper (tabLvl+1) env;printTabs tabLvl;Printf.printf "]\n"
and printEnvHelper tabLvl env = match env with 
| [] -> print_newline () 
| (vName,clos)::rem -> printTabs tabLvl;Printf.printf "for vName %s clos is:\n" vName;printResultClos (tabLvl+1) clos;printEnvHelper tabLvl env
(*not bothering to reverse the transpiling for the boolean operators 
  additional headache not adding as much value as reversing the 
  transformation for the tuples and booleans*)
(*similarly not reversing transpiling for the let expression too much effort*)
and printExpr tabLvl expr = match expr with 
| Add(e1,e2) -> printTabs tabLvl;Printf.printf "+\n";printExpr (tabLvl+1) e1;print_newline ();printExpr (tabLvl+1) e2
| Sub(e1,e2) -> printTabs tabLvl;Printf.printf "-\n";printExpr (tabLvl+1) e1;print_newline ();printExpr (tabLvl+1) e2
| Mul(e1,e2) -> printTabs tabLvl;Printf.printf "*\n";printExpr (tabLvl+1) e1;print_newline ();printExpr (tabLvl+1) e2
| Div(e1,e2) -> printTabs tabLvl;Printf.printf "/\n";printExpr (tabLvl+1) e1;print_newline ();printExpr (tabLvl+1) e2
| Mod(e1,e2) -> printTabs tabLvl;Printf.printf "mod\n";printExpr (tabLvl+1) e1;print_newline ();printExpr (tabLvl+1) e2
| Exp(e1,e2) -> printTabs tabLvl;Printf.printf "**\n";printExpr (tabLvl+1) e1;print_newline ();printExpr (tabLvl+1) e2

| Grtr(e1,e2) ->  printTabs tabLvl;Printf.printf ">\n";printExpr (tabLvl+1) e1;print_newline ();printExpr (tabLvl+1) e2
| Lsr(e1,e2) -> printTabs tabLvl;Printf.printf "<\n";printExpr (tabLvl+1) e1;print_newline ();printExpr (tabLvl+1) e2
| GrtrEq(e1,e2) -> printTabs tabLvl;Printf.printf ">=\n";printExpr (tabLvl+1) e1;print_newline ();printExpr (tabLvl+1) e2
| LsrEq(e1,e2) -> printTabs tabLvl;Printf.printf "<=\n";printExpr (tabLvl+1) e1;print_newline ();printExpr (tabLvl+1) e2
| Equal(e1,e2) -> printTabs tabLvl;Printf.printf "=\n";printExpr (tabLvl+1) e1;print_newline ();printExpr (tabLvl+1) e2

| Abs(vName,e) -> printTabs tabLvl;Printf.printf "Abs %s\n" vName;printExpr (tabLvl+1) e
| App(e1,e2) -> printTabs tabLvl;Printf.printf "App\n";printExpr (tabLvl+1) e1;print_newline ();printExpr (tabLvl+1) e2
| Var varName -> printTabs tabLvl;Printf.printf "%s\n" varName
| _ -> Printf.printf "Shouldnt expect any other expression types in transpiled code \n";raise (TranspileExprFirst expr)

let interpretter expr = 
   let expr = transpile expr in
   let exprClos = C(expr,[]) in
      let closResult = runKirvine exprClos [] in 
         Printf.printf "result is:\n";printResultClos 0 closResult;
;;
(*result should be 3 Simple arithmetic test*)
Printf.printf "Simple arithmetic test \n";
let expr1 = Div(Mul(Add(intToVal 1,intToVal 2),Sub(intToVal 10,intToVal 5)),intToVal 4) in 
   interpretter expr1
;;

(*simple nested let test*)
Printf.printf "Simple let expression test \n";
let exp1 = Let("x",Add(intToVal 1,intToVal 2), (*x =1+2 = 3*)
                  Let("y",Sub(Var "x",intToVal 10), (*y=x-10=-7*)
                     Add(Mul(Var "x",Var "y"),intToVal 12) (* x*y+12 = -21+12 = -9 *)
                  )
              ) in 
   interpretter exp1
;;

(*test of program that would fail to terminate in 
   call by value but terminates in call by name*)
(*below expression in toy language defiend in class 
   code would look like so:
   let f g = g g in 
      f f 
   ni*)
Printf.printf "test of code which would not terminate in call by value \n";
let infLoop = Let("f",Abs("g",App(Var "g",Var"g")),
                  App(Var "f",Var "f")
                 ) in 
let exp1 = App(App(Abs("x",Abs("y",Var "x")),intToVal 12),infLoop) in 
   interpretter exp1
;;(*expected result 12*)

(*simple test of boolean logic statements
   Added these testcases as have implemented boolean expressions 
   using lambda calculus*)
Printf.printf "Simple boolean identity test \n";
let exp1 =  boolToVal true in
   interpretter exp1
;;
Printf.printf "Or function test \n";
let exp1 = Or(boolToVal true,boolToVal false) in 
   interpretter exp1 
;;
Printf.printf "Boolean function test but of larger depth \n";
let exp1 = Or(boolToVal false,And(boolToVal true,Not(Or(boolToVal false,boolToVal false)))) in 
   interpretter exp1
;;
Printf.printf "Equals test to check if working properly \n";
let exp1 = Let("n",intToVal 1,Equal(Var "n",intToVal 2)) in 
   interpretter exp1 
;;
Printf.printf "Recursive program test\n";
let checkZeroor1 = Or(Equal(Var "n",intToVal 0),Equal(Var "n",intToVal 1)) in
let recurTerm1 = App(App(Var "f",Sub(Var "n",intToVal 1)),Var "f") in 
let recurTerm2 = App(App(Var "f",Sub(Var "n",intToVal 2)),Var "f") in 
let recurTerm = Add(recurTerm1,recurTerm2) in 
let fibFuncBody = IfThEl(checkZeroor1,Var "n",recurTerm) in 
let fibFunc = Abs("n",Abs("f",fibFuncBody)) in 
let exp1 = Let("fib",fibFunc,App(App(Var "fib",intToVal 11),Var "fib")) in 
   interpretter exp1
;;
Printf.printf "Case statement\n";
let caseExp = Case(Mod(Var "n",intToVal 4),
                  [(intToVal 0,Mul(intToVal 0,Var "n"));
                   (intToVal 1,Mul(intToVal 1,Var "n"));
                   (intToVal 2,Mul(intToVal 2,Var "n"));
                   (intToVal 3,Mul(intToVal 3,Var "n"));]
                   ,intToVal 0) in 
let exp1 = Let("n",intToVal 15,caseExp) in 
   interpretter exp1 
;;
Printf.printf "Simple test with tuples\n";
let e1 = Add(intToVal 12,intToVal 30) in 
let e2 = Mul(intToVal 3,intToVal 2) in 
let tupleExpr = MkPair(e1,e2) in 
let tupleAccsExpr = Div(First(Var "x"),Second(Var "x")) in 
let exp1 = Let("x",tupleExpr,tupleAccsExpr) in 
   interpretter exp1
;;
Printf.printf "Test with tuple of size 3\n";
let tupleExmpl = Tuple [intToVal 3;intToVal 4;intToVal 12] in 
let squareFuncBody = Abs("x",Mul(Var "x",Var "x")) in 
let dstFromOrgAdd = Add(Add(App(Var "sqr",Var "x"),App(Var "sqr",Var "y")),App(Var "sqr",Var "z")) in 
let squareAndAdd = Let("sqr",squareFuncBody,dstFromOrgAdd) in
let dstFromOrgFunc = Abs("tpl",
                        SeqLet([
                           ("x",First(Var "tpl"));
                           ("yz",Second(Var "tpl"));
                           ("y",First(Var "yz"));
                           ("z",Second(Var "yz"))
                        ],squareAndAdd)) in 
let expr = App(dstFromOrgFunc,tupleExmpl) in 
   interpretter expr
;;
Printf.printf "Test for lazy evaluation of tuples (wouldnt terminate in call by value)\n";
let infLoop = Let("f",Abs("g",App(Var "g",Var"g")),
                  App(Var "f",Var "f")
                 ) in 
let tupleExpr = MkPair(Mul(intToVal 4,intToVal 3),infLoop) in 
let exp1 = First(tupleExpr) in 
   interpretter exp1
;;
(*removing tuple statement in result will re add later when able to print tuples*)
Printf.printf "Nested case statement example \n";
let innerCaseStmnt1 = Case(Mod(Div(Var "n",intToVal 2),intToVal 2),
[(intToVal 0,intToVal 0);
(intToVal 1,intToVal 2)],
Var "n") in 
let innerCaseStmnt2 = Case(Mod(Div(Var "n",intToVal 2),intToVal 2),
[(intToVal 0,intToVal 1);
(intToVal 1,intToVal 3)],
Var "n") in
let mod4 = Abs("n",
Case(Mod(Var "n",intToVal 2),
[(intToVal 0,innerCaseStmnt1);
(intToVal 1,innerCaseStmnt2)],
Var "n")) in 
let tupleExpr = App(Var "mod4",intToVal 7) in
let exp1 = Let("mod4",mod4,tupleExpr) in 
   interpretter exp1
;;
Printf.printf "Test for lazy evaluation of if statements \n";
let infLoop = Let("f",Abs("g",App(Var "g",Var"g")),App(Var "f",Var "f")) in 
let ifStmnt = IfThEl(Grtr(intToVal 12,intToVal 11),intToVal 23,infLoop) in 
   interpretter ifStmnt
;;
Printf.printf "Printing tuple directly to show that lazy evaluation is taking place\n";
let infLoop = Let("f",Abs("g",App(Var "g",Var"g")),App(Var "f",Var "f")) in 
let tuple = MkPair(infLoop,infLoop) in 
   interpretter tuple
;;