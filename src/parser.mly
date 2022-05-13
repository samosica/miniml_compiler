%{
open Syntax
open Location

let mkloc ls le =
  { loc_start = ls; loc_end = le }
   
let mkexp d ls le =
  { exp_desc = d
  ; exp_loc = mkloc ls le
  }
  
let ghexp d =
  { exp_desc = d
  ; exp_loc = dummy_loc
  }
  
let reloc_exp e ls le =
  { e with exp_loc = mkloc ls le }
%}

%token LPAREN RPAREN SEMISEMI RARROW
%token PLUS MULT LT EQ
%token IF THEN ELSE TRUE FALSE LET IN FUN REC
%token LOOP RECUR COMMA DOT

%token <int> INTV
%token <Syntax.id> ID

%start toplevel
%type <Syntax.exp> toplevel
%%

toplevel :
    e=Expr SEMISEMI { let ast = e in
                      recur_check ast;
                      ast }

Expr :
    e=IfExpr     { e }
  | e=FunExpr    { e }
  | e=LetExpr    { e }
  | e=LetRecExpr { e }
  | e=LoopExpr   { e }
  | e=LTExpr     { e }

LTExpr :
    e1=PExpr LT e2=PExpr { mkexp (BinOp (Lt, e1, e2)) $symbolstartpos $endpos }
  | e=PExpr { e }

PExpr :
    e1=PExpr PLUS e2=MExpr { mkexp (BinOp (Plus, e1, e2)) $symbolstartpos $endpos }
  | e=MExpr { e }

MExpr :
    e1=MExpr MULT e2=AppExpr { mkexp (BinOp (Mult, e1, e2)) $symbolstartpos $endpos }
  | e=AppExpr { e }

AppExpr :
    e1=AppExpr e2=AExpr { mkexp (AppExp (e1, e2)) $symbolstartpos $endpos }
  | RECUR e=AExpr { mkexp (RecurExp e) $symbolstartpos $endpos }
  | e=AExpr { e }

AExpr :
    i=INTV { mkexp (ILit i) $symbolstartpos $endpos }
  | TRUE { mkexp (BLit true) $symbolstartpos $endpos }
  | FALSE { mkexp (BLit false) $symbolstartpos $endpos }
  | i=ID { mkexp (Var i) $symbolstartpos $endpos }
  | LPAREN e=Expr RPAREN { e }
  | LPAREN e1=Expr COMMA e2=Expr RPAREN { mkexp (TupleExp (e1, e2)) $symbolstartpos $endpos }
  | e=AExpr DOT i=INTV { mkexp (ProjExp (e, i, mkloc $startpos(i) $endpos(i))) $symbolstartpos $endpos }
   
IfExpr :
    IF e1=Expr THEN e2=Expr ELSE e3=Expr { mkexp (IfExp (e1, e2, e3)) $symbolstartpos $endpos }

LetExpr :
    LET i=ID EQ e1=Expr IN e2=Expr { mkexp (LetExp (i, mkloc $startpos(i) $endpos(i), e1, e2)) $symbolstartpos $endpos }

FunExpr :
    FUN i=ID RARROW e=Expr { mkexp (FunExp (i, e)) $symbolstartpos $endpos }

LetRecExpr :
    LET REC i=ID EQ FUN p=ID RARROW e1=Expr IN e2=Expr
      { if i = p then
          err "Name conflict"
        else if i = "main" then
          err "main must not be declared"
        else
          mkexp (LetRecExp (i, mkloc $startpos(i) $endpos(i), p, e1, e2)) $symbolstartpos $endpos }

LoopExpr :
    LOOP i=ID EQ e1=Expr IN e2=Expr { mkexp (LoopExp (i, mkloc $startpos(i) $endpos(i), e1, e2)) $symbolstartpos $endpos }
