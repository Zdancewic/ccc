%{
open Ast

let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : ('d, 'a) node =
  { elt ; loc=Range.mk_lex_range startpos endpos ; dec=None }

%}

/* Declare your tokens here. */
%token EOF
%token <int>  INT
%token <string> LIDENT    /* lowercase identifier */
%token <string> UIDENT    /* uppercase identifier */
%token <string> STRING

%token ONE      /* One */
%token ZERO     /* Zero */
%token <int> TBASE  /* B[n] */
%token TYPE     /* type */
%token CONST    /* const */
%token BEGIN    /* begin */
%token MATCH    /* match */
%token WITH     /* with */
%token END      /* end */
%token INL      /* inl */
%token INR      /* inr */
%token FST      /* fst */
%token SND      /* snd */
%token LET      /* let */
%token IN       /* in */
%token FUN      /* fun */
%token ABORT    /* fun */
%token COMMA    /* , */
%token PLUS     /* + */
%token STAR     /* * */
%token EQ       /* = */
%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token LBRACKET /* [ */
%token RBRACKET /* ] */
%token ARROW    /* -> */
%token BAR      /* | */
%token COLON    /* : */
%token UNIT     /* () */

%right PLUS STAR
%right ARROW


/* ---------------------------------------------------------------------- */

%start prog
%start exp_top
%type <(unit, unit Ast.exp) Ast.node> exp_top
%type <unit Ast.prog> prog
%type <(unit, unit Ast.exp) Ast.node> exp
%type <(unit, unit Ast.ty) node> ty

%%

exp_top:
  | e=exp EOF { e }


prog:
  | ts=list(tydef) e=exp_top  { (ts,e) }
    
ty:
  | tid=UIDENT             { loc $startpos $endpos @@ TId tid }
  | b=TBASE                { loc $startpos $endpos @@ TBase b }
  | ZERO                   { loc $startpos $endpos @@ TZero }
  | ONE                    { loc $startpos $endpos @@ TUnit }
  | t=ty PLUS u=ty         { loc $startpos $endpos @@ TSum(t, u) }
  | t=ty STAR u=ty         { loc $startpos $endpos @@ TProd(t, u) }
  | t=ty ARROW u=ty        { loc $startpos $endpos @@ TArr(t, u) }
  | LPAREN t=ty RPAREN     { t }

tydef:
  | TYPE tid=UIDENT EQ t=ty  { (tid, t) }

bnd:
  | LPAREN x=LIDENT COLON t=ty RPAREN { (x,t) }

arglist:
  | l=list(bnd) { l }


exp:
  | FUN args=arglist ARROW e=exp                        { loc $startpos $endpos @@ Lam (args, e) }
  | LET x=LIDENT COLON t=ty EQ e1=exp
    IN e2 = exp                                         { loc $startpos $endpos @@ Let ((x,t), e1, e2) }
  | e=exp0                                              { e }

exp0:
  | e=exp1                                              { e }
  | e1=exp0 e2=exp1                                     { (loc $startpos $endpos @@ App (e1, e2)) } 

exp1:
  | CONST LBRACKET i=INT COLON t=ty RBRACKET            { (loc $startpos $endpos @@ Const (i, t)) }

  | x=LIDENT                                            { (loc $startpos $endpos @@ Id x) }

  | UNIT                                                { (loc $startpos $endpos @@ Unit) }

  | INL LPAREN e=exp RPAREN                             { (loc $startpos $endpos @@ Inl e) }

  | INR LPAREN e=exp RPAREN                             { (loc $startpos $endpos @@ Inr e) }

  | BEGIN MATCH e1=exp WITH
    BAR INL LPAREN x=LIDENT RPAREN ARROW e2 = exp
    BAR INR LPAREN y=LIDENT RPAREN ARROW e3 = exp
    END                                                 { (loc $startpos $endpos @@ Case (e1, x, e2, y, e3)) }


  | LPAREN e=exp c=close                                { (c e) }

  | FST                                                 { (loc $startpos $endpos @@ Fst) }

  | SND                                                 { (loc $startpos $endpos @@ Snd) }

  | ABORT                                               { (loc $startpos $endpos @@ Abort) }


close:
  | RPAREN                         { (fun e -> e)  }
  | COMMA e2=exp RPAREN            { (fun e1 -> (loc $startpos $endpos @@ Pair (e1, e2))) }

