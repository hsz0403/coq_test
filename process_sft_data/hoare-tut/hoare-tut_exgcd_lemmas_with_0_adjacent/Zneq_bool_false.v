Set Implicit Arguments.
Require Import ZArith.
Require Import Znumtheory.
Require Import hoarelogic.
Require Import Zwf.
Require Import Wellfounded.
Module Example <: ExprLang.
Inductive ExVar: Type -> Type := VX: (ExVar Z) | VY: (ExVar Z).
Definition Var:=ExVar.
Definition Env:= (Z*Z)%type.
Definition upd (A:Type): (ExVar A) -> A -> Env -> Env := fun x => match x in (ExVar A) return A -> Env -> Env with | VX => fun vx e => (vx,snd e) | VY => fun vy e => (fst e,vy) end.
Definition get (A:Type): (ExVar A) -> Env -> A := fun x => match x in (ExVar A) return Env -> A with | VX => fun e => fst e | VY => fun e => snd e end.
Inductive binOP: Type := PLUS | MINUS.
Definition eval_binOP: binOP -> Z -> Z -> Z := fun op => match op with | PLUS => Zplus | MINUS => Zminus end.
Inductive relOP: Type := EQ | NEQ | LE.
Definition eval_relOP: relOP -> Z -> Z -> bool := fun op => match op with | EQ => Zeq_bool | NEQ => Zneq_bool | LE => Zle_bool end.
Inductive ExExpr: Type -> Type := | const: forall (A:Type), A -> (ExExpr A) | binop: binOP -> (ExExpr Z) -> (ExExpr Z) -> (ExExpr Z) | relop: relOP -> (ExExpr Z) -> (ExExpr Z) -> (ExExpr bool) | getvar: forall (A:Type), (ExVar A) -> (ExExpr A).
Definition Expr:= ExExpr.
Fixpoint eval (A:Type) (expr:Expr A) (e:Env) { struct expr } : A := match expr in ExExpr A return A with | const A v => v | binop op e1 e2 => eval_binOP op (eval e1 e) (eval e2 e) | relop op e1 e2 => eval_relOP op (eval e1 e) (eval e2 e) | getvar A x => (get x e) end.
End Example.
Module HL := HoareLogic(Example).
Import HL.
Import Example.
Coercion getvar: ExVar >-> ExExpr.
Coercion binop: binOP >-> Funclass.
Coercion relop: relOP >-> Funclass.
Coercion get: ExVar >-> Funclass.
Definition gcd := (Iwhile (NEQ VX VY) (Iif (LE VX VY) (Iset VY (MINUS VY VX)) (Iset VX (MINUS VX VY)))).
Hint Resolve Zgcd_minus: zarith.
Hint Resolve Zneq_bool_true Zneq_bool_false Zle_bool_imp_le Zis_gcd_intro: zarith.
Definition enum_3N := (Iseq (Iset VX (const 0)) (Iwhile (const true) (Iset VX (PLUS VX (const 3))))).

Lemma Zneq_bool_false: forall x y, Zneq_bool x y=false -> x=y.
Proof.
intros x y H0; apply Zcompare_Eq_eq; generalize H0; clear H0; unfold Zneq_bool.
case (x ?= y)%Z; auto; try (intros; discriminate); auto.
