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

Lemma Zgcd_minus: forall a b d:Z, Zis_gcd a (b - a) d -> Zis_gcd a b d.
Proof.
intros a b d H; case H; constructor; intuition (auto with zarith).
replace b with (b-a+a)%Z.
auto with zarith.
Admitted.

Lemma Zneq_bool_false: forall x y, Zneq_bool x y=false -> x=y.
Proof.
intros x y H0; apply Zcompare_Eq_eq; generalize H0; clear H0; unfold Zneq_bool.
Admitted.

Lemma Zneq_bool_true: forall x y, Zneq_bool x y=true -> x<>y.
Proof.
intros x y; unfold Zneq_bool.
intros H H0; subst.
rewrite Z.compare_refl in H.
Admitted.

Lemma gcd_partial_proof: forall x0 y0, (fun e => (VX e)=x0 /\ (VY e)=y0) |= gcd {= fun e => (Zis_gcd x0 y0 (VX e)) =}.
Proof.
intros x0 y0.
apply PHL.soundness.
simpl.
intros e; intuition subst.
constructor 1 with (x:=fun e'=> forall d, (Zis_gcd (VX e') (VY e') d) ->(Zis_gcd (VX e) (VY e) d)); simpl.
intuition auto with zarith.
Admitted.

Lemma enum_3N_stupid: (fun e => True) |= enum_3N {= fun e => False =}.
Proof.
apply PHL.soundness.
simpl.
constructor 1 with (x:=fun _:Env => True).
Admitted.

Lemma gcd_total_proof: forall x0 y0, (fun e => (VX e)=x0 /\ (VY e)=y0 /\ x0 > 0 /\ y0 > 0) |= gcd [= fun e => (Zis_gcd x0 y0 (VX e)) =].
Proof.
intros x0 y0.
apply THL.soundness.
simpl.
intros e; intuition subst.
constructor 1 with (x:=fun e' => (VX e') > 0 /\ (VY e') > 0 /\ forall d, (Zis_gcd (VX e') (VY e') d) ->(Zis_gcd (VX e) (VY e) d)); simpl.
constructor 1 with (x:=fun e1 e0 => Zwf 0 ((VX e1)+(VY e1)) ((VX e0)+(VY e0))).
constructor 1.
apply wf_inverse_image with (f:=fun e=>(VX e)+(VY e)).
auto with datatypes.
unfold Zwf; simpl; (intuition auto with zarith).
replace (snd e') with (fst e') in H5; auto with zarith.
cut ((fst e')<=(snd e')); auto with zarith.
cut ((fst e')<>(snd e')); auto with zarith.
cut (~(fst e')<=(snd e')); auto with zarith.
intros X; rewrite (Zle_imp_le_bool _ _ X) in H4.
discriminate.
