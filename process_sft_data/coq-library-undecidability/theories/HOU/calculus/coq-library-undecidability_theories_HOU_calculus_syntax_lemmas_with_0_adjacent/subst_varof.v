Set Implicit Arguments.
Require Import List Lia.
Import ListNotations.
From Undecidability.HOU Require Import calculus.terms calculus.prelim std.std.
Set Default Proof Using "Type".
Definition isVar X (e: exp X) := match e with var _ => True | _ => False end.
Definition isLam X (e: exp X) := match e with lambda _ => True | _ => False end.
Definition isApp X (e: exp X) := match e with app _ _ => True | _ => False end.
Definition isAtom X (e: exp X) := match e with lambda _ => False | app _ _ => False | _ => True end.
Ltac syn := match goal with | [H1: isVar ?X, H2: isLam ?X |- _] => solve [destruct X; cbn in *; intuition] | [H1: isVar ?X, H2: isApp ?X |- _] => solve [destruct X; cbn in *; intuition] | [H1: isApp ?X, H2: isLam ?X |- _] => solve [destruct X; cbn in *; intuition] | [H1: isApp ?X, H2: isAtom ?X |- _] => solve [destruct X; cbn in *; intuition] | [H1: isLam ?X, H2: isAtom ?X |- _] => solve [destruct X; cbn in *; intuition] | [ |- isLam (lambda _)] => constructor | [ |- isApp (app _ _)] => constructor | [ |- isAtom (var _)] => constructor | [ |- isAtom (const _)] => constructor | [ |- isVar (var _)] => constructor end.
Section Atoms.
Variable (X: Const).
End Atoms.
Ltac atom := match goal with | [ |- isAtom _] => cbn in *; intuition end.
Hint Extern 4 => syn : core.
Section DiscreteTypes.
Global Instance Const_dis (C: Const) : Dis C.
Proof.
eapply const_dis.
Global Instance exp_dis X: Dis (exp X).
Proof.
intros ??; unfold Dec; decide equality.
decide equality.
eapply const_dis.
Global Instance type_dis: Dis type.
Proof.
intros ??; unfold Dec; decide equality; decide equality.
End DiscreteTypes.
Section ApplicativeHead.
Variable (X: Const).
Fixpoint head (e: exp X) := match e with | const b => const b | var x => var x | lambda s => lambda s | app e1 e2 => head e1 end.
End ApplicativeHead.
Hint Resolve atom_var var_head atom_head : core.
Section TypeFunctions.
Fixpoint target (A: type) := match A with | typevar beta => typevar beta | A → B => target B end.
Definition target' (Gamma: list type) := map target Gamma.
Fixpoint arity (A: type) := match A with | typevar _ => 0 | A → B => S (arity B) end.
End TypeFunctions.
Section FreeVariables.
Context {X: Const}.
Fixpoint vars (s: exp X) := match s with | var x => [x] | const x => nil | lambda s => map pred (remove eq_dec 0 (vars s)) | app s1 s2 => vars s1 ++ vars s2 end.
Inductive varof (x: nat) : exp X -> Prop := | varofVar: varof x (var x) | varofAppL (s t: exp X): varof x s -> varof x (s t) | varofAppR (s t: exp X): varof x t -> varof x (s t) | varofLambda s: varof (S x) s -> varof x (lambda s).
Hint Constructors varof : core.
Hint Resolve varof_vars vars_varof : core.
Global Instance dec_varof: Dec2 (varof).
Proof.
intros x s; eapply iff_dec with (P := x ∈ vars s); intuition; eauto.
End FreeVariables.
Hint Constructors varof : core.
Hint Resolve varof_vars vars_varof : core.

Lemma subst_varof x sigma y (s: exp X): varof y s -> varof x (sigma y) -> varof x (sigma • s).
Proof.
induction 1 in sigma, x |-*; cbn; eauto.
intros H'; econstructor; eapply IHvarof; cbn; unfold funcomp.
now eapply ren_varof.
