Set Implicit Arguments.
Require Import Lia.
Require Import Arith.
Require Export Coq.Program.Equality.
From Dblib Require Import DblibTactics DeBruijn Environments.
Inductive term := | TVar: nat -> term | TAbs: term -> term | TApp: term -> term -> term.
Instance Var_term : Var term := { var := TVar (* avoid eta-expansion *) }.
Fixpoint traverse_term (f : nat -> nat -> term) l t := match t with | TVar x => f l x | TAbs t => TAbs (traverse_term f (1 + l) t) | TApp t1 t2 => TApp (traverse_term f l t1) (traverse_term f l t2) end.
Instance Traverse_term : Traverse term term := { traverse := traverse_term }.
Instance TraverseVarInjective_term : @TraverseVarInjective term _ term _.
Proof.
constructor.
prove_traverse_var_injective.
Instance TraverseFunctorial_term : @TraverseFunctorial term _ term _.
Proof.
constructor.
prove_traverse_functorial.
Instance TraverseRelative_term : @TraverseRelative term term _.
Proof.
constructor.
prove_traverse_relative.
Instance TraverseIdentifiesVar_term : @TraverseIdentifiesVar term _ _.
Proof.
constructor.
prove_traverse_identifies_var.
Instance TraverseVarIsIdentity_term : @TraverseVarIsIdentity term _ term _.
Proof.
constructor.
prove_traverse_var_is_identity.
Inductive red : term -> term -> Prop := | RedBeta: forall t1 t2, red (TApp (TAbs t1) t2) (subst t2 0 t1) | RedContextTAbs: forall t1 t2, red t1 t2 -> red (TAbs t1) (TAbs t2) | RedContextTAppLeft: forall t1 t2 t, red t1 t2 -> red (TApp t1 t) (TApp t2 t) | RedContextTAppRight: forall t1 t2 t, red t1 t2 -> red (TApp t t1) (TApp t t2).
Inductive ty := | TyVar: nat -> ty | TyArrow: ty -> ty -> ty | TyForall: ty -> ty.
Instance Var_ty : Var ty := { var := TyVar (* avoid eta-expansion *) }.
Fixpoint traverse_ty (f : nat -> nat -> ty) l T := match T with | TyVar x => f l x | TyArrow T1 T2 => TyArrow (traverse_ty f l T1) (traverse_ty f l T2) | TyForall T => TyForall (traverse_ty f (1 + l) T) end.
Instance Traverse_ty : Traverse ty ty := { traverse := traverse_ty }.
Instance TraverseVarInjective_ty : @TraverseVarInjective ty _ ty _.
Proof.
constructor.
prove_traverse_var_injective.
Instance TraverseFunctorial_ty : @TraverseFunctorial ty _ ty _.
Proof.
constructor.
prove_traverse_functorial.
Instance TraverseRelative_ty : @TraverseRelative ty ty _.
Proof.
constructor.
prove_traverse_relative.
Instance TraverseIdentifiesVar_ty : @TraverseIdentifiesVar ty _ _.
Proof.
constructor.
prove_traverse_identifies_var.
Instance TraverseVarIsIdentity_ty : @TraverseVarIsIdentity ty _ ty _.
Proof.
constructor.
prove_traverse_var_is_identity.
Ltac introq := match goal with | |- ?P -> ?Q => idtac | |- forall _, _ => intro; introq | |- _ => idtac end.
Inductive j : nat -> env ty -> term -> ty -> Prop := | JVar: forall n E x T, lookup x E = Some T -> j n E (TVar x) T | JAbs: forall m n E t T1 T2, j m (insert 0 T1 E) t T2 -> j n E (TAbs t) (TyArrow T1 T2) | JApp: forall n m1 m2 E t1 t2 T1 T2, j m1 E t1 (TyArrow T1 T2) -> j m2 E t2 T1 -> j n E (TApp t1 t2) T2 | JTyAbs: forall n E t T, j n (map (shift 0) E) t T -> j n E t (TyForall T) | JTyApp: forall n m E t T U U', j m E t (TyForall T) -> m < n -> (* an explicit equality facilitates the use of this axiom by [eauto] *) subst U 0 T = U' -> j n E t U'.
Hint Constructors j : j.
Goal (* phony_inversion_JTyAbs: *) forall n E t T, j n E t (TyForall T) -> j (S n) (map (shift 0) E) t T.
Proof.
intros.
generalize (pun_2 T 0).
simpl.
intro h.
rewrite <- h.
clear h.
eapply JTyApp; [ | eauto | eauto ].
eapply type_weakening; [ eauto | eauto | ].
simpl_lift_goal.
eauto.

Instance TraverseFunctorial_term : @TraverseFunctorial term _ term _.
Proof.
constructor.
Admitted.

Instance TraverseRelative_term : @TraverseRelative term term _.
Proof.
constructor.
Admitted.

Instance TraverseIdentifiesVar_term : @TraverseIdentifiesVar term _ _.
Proof.
constructor.
Admitted.

Instance TraverseVarIsIdentity_term : @TraverseVarIsIdentity term _ term _.
Proof.
constructor.
Admitted.

Instance TraverseVarInjective_ty : @TraverseVarInjective ty _ ty _.
Proof.
constructor.
Admitted.

Instance TraverseFunctorial_ty : @TraverseFunctorial ty _ ty _.
Proof.
constructor.
Admitted.

Instance TraverseRelative_ty : @TraverseRelative ty ty _.
Proof.
constructor.
Admitted.

Instance TraverseIdentifiesVar_ty : @TraverseIdentifiesVar ty _ _.
Proof.
constructor.
Admitted.

Instance TraverseVarIsIdentity_ty : @TraverseVarIsIdentity ty _ ty _.
Proof.
constructor.
Admitted.

Lemma j_index_monotonic: forall n E t T, j n E t T -> forall m, m >= n -> j m E t T.
Proof.
Admitted.

Instance TraverseVarInjective_term : @TraverseVarInjective term _ term _.
Proof.
constructor.
prove_traverse_var_injective.
