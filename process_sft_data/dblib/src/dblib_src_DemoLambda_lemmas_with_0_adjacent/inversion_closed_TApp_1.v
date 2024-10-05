Set Implicit Arguments.
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
Inductive red : term -> term -> Prop := | RedBeta: forall t1 t2 t, subst t2 0 t1 = t -> red (TApp (TAbs t1) t2) t | RedContextTAbs: forall t1 t2, red t1 t2 -> red (TAbs t1) (TAbs t2) | RedContextTAppLeft: forall t1 t2 t, red t1 t2 -> red (TApp t1 t) (TApp t2 t) | RedContextTAppRight: forall t1 t2 t, red t1 t2 -> red (TApp t t1) (TApp t t2).
Inductive ty := | TyIota: ty | TyArrow: ty -> ty -> ty.
Inductive j : env ty -> term -> ty -> Prop := | JVar: forall E x T, lookup x E = Some T -> j E (TVar x) T | JAbs: forall E t T1 T2, j (insert 0 T1 E) t T2 -> j E (TAbs t) (TyArrow T1 T2) | JApp: forall E t1 t2 T1 T2, j E t1 (TyArrow T1 T2) -> j E t2 T1 -> j E (TApp t1 t2) T2.
Hint Constructors j : j.

Lemma inversion_closed_TApp_1: forall t1 t2 k, closed k (TApp t1 t2) -> closed k t1.
Proof.
intros.
inversion_closed.
assumption.
