Set Implicit Arguments.
Require Export Coq.Program.Equality.
Require Import Dblib.DblibTactics.
Require Import Dblib.DeBruijn.
Require Import Dblib.Environments.
Inductive term := | TVar: nat -> term | TAbs: term -> term | TApp: term -> term -> term | TTyAbs: term -> term | TTyApp: term -> term.
Instance Var_term : Var term := { var := TVar (* avoid eta-expansion *) }.
Fixpoint traverse_term (f : nat -> nat -> term) l t := match t with | TVar x => f l x | TAbs t => TAbs (traverse_term f (1 + l) t) | TApp t1 t2 => TApp (traverse_term f l t1) (traverse_term f l t2) | TTyAbs t => TTyAbs (traverse_term f l t) | TTyApp t => TTyApp (traverse_term f l t) end.
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
Inductive red : term -> term -> Prop := | RedBeta: forall t1 t2, red (TApp (TAbs t1) t2) (subst t2 0 t1) | RedTyBeta: forall t, red (TTyApp (TTyAbs t)) t | RedContextTAbs: forall t1 t2, red t1 t2 -> red (TAbs t1) (TAbs t2) | RedContextTAppLeft: forall t1 t2 t, red t1 t2 -> red (TApp t1 t) (TApp t2 t) | RedContextTAppRight: forall t1 t2 t, red t1 t2 -> red (TApp t t1) (TApp t t2) | RedContextTTyAbs: forall t1 t2, red t1 t2 -> red (TTyAbs t1) (TTyAbs t2) | RedContextTTyApp: forall t1 t2, red t1 t2 -> red (TTyApp t1) (TTyApp t2).
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
Inductive j : env ty -> term -> ty -> Prop := | JVar: forall E x T, lookup x E = Some T -> j E (TVar x) T | JAbs: forall E t T1 T2, j (insert 0 T1 E) t T2 -> j E (TAbs t) (TyArrow T1 T2) | JApp: forall E t1 t2 T1 T2, j E t1 (TyArrow T1 T2) -> j E t2 T1 -> j E (TApp t1 t2) T2 | JTyAbs: forall E t T, j (map (shift 0) E) t T -> j E (TTyAbs t) (TyForall T) | JTyApp: forall E t T U U', j E t (TyForall T) -> (* an explicit equality facilitates the use of this axiom by [eauto] *) subst U 0 T = U' -> j E (TTyApp t) U'.
Hint Constructors j : j.
Ltac j_inversion := match goal with | h: j _ (TAbs _) _ |- _ => inversion h; clear h; subst | h: j _ (TTyAbs _) _ |- _ => inversion h; clear h; subst end.

Instance TraverseVarInjective_term : @TraverseVarInjective term _ term _.
Proof.
constructor.
Admitted.

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

Lemma term_weakening: forall E t T, j E t T -> forall x U E', insert x U E = E' -> j E' (shift x t) T.
Proof.
Admitted.

Lemma type_weakening: forall E t T, j E t T -> forall x E' T', map (shift x) E = E' -> shift x T = T' -> j E' t T'.
Proof.
Admitted.

Lemma term_substitution: forall E x t2 T1 T2, j (insert x T1 E) t2 T2 -> forall t1, j E t1 T1 -> j E (subst t1 x t2) T2.
Proof.
do 5 intro; intro h; dependent induction h; intros; simpl_subst_goal; try ( econstructor; eauto using term_weakening, type_weakening with insert_insert map_insert ).
unfold subst_idx.
Admitted.

Lemma type_substitution: forall E t T, j E t T -> forall U x E' T', map (subst U x) E = E' -> subst U x T = T' -> j E' t T'.
Proof.
Admitted.

Lemma type_preservation: forall t1 t2, red t1 t2 -> forall E T, j E t1 T -> j E t2 T.
Proof.
induction 1; intros ? ? h; dependent destruction h; subst; eauto with j.
j_inversion.
eauto using term_substitution.
j_inversion.
Admitted.

Instance TraverseVarIsIdentity_ty : @TraverseVarIsIdentity ty _ ty _.
Proof.
constructor.
prove_traverse_var_is_identity.
