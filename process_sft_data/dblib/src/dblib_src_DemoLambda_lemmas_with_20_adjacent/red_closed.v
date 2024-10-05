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

Lemma lift_TVar: forall w k x, lift w k (TVar x) = TVar (lift w k x).
Proof.
intros.
simpl_lift_goal.
Admitted.

Lemma lift_TApp: forall w k t1 t2, lift w k (TApp t1 t2) = TApp (lift w k t1) (lift w k t2).
Proof.
Admitted.

Lemma lift_TAbs: forall w k t, lift w k (TAbs t) = TAbs (lift w (1 + k) t).
Proof.
Admitted.

Lemma subst_TVar: forall v k x, subst v k (TVar x) = subst_idx v k x.
Proof.
intros.
simpl_subst_goal.
Admitted.

Lemma subst_TApp: forall v k t1 t2, subst v k (TApp t1 t2) = TApp (subst v k t1) (subst v k t2).
Proof.
Admitted.

Lemma subst_TAbs: forall v k t, subst v k (TAbs t) = TAbs (subst (shift 0 v) (1 + k) t).
Proof.
Admitted.

Lemma red_weakening: forall t1 t2, red t1 t2 -> forall x, red (shift x t1) (shift x t2).
Proof.
Admitted.

Lemma inversion_closed_TVar: forall k x, x >= k -> closed k (TVar x) -> False.
Proof.
intros.
inversion_closed.
Admitted.

Lemma inversion_closed_TApp_1: forall t1 t2 k, closed k (TApp t1 t2) -> closed k t1.
Proof.
intros.
inversion_closed.
Admitted.

Lemma inversion_closed_TApp_2: forall t1 t2 k, closed k (TApp t1 t2) -> closed k t2.
Proof.
intros.
inversion_closed.
Admitted.

Lemma inversion_closed_TAbs: forall t k, closed k (TAbs t) -> closed (1 + k) t.
Proof.
intros.
inversion_closed.
Admitted.

Lemma weakening: forall E t T, j E t T -> forall x U E', insert x U E = E' -> j E' (shift x t) T.
Proof.
Admitted.

Lemma substitution: forall E x t2 T1 T2, j (insert x T1 E) t2 T2 -> forall t1, j E t1 T1 -> j E (subst t1 x t2) T2.
Proof.
do 5 intro; intro h; dependent induction h; intros; simpl_subst_goal; (* General rule. *) try solve [ econstructor; eauto using weakening with insert_insert ].
unfold subst_idx.
Admitted.

Lemma type_preservation: forall t1 t2, red t1 t2 -> forall E T, j E t1 T -> j E t2 T.
Proof.
induction 1; intros ? ? h; subst; dependent destruction h; eauto with j.
match goal with h: j _ (TAbs _) _ |- _ => inversion h; clear h; subst end.
Admitted.

Lemma j_closed: forall E t T, j E t T -> forall k, length E <= k -> closed k t.
Proof.
Admitted.

Lemma j_agree: forall E1 t T, j E1 t T -> forall E2 k, agree E1 E2 k -> length E1 <= k -> j E2 t T.
Proof.
Admitted.

Lemma j_empty: forall E t T, j (@empty _) t T -> j E t T.
Proof.
Admitted.

Lemma red_closed: forall t1 t2, red t1 t2 -> forall k, closed k t1 -> closed k t2.
Proof.
induction 1; intros; subst; inversion_closed; try construction_closed.
eauto using @subst_preserves_closed with typeclass_instances.
