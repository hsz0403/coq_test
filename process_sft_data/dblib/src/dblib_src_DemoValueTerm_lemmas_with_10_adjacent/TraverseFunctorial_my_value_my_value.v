Set Implicit Arguments.
Require Import Dblib.DblibTactics.
Require Import Dblib.DeBruijn.
Inductive my_term := | MyTValue: my_value -> my_term | MyTApp: my_term -> my_term -> my_term with my_value := | MyVVar: nat -> my_value | MyVAbs: my_term -> my_value.
Instance Var_my_value : Var my_value := { var := MyVVar }.
Fixpoint traverse_my_term (f : nat -> nat -> my_value) l t := match t with | MyTValue v => MyTValue (traverse_my_value f l v) | MyTApp t1 t2 => MyTApp (traverse_my_term f l t1) (traverse_my_term f l t2) end with traverse_my_value f l v := match v with | MyVVar x => f l x | MyVAbs t => MyVAbs (traverse_my_term f (1 + l) t) end.
Instance Traverse_my_value_my_value : Traverse my_value my_value := { traverse := traverse_my_value }.
Instance Traverse_my_value_my_term : Traverse my_value my_term := { traverse := traverse_my_term }.
Instance TraverseVarInjective_my_value_my_value : @TraverseVarInjective my_value _ my_value _.
Proof.
constructor.
apply traverse_my_value_injective.
Instance TraverseVarInjective_my_value_my_term : @TraverseVarInjective my_value _ my_term _.
Proof.
constructor.
apply traverse_my_term_injective.
Instance TraverseFunctorial_my_value_my_value : @TraverseFunctorial my_value _ my_value _.
Proof.
constructor.
apply traverse_functorial_value_value.
Instance TraverseFunctorial_my_term_my_term : @TraverseFunctorial my_value _ my_term _.
Proof.
constructor.
apply traverse_functorial_value_term.
Instance TraverseIdentifiesVar_my_value : TraverseIdentifiesVar.
Proof.
constructor.
prove_traverse_identifies_var.
Instance TraverseRelative_my_value_my_value : @TraverseRelative my_value my_value _.
Proof.
constructor.
apply traverse_relative_my_value_my_value.
Instance TraverseRelative_my_value_my_term : @TraverseRelative my_value my_term _.
Proof.
constructor.
apply traverse_relative_my_value_my_term.
Instance TraverseVarIsIdentity_my_value_my_value : @TraverseVarIsIdentity my_value _ my_value _.
Proof.
constructor.
apply traverse_my_value_var_is_identity.
Instance TraverseVarIsIdentity_my_value_my_term : @TraverseVarIsIdentity my_value _ my_term _.
Proof.
constructor.
apply traverse_my_term_var_is_identity.

Lemma traverse_my_value_injective: forall f, (forall x1 x2 l, f l x1 = f l x2 -> x1 = x2) -> forall (t1 t2 : my_value) l, traverse_var f l t1 = traverse_var f l t2 -> t1 = t2 with traverse_my_term_injective: forall f, (forall x1 x2 l, f l x1 = f l x2 -> x1 = x2) -> forall (t1 t2 : my_term) l, traverse_var f l t1 = traverse_var f l t2 -> t1 = t2.
Proof.
prove_traverse_var_injective.
Admitted.

Instance TraverseVarInjective_my_value_my_value : @TraverseVarInjective my_value _ my_value _.
Proof.
constructor.
Admitted.

Instance TraverseVarInjective_my_value_my_term : @TraverseVarInjective my_value _ my_term _.
Proof.
constructor.
Admitted.

Lemma traverse_functorial_value_value: forall f g (t : my_value) l, traverse g l (traverse f l t) = traverse (fun l x => traverse g l (f l x)) l t with traverse_functorial_value_term: forall f g (t : my_term) l, traverse g l (traverse f l t) = traverse (fun l x => traverse g l (f l x)) l t.
Proof.
prove_traverse_functorial.
Admitted.

Instance TraverseFunctorial_my_term_my_term : @TraverseFunctorial my_value _ my_term _.
Proof.
constructor.
Admitted.

Instance TraverseIdentifiesVar_my_value : TraverseIdentifiesVar.
Proof.
constructor.
Admitted.

Lemma traverse_relative_my_value_my_value: forall f g p (t : my_value) m l, (forall l x, f (l + p) x = g l x) -> m = l + p -> traverse f m t = traverse g l t with traverse_relative_my_value_my_term: forall f g p (t : my_term) m l, (forall l x, f (l + p) x = g l x) -> m = l + p -> traverse f m t = traverse g l t.
Proof.
prove_traverse_relative.
Admitted.

Instance TraverseRelative_my_value_my_value : @TraverseRelative my_value my_value _.
Proof.
constructor.
Admitted.

Instance TraverseRelative_my_value_my_term : @TraverseRelative my_value my_term _.
Proof.
constructor.
Admitted.

Lemma traverse_my_value_var_is_identity: forall f, (forall l x, f l x = var x) -> forall (t : my_value) l, traverse f l t = t with traverse_my_term_var_is_identity: forall f, (forall l x, f l x = var x) -> forall (t : my_term) l, traverse f l t = t.
Proof.
prove_traverse_var_is_identity.
Admitted.

Instance TraverseVarIsIdentity_my_value_my_value : @TraverseVarIsIdentity my_value _ my_value _.
Proof.
constructor.
Admitted.

Instance TraverseVarIsIdentity_my_value_my_term : @TraverseVarIsIdentity my_value _ my_term _.
Proof.
constructor.
Admitted.

Lemma lift_MyVAbs: forall w k t, lift w k (MyVAbs t) = MyVAbs (lift w (1 + k) t).
Proof.
intros.
simpl_lift_goal.
Admitted.

Lemma subst_MyVAbs: forall v k t, subst v k (MyVAbs t) = MyVAbs (subst (shift 0 v) (1 + k) t).
Proof.
intros.
simpl_subst_goal.
Admitted.

Instance TraverseFunctorial_my_value_my_value : @TraverseFunctorial my_value _ my_value _.
Proof.
constructor.
apply traverse_functorial_value_value.
