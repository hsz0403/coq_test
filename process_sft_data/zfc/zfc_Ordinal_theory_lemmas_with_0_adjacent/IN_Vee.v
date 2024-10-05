Require Export Plump.
Definition PI1 (A : Type) (P : A -> Type) (c : depprod A P) := match c with | dep_i a p => a end.
Definition PI2 (A : Type) (P : A -> Type) (c : depprod A P) := match c return (P (PI1 A P c)) with | dep_i a p => p end.
Hint Resolve IN_Power_INC: zfc.
Hint Resolve Ord_Succ: zfc.
Inductive depprod1 (A : Type) (P : A -> Type) : Type := dep_i1 : forall x : A, P x -> depprod1 A P.
Definition PI11 (A : Type) (P : A -> Type) (c : depprod1 A P) := match c with | dep_i1 a p => a end.
Definition PI21 (A : Type) (P : A -> Type) (c : depprod1 A P) := match c return (P (PI11 A P c)) with | dep_i1 a p => p end.

Lemma IN_Vee : forall V W : Ens, IN W V -> forall E : Ens, INC E (Vee W) -> IN E (Vee V).
simple induction V; intros A f HR.
intros W i E inc.
change (IN E (Union (sup A (fun a : A => Power (Vee (f a)))))) in |- *.
apply IN_Union with (Power (Vee W)).
elim i; intros a h.
exists a.
apply Power_sound; apply Vee_sound; auto with zfc.
auto with zfc.
apply INC_IN_Power.
assumption.
