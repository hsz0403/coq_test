Require Export Plump.
Definition PI1 (A : Type) (P : A -> Type) (c : depprod A P) := match c with | dep_i a p => a end.
Definition PI2 (A : Type) (P : A -> Type) (c : depprod A P) := match c return (P (PI1 A P c)) with | dep_i a p => p end.
Hint Resolve IN_Power_INC: zfc.
Hint Resolve Ord_Succ: zfc.
Inductive depprod1 (A : Type) (P : A -> Type) : Type := dep_i1 : forall x : A, P x -> depprod1 A P.
Definition PI11 (A : Type) (P : A -> Type) (c : depprod1 A P) := match c with | dep_i1 a p => a end.
Definition PI21 (A : Type) (P : A -> Type) (c : depprod1 A P) := match c return (P (PI11 A P c)) with | dep_i1 a p => p end.

Lemma IN_Vee_EXType : forall E X : Ens, IN X (Vee E) -> EXType Ens (fun Y : Ens => IN Y E /\ INC X (Vee Y)).
simple induction E; intros A f HR X.
intros i.
change (IN X (Union (sup A (fun a : A => Power (Vee (f a)))))) in i.
elim (Union_IN _ _ i).
intros T c.
elim c; intros i1 i2.
elim i1; intros a e.
exists (f a); split.
exists a; auto with zfc.
apply IN_Power_INC.
apply IN_sound_right with T; auto with zfc.
