Require Export Plump.
Definition PI1 (A : Type) (P : A -> Type) (c : depprod A P) := match c with | dep_i a p => a end.
Definition PI2 (A : Type) (P : A -> Type) (c : depprod A P) := match c return (P (PI1 A P c)) with | dep_i a p => p end.
Hint Resolve IN_Power_INC: zfc.
Hint Resolve Ord_Succ: zfc.
Inductive depprod1 (A : Type) (P : A -> Type) : Type := dep_i1 : forall x : A, P x -> depprod1 A P.
Definition PI11 (A : Type) (P : A -> Type) (c : depprod1 A P) := match c with | dep_i1 a p => a end.
Definition PI21 (A : Type) (P : A -> Type) (c : depprod1 A P) := match c return (P (PI11 A P c)) with | dep_i1 a p => p end.

Lemma ex_rk : forall E : Ens, depprod1 _ (fun L : Ens => Ord L /\ IN E (Vee L)).
simple induction E; intros A f HR.
exists (Succ (Union (sup A (fun a : A => PI11 _ _ (HR a))))).
split.
apply Ord_Succ.
apply Union_Ord.
simple induction 1; intros a h.
apply Ord_sound with (PI11 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)).
auto with zfc.
elim (PI21 _ _ (HR a)).
auto with zfc.
apply IN_Vee_Succ with (Union (sup A (fun a : A => PI11 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)))).
apply Union_Ord.
intros E'; simple induction 1; intros a c.
apply Ord_sound with (PI11 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)).
elim (PI21 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)); auto with zfc.
elim (PI21 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)); auto with zfc.
apply Union_Ord.
intros E'; simple induction 1; intros a e.
apply Ord_sound with (PI11 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)); auto with zfc.
elim (PI21 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)); auto with zfc.
auto with zfc.
unfold INC in |- *; intros E' i.
elim i; intros a e.
apply IN_sound_left with (f a); auto with zfc.
cut (INC (PI11 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)) (Union (sup A (fun a0 : A => PI11 Ens (fun L : Ens => Ord L /\ IN (f a0) (Vee L)) (HR a0))))).
intros inc.
apply (mon_Vee (PI11 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)) (Union (sup A (fun a0 : A => PI11 Ens (fun L : Ens => Ord L /\ IN (f a0) (Vee L)) (HR a0)))) inc).
elim (PI21 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)).
elim (PI21 Ens (fun L : Ens => Ord L /\ IN (f a) (Vee L)) (HR a)).
auto with zfc.
apply IN_INC_Union.
exists a; auto with zfc.
