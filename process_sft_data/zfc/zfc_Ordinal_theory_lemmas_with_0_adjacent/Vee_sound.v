Require Export Plump.
Definition PI1 (A : Type) (P : A -> Type) (c : depprod A P) := match c with | dep_i a p => a end.
Definition PI2 (A : Type) (P : A -> Type) (c : depprod A P) := match c return (P (PI1 A P c)) with | dep_i a p => p end.
Hint Resolve IN_Power_INC: zfc.
Hint Resolve Ord_Succ: zfc.
Inductive depprod1 (A : Type) (P : A -> Type) : Type := dep_i1 : forall x : A, P x -> depprod1 A P.
Definition PI11 (A : Type) (P : A -> Type) (c : depprod1 A P) := match c with | dep_i1 a p => a end.
Definition PI21 (A : Type) (P : A -> Type) (c : depprod1 A P) := match c return (P (PI11 A P c)) with | dep_i1 a p => p end.

Lemma Vee_sound : forall E1 E2 : Ens, EQ E1 E2 -> EQ (Vee E1) (Vee E2).
simple induction E1; intros A1 f1 HR1; simple induction E2; intros A2 f2 HR2.
simple induction 1; intros e1 e2.
apply INC_EQ; unfold INC in |- *.
change (forall E : Ens, IN E (Union (sup A1 (fun a1 : A1 => Power (Vee (f1 a1))))) -> IN E (Union (sup A2 (fun a2 : A2 => Power (Vee (f2 a2)))))) in |- *.
intros E i.
apply IN_sound_right with (Union (sup A1 (fun a1 : A1 => Power (Vee (f1 a1))))); try trivial with zfc.
apply Union_sound.
split.
intros a1; elim (e1 a1).
intros a2 h.
exists a2.
apply Power_sound.
apply HR1.
assumption.
intros a2; elim (e2 a2); intros a1 h; exists a1; apply Power_sound; auto with zfc.
change (forall E : Ens, IN E (Union (sup A2 (fun a2 : A2 => Power (Vee (f2 a2))))) -> IN E (Union (sup A1 (fun a1 : A1 => Power (Vee (f1 a1)))))) in |- *.
intros E i.
apply IN_sound_right with (Union (sup A2 (fun a2 : A2 => Power (Vee (f2 a2))))).
apply Union_sound.
split.
intros a2; elim (e2 a2); intros a1 h; exists a1.
apply Power_sound; auto with zfc.
intros a1; elim (e1 a1); intros a2 h; exists a2.
apply Power_sound; auto with zfc.
assumption.
