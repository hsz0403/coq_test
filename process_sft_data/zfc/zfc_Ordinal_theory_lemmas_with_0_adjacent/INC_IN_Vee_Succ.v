Require Export Plump.
Definition PI1 (A : Type) (P : A -> Type) (c : depprod A P) := match c with | dep_i a p => a end.
Definition PI2 (A : Type) (P : A -> Type) (c : depprod A P) := match c return (P (PI1 A P c)) with | dep_i a p => p end.
Hint Resolve IN_Power_INC: zfc.
Hint Resolve Ord_Succ: zfc.
Inductive depprod1 (A : Type) (P : A -> Type) : Type := dep_i1 : forall x : A, P x -> depprod1 A P.
Definition PI11 (A : Type) (P : A -> Type) (c : depprod1 A P) := match c with | dep_i1 a p => a end.
Definition PI21 (A : Type) (P : A -> Type) (c : depprod1 A P) := match c return (P (PI11 A P c)) with | dep_i1 a p => p end.

Lemma INC_IN_Vee_Succ : forall E L : Ens, Ord L -> INC E (Vee L) -> IN E (Vee (Succ L)).
simple induction L; intros A f HR.
intros o inc.
unfold Succ in |- *.
apply IN_Vee with (sup A f).
apply IN_P_Comp.
intros; apply Ord_sound with w1; auto with zfc.
auto with zfc.
apply INC_IN_Power; auto with zfc.
assumption.
assumption.
