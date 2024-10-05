Require Export Plump.
Definition PI1 (A : Type) (P : A -> Type) (c : depprod A P) := match c with | dep_i a p => a end.
Definition PI2 (A : Type) (P : A -> Type) (c : depprod A P) := match c return (P (PI1 A P c)) with | dep_i a p => p end.
Hint Resolve IN_Power_INC: zfc.
Hint Resolve Ord_Succ: zfc.
Inductive depprod1 (A : Type) (P : A -> Type) : Type := dep_i1 : forall x : A, P x -> depprod1 A P.
Definition PI11 (A : Type) (P : A -> Type) (c : depprod1 A P) := match c with | dep_i1 a p => a end.
Definition PI21 (A : Type) (P : A -> Type) (c : depprod1 A P) := match c return (P (PI11 A P c)) with | dep_i1 a p => p end.

Lemma IN_Vee_Succ_EXType : forall E X : Ens, Ord E -> IN X (Vee (Succ E)) -> EXType _ (fun Y : Ens => INC Y E /\ Ord Y /\ INC X (Vee Y)).
intros E X o i.
elim (IN_Vee_EXType _ _ i).
intros Y; simple induction 1; intros i1 inc.
exists Y; split.
apply IN_Succ_INC; auto with zfc.
split.
auto with zfc.
apply IN_Ord_Ord with (Succ E); auto with zfc.
auto with zfc.
