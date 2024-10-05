Require Export Plump.
Definition PI1 (A : Type) (P : A -> Type) (c : depprod A P) := match c with | dep_i a p => a end.
Definition PI2 (A : Type) (P : A -> Type) (c : depprod A P) := match c return (P (PI1 A P c)) with | dep_i a p => p end.
Hint Resolve IN_Power_INC: zfc.
Hint Resolve Ord_Succ: zfc.
Inductive depprod1 (A : Type) (P : A -> Type) : Type := dep_i1 : forall x : A, P x -> depprod1 A P.
Definition PI11 (A : Type) (P : A -> Type) (c : depprod1 A P) := match c with | dep_i1 a p => a end.
Definition PI21 (A : Type) (P : A -> Type) (c : depprod1 A P) := match c return (P (PI11 A P c)) with | dep_i1 a p => p end.

Lemma mon_Vee : forall E1 E2 : Ens, INC E1 E2 -> INC (Vee E1) (Vee E2).
intros E1 E2 inc; unfold INC in |- *; intros X i.
elim (IN_Vee_EXType _ _ i).
intros Y; simple induction 1; intros i1 inc1.
apply IN_Vee with Y; auto with zfc.
