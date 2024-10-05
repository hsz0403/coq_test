Set Implicit Arguments.
Section Acc_irrelevance.
Variable (X : Type) (R : X -> X -> Prop).
Inductive Acc_eq : forall x, Acc R x -> Acc R x -> Prop := | in_Acc_eq : forall x A1 A2, (forall y H, @Acc_eq y (A1 y H) (A2 y H)) -> @Acc_eq x (Acc_intro _ A1) (Acc_intro _ A2).
Fact Acc_eq_total x H1 H2 : @Acc_eq x H1 H2.
Proof.
revert H2.
induction H1 as [ ? ? IH ] using Acc_inv_dep.
intros []; constructor; intros; apply IH.
Qed.
Variables (P : X -> Type) (f : forall x, Acc R x -> P x) (Hf : forall x H1 H2, (forall y Hy, f (H1 y Hy) = f (H2 _ Hy)) -> f (Acc_intro x H1) = f (Acc_intro x H2)).
Theorem Acc_irrelevance x H1 H2 : @f x H1 = f H2.
Proof.
generalize (Acc_eq_total H1 H2).
induction 1 as [ x H1 H2 _ IH ].
apply Hf, IH.
Qed.
End Acc_irrelevance.