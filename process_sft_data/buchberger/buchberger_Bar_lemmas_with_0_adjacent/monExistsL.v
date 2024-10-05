Require Import List.
Definition Pred (A : Set) := A -> Prop.
Definition Rel (A : Set) := A -> A -> Prop.
Inductive ExistsL (A : Set) (P : Pred A) : list A -> Set := | FoundE : forall (a : A) (l : list A), P a -> ExistsL A P (a :: l) | SearchE : forall (a : A) (l : list A), ExistsL A P l -> ExistsL A P (a :: l).
Hint Resolve FoundE SearchE : core.
Hint Resolve monExistsL1 : core.
Hint Resolve monExistsL : core.
Inductive GoodR (A : Set) (R : Rel A) : list A -> Set := | FoundG : forall (a : A) (l : list A), ExistsL A (fun x : A => R x a) l -> GoodR A R (a :: l) | SearchG : forall (a : A) (l : list A), GoodR A R l -> GoodR A R (a :: l).
Hint Resolve FoundG SearchG : core.
Hint Resolve monGoodR1 : core.
Hint Resolve monGoodR : core.
Inductive Bar (A : Set) (P : list A -> Set) : list A -> Set := | Base : forall l : list A, P l -> Bar A P l | Ind : forall l : list A, (forall a : A, Bar A P (a :: l)) -> Bar A P l.
Hint Resolve Base Ind : core.
Definition GRBar (A : Set) (R : Rel A) := Bar A (GoodR A R).
Definition WR (A : Set) (R : Rel A) := GRBar A R nil.
Hint Unfold GRBar WR : core.
Hint Resolve consGRBar : core.
Hint Resolve monGRBar : core.
Section lems.
Variable trm : Set.
Variable tdiv : trm -> trm -> Prop.
Definition Bad (M : list trm) := GoodR trm tdiv M -> False.
End lems.

Lemma monExistsL : forall (A : Set) (P : Pred A) (xs bs cs : list A), ExistsL A P (xs ++ bs) -> ExistsL A P (xs ++ cs ++ bs).
intros A P xs; elim xs; simpl in |- *; auto.
intros a l H' bs cs H'0; inversion H'0; auto.
