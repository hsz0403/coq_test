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

Lemma monGoodR1 : forall (A : Set) (R : Rel A) (xs bs : list A), GoodR A R bs -> GoodR A R (xs ++ bs).
Admitted.

Lemma monGoodR : forall (A : Set) (R : Rel A) (xs bs cs : list A), GoodR A R (xs ++ bs) -> GoodR A R (xs ++ cs ++ bs).
intros A R xs bs cs; elim xs; simpl in |- *; auto.
Admitted.

Lemma subPredExistsL : forall (A B : Set) (P : Pred A) (S : Pred B) (f : A -> B), (forall a : A, P a -> S (f a)) -> forall l : list A, ExistsL A P l -> ExistsL B S (map f l).
Admitted.

Lemma subRelGoodR : forall (A B : Set) (R : Rel A) (S : Rel B) (f : A -> B), (forall a b : A, R a b -> S (f a) (f b)) -> forall l : list A, GoodR A R l -> GoodR B S (map f l).
intros A B R S f H' l H'0; elim H'0; simpl in |- *; auto.
intros a l0 H'1; apply FoundG; auto.
Admitted.

Lemma subRelGRBar : forall (A B : Set) (R : Rel A) (S : Rel B) (f : A -> B), (forall a b : A, R a b -> S (f a) (f b)) -> (forall b : B, {a : A | b = f a}) -> forall l : list A, GRBar A R l -> GRBar B S (map f l).
intros A B R S f H' H'0 l H'1; elim H'1; simpl in |- *; auto.
intros l0 H'2.
red in |- *; apply Base; auto.
unfold GRBar in |- *.
apply subRelGoodR with (R := R); auto.
intros l0 H'2 H'3; red in |- *; apply Ind; auto.
intros a; case (H'0 a); auto.
intros x H'4; rewrite H'4; auto.
Admitted.

Lemma consGRBar : forall (A : Set) (R : Rel A) (l : list A), GRBar A R l -> forall a : A, GRBar A R (a :: l).
Admitted.

Lemma nilGRBar : forall (A : Set) (R : Rel A), GRBar A R nil -> forall l : list A, GRBar A R l.
Admitted.

Lemma monGRBarAux : forall (A : Set) (R : Rel A) (l : list A), GRBar A R l -> forall xs bs cs : list A, l = xs ++ cs -> GRBar A R (xs ++ bs ++ cs).
intros A R l H'; elim H'; auto.
intros l0 H'0 xs bs cs H'1; red in |- *; rewrite H'1 in H'0; auto.
intros l0 H'0 H'1 xs bs cs H'2; rewrite H'2 in H'1; auto.
red in |- *; apply Ind.
intros a.
change (Bar A (GoodR A R) ((a :: xs) ++ bs ++ cs)) in |- *.
Admitted.

Lemma monGRBar : forall (A : Set) (R : Rel A) (xs bs cs : list A), GRBar A R (xs ++ cs) -> GRBar A R (xs ++ bs ++ cs).
intros A R xs bs cs H'.
Admitted.

Lemma tdivExists_trmHd_lem : forall (F : list trm) (f : trm), (forall g : trm, In g F -> ~ tdiv g f) -> ExistsL trm (fun g : trm => tdiv g f) F -> False.
intros F; elim F; simpl in |- *; auto.
intros f H' H'0; inversion H'0; auto.
intros a l H' f H'0 H'1; inversion H'1; auto.
lapply (H'0 a); [ intro H'3; apply H'3 | idtac ]; auto.
Admitted.

Lemma tdivGoodP : forall (F : list trm) (f : trm), Bad F -> (forall g : trm, In g F -> ~ tdiv g f) -> Bad (f :: F).
intros F f H' H'0; red in |- *.
intros H'1; inversion H'1; auto.
apply tdivExists_trmHd_lem with (F := F) (f := f); auto.
