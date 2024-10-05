Require Import List.
Require Import Bar.
Require Import OpenIndGoodRel.
Require Import Lt.
Require Import Wf_nat.
Require Import Inverse_Image.
Require Import Monomials.
Definition DecRel (A : Set) (R : Rel A) := forall x y : A, {R x y} + {~ R x y}.
Definition NegRel (A : Set) (R : Rel A) (x y : A) := ~ R x y.
Definition ProdRel (A B : Set) (R : Rel A) (S : Rel B) (x y : A * B) := R (fst x) (fst y) /\ S (snd x) (snd y).
Section Dickson.
Variable A B : Set.
Variable lt : Rel A.
Variable R : Rel B.
Variable wfgt : well_founded lt.
Variable declt : DecRel A lt.
Variable wR : WR B R.
Definition leq (a b : A) := ~ lt b a.
Definition GBarlR := GRBar (A * B) (ProdRel A B leq R).
Definition sndL := map (fun p : A * B => snd p).
Definition MinD := Min (A * B) (fun p q : A * B => lt (fst p) (fst q)) (ProdRel A B leq R).
Definition prod_lt (a b : A * B) := lt (fst a) (fst b).
End Dickson.
Definition jj : forall d : nat, mon d := (fix jj (d : nat) : mon d := match d as n return (mon n) with | O => n_0 | S n => c_n n 0 (jj n) end).
Definition monLift (n : nat) (p : nat * mon n) := match p with | (x, m) => c_n n x m end.

Lemma dec_lt : DecRel nat lt.
red in |- *; intros; pattern x, y in |- *.
apply nat_double_ind_set; auto with arith.
intros n; case n; auto with arith.
Admitted.

Lemma WFlem1 : well_founded prod_lt.
Admitted.

Lemma lem0 : forall (l : list (A * B)) (a : A * B), ExistsL B (fun x : B => R x (snd a)) (sndL l) -> MinD l -> GBarlR (a :: l).
intros l; elim l; simpl in |- *; auto.
intros a H' H'0; inversion H'.
intros a l0 H' a0 H'0 H'1; inversion H'0.
simpl in H0; simpl in H1; simpl in H.
case (declt (fst a0) (fst a)); intros LtE.
change (GBarlR ((a0 :: nil) ++ (a :: nil) ++ l0)) in |- *; auto.
red in |- *; apply monGRBar; simpl in |- *; auto.
inversion H'1; auto.
red in |- *; red in |- *; apply Base.
apply FoundG.
apply FoundE.
unfold ProdRel in |- *; split; auto.
simpl in H0; simpl in H1; simpl in H.
change (GBarlR ((a0 :: nil) ++ (a :: nil) ++ l0)) in |- *; auto.
red in |- *; apply monGRBar; simpl in |- *; auto.
inversion H'1; simpl in |- *; auto.
Admitted.

Lemma lem1aux : forall l : list B, GoodR B R l -> forall us : list (A * B), l = sndL us -> MinD us -> GBarlR us.
intros l; elim l; auto.
intros H'; inversion H'.
intros a l0 H' H'0; inversion H'0; auto.
intros us; elim us; simpl in |- *; auto.
intros; discriminate.
intros a1 l2 H'1 H'2 H'3; inversion H'2.
apply lem0; auto.
rewrite <- H3; rewrite <- H4; auto.
inversion H'3; auto.
intros us; elim us; unfold sndL in |- *; simpl in |- *; auto.
intros; discriminate.
intros a1 l2 H'1 H'2 H'3; inversion H'2.
change (GBarlR (nil ++ (a1 :: nil) ++ l2)) in |- *.
red in |- *; apply monGRBar; simpl in |- *; auto.
apply H'; auto.
Admitted.

Lemma lem1 : forall us : list (A * B), GoodR B R (sndL us) -> MinD us -> GBarlR us.
intros us H' H'0.
Admitted.

Lemma keylem : forall bs : list B, GRBar B R bs -> forall us : list (A * B), bs = sndL us -> MinD us -> GBarlR us.
intros bs H'; elim H'; auto.
intros l H'0 us H'1 H'2.
apply lem1; auto.
rewrite <- H'1; auto.
intros l H'0 H'1 us H'2 H'3; red in |- *.
apply OpenInd with (lt := prod_lt); auto.
exact WFlem1.
intros a H'4.
apply H'1 with (a := snd a); auto.
Admitted.

Lemma keylem_cor : WR (A * B) (ProdRel A B leq R).
red in |- *; apply keylem with (bs := nil (A:=B)); auto.
red in |- *; auto.
Admitted.

Lemma leq2le : forall a b : nat, leq nat lt a b -> a <= b.
intros.
case (le_or_lt a b).
auto.
intro.
unfold leq in H.
unfold not in H.
Admitted.

Theorem jjProp1 : forall (d : nat) (m : mon d), d = 0 -> m = jj d.
intros d m; elim m.
simpl in |- *; auto.
Admitted.

Theorem jjProp2 : jj 0 = n_0.
Admitted.

Theorem nat_double_ind_set : forall R : nat -> nat -> Set, (forall n : nat, R 0 n) -> (forall n : nat, R (S n) 0) -> (forall n m : nat, R n m -> R (S n) (S m)) -> forall n m : nat, R n m.
Proof.
simple induction n; simple induction m; auto.
