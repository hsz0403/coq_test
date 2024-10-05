Require Import Sets.
Require Import Axioms.
Definition Couple (E E' : Ens) := Paire (Sing E) (Paire Vide (Sing E')).
Definition Prod (E E' : Ens) : Ens := match E, E' with | sup A f, sup A' f' => sup _ (fun c : prod_t A A' => match c with | pair_t a a' => Couple (f a) (f' a') end) end.
Hint Resolve Paire_sound_left Paire_sound_right: zfc.

Theorem Couple_IN_Prod : forall E1 E2 E1' E2' : Ens, IN E1' E1 -> IN E2' E2 -> IN (Couple E1' E2') (Prod E1 E2).
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2.
intros E1' E2' i1 i2.
elim (IN_EXType (sup A1 f1) E1').
intros x e1; simpl in x.
elim (IN_EXType (sup A2 f2) E2').
intros x0 e2; simpl in x.
apply IN_sound_left with (Couple (pi2 (sup A1 f1) x) (pi2 (sup A2 f2) x0)); auto with zfc.
apply EQ_tran with (Couple (pi2 (sup A1 f1) x) E2'); auto with zfc.
apply Couple_sound_right.
auto with zfc.
apply Couple_sound_left; auto with zfc.
simpl in |- *.
simpl in |- *.
exists (pair_t _ _ x x0).
simpl in |- *.
split.
simple induction x1; simpl in |- *.
exists true; simpl in |- *.
split.
simple induction x2; simpl in |- *.
exists true; auto with zfc.
exists true; auto with zfc.
simple induction y; exists true; auto with zfc.
exists false; simpl in |- *.
split.
simple induction x2.
exists true; simpl in |- *; auto with zfc.
split.
simple induction x3.
simple induction y.
exists false; auto with zfc.
simple induction y; simpl in |- *.
exists true; auto with zfc.
exists false; auto with zfc.
simple induction y; simpl in |- *.
exists true; auto with zfc.
exists false; auto with zfc.
auto with zfc.
auto with zfc.
