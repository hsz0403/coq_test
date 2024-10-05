Require Import Sets.
Require Import Axioms.
Definition Couple (E E' : Ens) := Paire (Sing E) (Paire Vide (Sing E')).
Definition Prod (E E' : Ens) : Ens := match E, E' with | sup A f, sup A' f' => sup _ (fun c : prod_t A A' => match c with | pair_t a a' => Couple (f a) (f' a') end) end.
Hint Resolve Paire_sound_left Paire_sound_right: zfc.

Theorem Couple_Prod_IN : forall E1 E2 E1' E2' : Ens, IN (Couple E1' E2') (Prod E1 E2) -> IN E1' E1 /\ IN E2' E2.
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2.
intros E1' E2' i.
elim (IN_EXType (Prod (sup A1 f1) (sup A2 f2)) (Couple E1' E2') i).
intros xx; elim xx; intros a1 a2 e.
change (EQ (Couple E1' E2') (Couple (f1 a1) (f2 a2))) in e.
cut (EQ E1' (f1 a1)).
cut (EQ E2' (f2 a2)).
intros e1 e2.
split.
apply IN_sound_left with (f1 a1); auto with zfc; simpl in |- *; exists a1; auto with zfc.
apply IN_sound_left with (f2 a2); auto with zfc; simpl in |- *; exists a2; auto with zfc.
apply Couple_inj_right with (A := E1') (B := f1 a1); auto with zfc.
apply Couple_inj_left with E2' (f2 a2); auto with zfc.
