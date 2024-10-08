Require Import Sets.
Require Import Axioms.
Theorem Russell : forall E : Ens, (forall E' : Ens, IN E' E) -> False.
intros U HU.
cut ((fun x : Ens => IN x x -> False) (Comp U (fun x : Ens => IN x x -> False))).
intros HR.
apply HR.
apply IN_P_Comp; auto with zfc.
intros w1 w2 HF e i; apply HF; apply IN_sound_left with w2; auto with zfc; apply IN_sound_right with w2; auto with zfc.
intros H.
cut (IN (Comp U (fun x : Ens => IN x x -> False)) (Comp U (fun x : Ens => IN x x -> False))).
change ((fun x : Ens => IN x x -> False) (Comp U (fun x : Ens => IN x x -> False))) in |- *.
cut (forall w1 w2 : Ens, (IN w1 w1 -> False) -> EQ w1 w2 -> IN w2 w2 -> False).
intros ww.
exact (IN_Comp_P U (Comp U (fun x : Ens => IN x x -> False)) (fun x : Ens => IN x x -> False) ww H).
intros w1 w2 HF e i; apply HF; apply IN_sound_left with w2; auto with zfc; apply IN_sound_right with w2; auto with zfc.
assumption.
Qed.