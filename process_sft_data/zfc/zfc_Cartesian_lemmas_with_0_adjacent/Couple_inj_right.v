Require Import Sets.
Require Import Axioms.
Definition Couple (E E' : Ens) := Paire (Sing E) (Paire Vide (Sing E')).
Definition Prod (E E' : Ens) : Ens := match E, E' with | sup A f, sup A' f' => sup _ (fun c : prod_t A A' => match c with | pair_t a a' => Couple (f a) (f' a') end) end.
Hint Resolve Paire_sound_left Paire_sound_right: zfc.

Theorem Couple_inj_right : forall A A' B B' : Ens, EQ (Couple A A') (Couple B B') -> EQ A' B'.
unfold Couple in |- *; simpl in |- *.
simple induction 1; intros H1 H2.
elim (H1 false).
intros bb1; elim bb1.
intros HF.
change (EQ (Paire Vide (Sing A')) (Sing B)) in HF.
cut F.
simple induction 1.
apply (not_EQ_Vide_Sing A').
apply EQ_tran with B.
apply IN_Sing_EQ; apply IN_sound_right with (Paire Vide (Sing A')); auto with zfc.
apply EQ_sym; apply IN_Sing_EQ; apply IN_sound_right with (Paire Vide (Sing A')); auto with zfc.
change (EQ (Paire Vide (Sing A')) (Paire Vide (Sing B')) -> EQ A' B') in |- *.
intros HP; cut (EQ (Sing A') (Sing B')).
intros; auto with zfc.
cut (IN (Sing A') (Paire Vide (Sing B'))).
intros HI; elim (Paire_IN Vide (Sing B') (Sing A') HI).
intros; cut F.
simple induction 1.
apply not_EQ_Sing_Vide with A'; assumption.
trivial with zfc.
apply IN_sound_right with (Paire Vide (Sing A')); auto with zfc.
