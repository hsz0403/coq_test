Require Import Sets.
Require Import Axioms.
Definition Couple (E E' : Ens) := Paire (Sing E) (Paire Vide (Sing E')).
Definition Prod (E E' : Ens) : Ens := match E, E' with | sup A f, sup A' f' => sup _ (fun c : prod_t A A' => match c with | pair_t a a' => Couple (f a) (f' a') end) end.
Hint Resolve Paire_sound_left Paire_sound_right: zfc.

Theorem Couple_inj_left : forall A A' B B' : Ens, EQ (Couple A A') (Couple B B') -> EQ A B.
unfold Couple in |- *; simpl in |- *.
simple induction 1.
intros HA HB; elim (HA true).
intros x; elim x; simpl in |- *; simple induction 1; intros H3 H4; elim (H3 true); simpl in |- *; intros xx; elim xx; simpl in |- *; auto with zfc.
elim (H4 false); simpl in |- *.
simple induction x0; simpl in |- *.
intros.
cut (EQ (Sing B') Vide).
simpl in |- *.
simple induction 1.
intros yy; elim (yy true).
simple induction x1.
apply EQ_tran with A; auto with zfc.
intros; cut (EQ (Sing B') Vide).
simpl in |- *.
simple induction 1.
intros yy; elim (yy true).
simple induction x1.
apply EQ_tran with A; auto with zfc.
intros yy.
elim (HB true); simpl in |- *.
simple induction x0.
change (EQ (Sing A) (Sing B) -> EQ A B) in |- *; intros EE.
apply IN_Sing_EQ.
apply IN_sound_right with (Sing A); auto with zfc.
change (EQ (Paire Vide (Sing A')) (Sing B) -> EQ A B) in |- *.
intros zz.
elimtype F.
apply (not_EQ_Sing_Vide A').
apply EQ_tran with B.
apply IN_Sing_EQ.
apply IN_sound_right with (Paire Vide (Sing A')); auto with zfc.
apply EQ_sym; apply IN_Sing_EQ; apply IN_sound_right with (Paire Vide (Sing A')); auto with zfc.
