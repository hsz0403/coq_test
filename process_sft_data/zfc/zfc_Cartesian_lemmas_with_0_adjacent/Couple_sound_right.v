Require Import Sets.
Require Import Axioms.
Definition Couple (E E' : Ens) := Paire (Sing E) (Paire Vide (Sing E')).
Definition Prod (E E' : Ens) : Ens := match E, E' with | sup A f, sup A' f' => sup _ (fun c : prod_t A A' => match c with | pair_t a a' => Couple (f a) (f' a') end) end.
Hint Resolve Paire_sound_left Paire_sound_right: zfc.

Theorem Couple_sound_right : forall A B B' : Ens, EQ B B' -> EQ (Couple A B) (Couple A B').
unfold Couple in |- *; intros; auto with zfc.
