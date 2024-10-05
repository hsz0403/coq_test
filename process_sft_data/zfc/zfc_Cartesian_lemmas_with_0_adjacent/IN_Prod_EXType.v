Require Import Sets.
Require Import Axioms.
Definition Couple (E E' : Ens) := Paire (Sing E) (Paire Vide (Sing E')).
Definition Prod (E E' : Ens) : Ens := match E, E' with | sup A f, sup A' f' => sup _ (fun c : prod_t A A' => match c with | pair_t a a' => Couple (f a) (f' a') end) end.
Hint Resolve Paire_sound_left Paire_sound_right: zfc.

Theorem IN_Prod_EXType : forall E E' E'' : Ens, IN E'' (Prod E E') -> EXType _ (fun A : Ens => EXType _ (fun B : Ens => EQ (Couple A B) E'')).
simple induction E; intros A f r; simple induction E'; intros A' f' r'.
intros; elim (IN_EXType (Prod (sup A f) (sup A' f')) E'').
simple induction x.
intros; exists (f a); exists (f' b); auto with zfc.
auto with zfc.
