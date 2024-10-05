Require Import Undecidability.Shared.Libs.PSL.Base Lia.
Fixpoint natsLess n : list nat := match n with 0 => [] | S n => n :: natsLess n end.
Fixpoint sumn (A:list nat) := match A with [] => 0 | a::A => a + sumn A end.
Hint Rewrite sumn_app : list.
Definition maxl := fold_right max 0.

Lemma sumn_map_add X f g (l:list X) : sumn (map (fun x => f x + g x) l) = sumn (map f l) + sumn (map g l).
Proof.
induction l;cbn;nia.
