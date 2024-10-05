Require Import Undecidability.Shared.Libs.PSL.Base Lia.
Fixpoint natsLess n : list nat := match n with 0 => [] | S n => n :: natsLess n end.
Fixpoint sumn (A:list nat) := match A with [] => 0 | a::A => a + sumn A end.
Hint Rewrite sumn_app : list.
Definition maxl := fold_right max 0.

Lemma sumn_rev A : sumn A = sumn (rev A).
Proof.
enough (H:forall B, sumn A + sumn B = sumn (rev A++B)).
{
specialize (H []).
cbn in H.
autorewrite with list in H.
cbn in H.
lia.
}
induction A as [|a A];intros B.
reflexivity.
cbn in *.
specialize (IHA (a::B)).
autorewrite with list in *.
cbn in *.
lia.
