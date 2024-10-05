Require Import Undecidability.Shared.Libs.PSL.Base Lia.
Fixpoint natsLess n : list nat := match n with 0 => [] | S n => n :: natsLess n end.
Fixpoint sumn (A:list nat) := match A with [] => 0 | a::A => a + sumn A end.
Hint Rewrite sumn_app : list.
Definition maxl := fold_right max 0.

Lemma sumn_map_natsLess f n : sumn (map f (natsLess n)) = sumn (map (fun i => f (n - (1 + i))) (natsLess n)).
Proof.
rewrite sumn_rev.
f_equal.
rewrite <- map_rev.
rewrite <- map_map with (g:=f) (f:= fun i => (n - (1+i))).
f_equal.
induction n;intros;autorewrite with list in *.
reflexivity.
rewrite natsLess_S at 2.
cbn.
rewrite map_app.
cbn.
rewrite map_map.
cbn in IHn.
rewrite IHn.
rewrite <- minus_n_O.
reflexivity.
