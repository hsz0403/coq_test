Set Implicit Arguments.
Require Import List.
From Undecidability.HOU Require Import std.std.
Import ListNotations.
Set Default Proof Using "Type".
Notation symbol := bool.
Notation word := (list symbol).
Notation card := (word * word)%type.
Notation stack := (list card).
Notation hd := fst.
Notation tl := snd.
Notation heads S := (map hd S).
Notation tails S := (map tl S).
Definition PCP (S: list card) := exists (I: list nat), I ⊆ nats (|S|) /\ I <> nil /\ concat (select I (heads S)) = concat (select I (tails S)).
Definition MPCP '(c, C) := exists (I: list nat), I ⊆ nats (1 + |C|) /\ hd c ++ @concat symbol (select I (heads (c :: C))) = tl c ++ concat (select I (tails (c :: C))).
Definition PCPsimp (C: list card) := exists (C': stack), C' ⊆ C /\ C' <> nil /\ concat (heads C') = concat (tails C').
Definition MPCPsimp '(c, C) := exists (C': stack), C' ⊆ c :: C /\ hd c ++ concat (heads C') = tl c ++ concat (tails C').
Section PCPEquivalence.
Hint Resolve nth_error_Some_lt nth_error_lt_Some nats_lt lt_nats : core.
End PCPEquivalence.

Lemma MPCPsimp_MPCP c C: MPCPsimp (c,C) <-> MPCP (c,C).
Proof.
split.
+
intros [C' H].
rewrite incl_select_iff in H.
destruct H as ((I & ? & ?) & ?); subst.
exists I.
rewrite <-!select_map; intuition.
+
intros (I & H).
exists (select I (c :: C)).
rewrite incl_select_iff.
intuition eauto.
rewrite !select_map; intuition.
