From Undecidability.L Require Export Util.L_facts.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
MetaCoq Run (tmGenEncode "unit_enc" unit).
Hint Resolve unit_enc_correct : Lrewrite.
Lemma size_unit_enc : size(enc tt) = 2.
Proof.
cbv[enc registered_unit_enc size unit_enc].
lia.
Qed.