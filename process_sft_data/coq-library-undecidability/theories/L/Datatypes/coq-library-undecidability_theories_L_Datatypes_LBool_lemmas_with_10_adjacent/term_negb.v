From Undecidability.L Require Export Util.L_facts.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
MetaCoq Run (tmGenEncode "bool_enc" bool).
Hint Resolve bool_enc_correct : Lrewrite.
Instance term_negb : computableTime' negb (fun _ _ => (4,tt)).
Proof.
extract.
solverec.
Instance term_andb : computableTime' andb (fun _ _ => (1,fun _ _ => (4,tt))).
Proof.
extract.
solverec.
Instance term_orb : computableTime' orb (fun _ _ => (1,fun _ _ => (4,tt))).
Proof.
extract.
solverec.
Definition c__sizeBool := 4.
Definition OmegaLift := lam Omega.
Hint Resolve OmegaLift_proc : LProc.
Import L_Notations.
Definition trueOrDiverge := lam (var 0 I OmegaLift I).
Hint Resolve trueOrDiverge_proc : LProc.
Hint Resolve trueOrDiverge_true : Lrewrite.

Instance term_andb : computableTime' andb (fun _ _ => (1,fun _ _ => (4,tt))).
Proof.
extract.
Admitted.

Instance term_orb : computableTime' orb (fun _ _ => (1,fun _ _ => (4,tt))).
Proof.
extract.
Admitted.

Lemma size_bool (b : bool) : size(enc b) <= c__sizeBool.
Proof.
Admitted.

Lemma size_bool_enc (b:bool): size (enc b) = if b then 4 else 3.
Proof.
Admitted.

Lemma OmegaLift_proc : proc OmegaLift.
Proof.
unfold OmegaLift.
Admitted.

Lemma trueOrDiverge_proc : proc trueOrDiverge.
Proof.
unfold trueOrDiverge.
Admitted.

Lemma trueOrDiverge_true : trueOrDiverge (enc true) >(4) I.
Proof.
unfold trueOrDiverge.
cbv - [pow].
Admitted.

Lemma trueOrDiverge_eval t b: trueOrDiverge (enc b) ⇓ t -> b = true.
Proof.
destruct b.
easy.
unfold trueOrDiverge.
intros (R&l).
edestruct Omega_diverge with (t:=t).
assert (H':t == Omega).
{
rewrite <- R.
apply star_equiv.
unfold enc;cbn.
etransitivity.
now Lbeta.
apply step_star.
constructor.
}
Admitted.

Instance term_negb : computableTime' negb (fun _ _ => (4,tt)).
Proof.
extract.
solverec.
