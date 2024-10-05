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
now rewrite <- H'.
