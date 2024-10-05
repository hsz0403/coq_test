From Undecidability Require TM.TM TM.SBTM.
Require Import Undecidability.Shared.FinTypeEquiv.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes Undecidability.Shared.Libs.PSL.Vectors.Vectors.
Require Undecidability.TM.Util.TM_facts.
Import VectorNotations2.
Local Open Scope vector.
Notation vector_hd v := (projT1 (destruct_vector_cons v)).
Section red.
Variable M : TM.TM (finType_CS bool) 1.
Definition num_states := (projT1 (finite_n (TM.state M))).
Definition f := (projT1 (projT2 (finite_n (TM.state M)))).
Definition g := (proj1_sig (projT2 (projT2 (finite_n (TM.state M))))).
Definition Hf := (proj1 (proj2_sig (projT2 (projT2 (finite_n (TM.state M)))))).
Definition Hg := (proj2 (proj2_sig (projT2 (projT2 (finite_n (TM.state M)))))).
Definition conv_move : TM.move -> SBTM.move := fun m => match m with TM.Lmove => SBTM.Lmove | TM.Nmove => SBTM.Nmove | TM.Rmove => SBTM.Rmove end.
Definition conv_state : TM.state M -> Fin.t (S num_states) := fun q => (Fin.FS (f q)).
Definition trans : Fin.t (S num_states) * option bool -> option (Fin.t (S num_states) * option bool * SBTM.move) := fun '(q, o) => Fin.caseS' q (fun _ => _) (Some (conv_state (TM.start M), None, SBTM.Nmove)) (fun q => if TM.halt (g q) then None else let '(q', vec) := TM.trans M (g q, [| o |]) in let '(w, m) := vector_hd vec in Some (conv_state q', w, conv_move m) ).
Definition conv_tape (t : Vector.t (TM.tape bool) 1) : SBTM.tape := let t := vector_hd t in match TM.current t with | Some c => (TM.Util.TM_facts.left t, Some c, TM.Util.TM_facts.right t) | None => (TM.Util.TM_facts.left t, None, TM.Util.TM_facts.right t) end.
End red.
Require Undecidability.TM.TM Undecidability.TM.SBTM.
Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.
Require Undecidability.TM.Reductions.Arbitrary_to_Binary.

Lemma red_correct1 q q' t t' : TM.eval M q t q' t' -> SBTM.eval (SBTM.Build_SBTM num_states trans) (conv_state q) (conv_tape t) (conv_state q') (conv_tape t').
Proof.
induction 1.
+
eapply SBTM.eval_halt.
cbn.
now rewrite Hg, H.
+
TM_facts.destruct_tapes.
cbn in *.
rewrite <- current_red in H0.
destruct TM.trans eqn:E.
inv H0.
destruct h0 as (w, m).
eapply SBTM.eval_step with (q' := conv_state q') (w := w) (m := conv_move m).
cbn.
rewrite Hg, H, E.
destruct destruct_vector_cons as (? & ? & ?), x; cbn.
inv e.
reflexivity.
now rewrite wr_red, mv_red.
