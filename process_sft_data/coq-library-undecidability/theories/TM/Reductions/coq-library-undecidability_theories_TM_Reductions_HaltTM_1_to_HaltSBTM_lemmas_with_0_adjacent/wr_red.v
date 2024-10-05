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

Lemma wr_red w t : SBTM.wr w (conv_tape [| t |]) = conv_tape [| TM.wr w t |].
Proof.
unfold conv_tape.
cbn.
destruct (destruct_vector_cons [| t |]) as (? & ? & E); cbn in *.
inv E.
clear H1.
destruct (destruct_vector_cons [| _ |]) as (? & ? & E); cbn in *.
inv E.
clear H1.
destruct x eqn:E1, w eqn:E2; cbn; reflexivity.
