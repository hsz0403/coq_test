From Undecidability Require Import TM.Util.Prelim TM.Util.TM_facts.
Section Mirror.
Variable (n : nat) (sig : finType).
Definition mirror_act : (option sig * move) -> (option sig * move) := map_snd mirror_move.
Definition mirror_acts : Vector.t (option sig * move) n -> Vector.t (option sig * move) n := Vector.map mirror_act.
Variable F : finType.
Variable pM : pTM sig F n.
Definition Mirror_trans : state (projT1 pM) * Vector.t (option sig) n -> state (projT1 pM) * Vector.t (option sig * move) n := fun qsym => let (q', act) := trans qsym in (q', mirror_acts act).
Definition MirrorTM : TM sig n := {| trans := Mirror_trans; start := start (projT1 pM); halt := halt (m := projT1 pM); |}.
Definition Mirror : pTM sig F n := (MirrorTM; projT2 pM).
Definition mirrorConf : mconfig sig (state (projT1 pM)) n -> mconfig sig (state (projT1 pM)) n := fun c => mk_mconfig (cstate c) (mirror_tapes (ctapes c)).
Definition Mirror_Rel (R : pRel sig F n) : pRel sig F n := fun t '(l, t') => R (mirror_tapes t) (l, mirror_tapes t').
Definition Mirror_T (T : tRel sig n) : tRel sig n := fun t k => T (mirror_tapes t) k.
End Mirror.
Arguments Mirror : simpl never.
Arguments Mirror_Rel { n sig F } R x y /.
Arguments Mirror_T { n sig } T x y /.
Ltac smpl_TM_Mirror := once lazymatch goal with | [ |- Mirror _ ⊨ _ ] => eapply Mirror_Realise | [ |- Mirror _ ⊨c(_) _ ] => eapply Mirror_RealiseIn | [ |- projT1 (Mirror _) ↓ _ ] => eapply Mirror_Terminates end.
Smpl Add smpl_TM_Mirror : TM_Correct.

Lemma Mirror_Terminates T : projT1 pM ↓ T -> projT1 Mirror ↓ Mirror_T T.
Proof.
intros HTerm.
hnf.
intros t1 k H1.
hnf in HTerm.
specialize (HTerm (mirror_tapes t1) k H1) as (outc&H).
exists (mirrorConf outc).
apply mirror_unlift.
cbn.
now rewrite mirrorConf_involution.
