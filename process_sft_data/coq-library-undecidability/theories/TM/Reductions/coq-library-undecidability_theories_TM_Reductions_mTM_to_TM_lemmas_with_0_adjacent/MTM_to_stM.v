From Undecidability.TM Require Import Single.StepTM Code.CodeTM TM.
Require Import Undecidability.Synthetic.Definitions.

Lemma MTM_to_stM : HaltMTM ⪯ HaltTM 1.
Proof.
unshelve eexists.
-
intros [ [n sig] M t].
eapply mk_pTM in M.
pose (ToSingleTape M).
cbn in *.
eexists.
destruct p.
exact x.
cbn.
eapply EncodeTapes.encode_tapes in t.
econstructor.
2:econstructor.
refine (midtape nil (inl START) (map inr t ++ [inl STOP])).
-
intros [ [n sig] M t].
cbn.
unfold HaltsTM.
setoid_rewrite TM_eval_iff.
intuition.
+
destruct H as (q' & t' & k & H).
assert (M ↓ (fun t' k' => t = t' /\ k' = k)).
{
intros ? ? [].
subst.
eauto.
}
eapply (ToSingleTape_Terminates' (pM := mk_pTM M)) in H0.
specialize (H0 [|midtape [] (inl START) ([inr p | p ∈ EncodeTapes.encode_tapes t] ++ [inl STOP])|]).
edestruct H0.
*
exists t, k.
repeat split; eauto.
*
destruct x as [q'' t''].
exists q'', t''.
destruct ((ToSingleTape (mk_pTM M))).
eexists.
eapply H1.
+
destruct H as (q' & t' & k & H).
cbn in *.
pose proof (ToSingleTape_Realise' (pM := mk_pTM M)).
specialize (H0 (fun t '(f,t') => exists outc k, loopM (initc M t) k = Some outc /\ ctapes outc = t')).
edestruct H0.
*
intros ? ? ? ?.
exists outc, k0.
eauto.
*
eapply H.
*
firstorder.
*
intuition.
destruct H2 as (? & ? & ? & ?).
subst.
destruct x0 as [q'' t''].
now exists q'', t'', x1.
