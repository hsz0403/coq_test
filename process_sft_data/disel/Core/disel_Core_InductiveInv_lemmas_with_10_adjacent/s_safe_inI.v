From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely.
Require FunctionalExtensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module ProtocolWithInvariant.
Section ProtocolWithInvariant.
Variable p : protocol.
Notation l := (plab p).
Notation coh := (coh p).
Variable I : dstatelet -> pred nid -> Prop.
Variable d0 : dstatelet.
Definition W := mkWorld p.
Notation toSt d := (l \\-> d).
Definition cohI := [Pred d | coh d /\ I d (nodes p d)].
Definition CohI := CohPred (CohPredMixin cohIVd cohIVs cohIDom).
Section SendInvWrapper.
Variable st : send_trans coh.
Definition send_safeI this to d m := send_safe st this to d m /\ I d (nodes p d).
Definition send_stepI: send_step_t (send_safeI) := fun this to d msg S => (@send_step _ _ st this to d msg (proj1 S)).
Definition S_inv := forall this to d msg (S : send_safe st this to d msg) b, I d (nodes p d) -> Some b = send_step S -> let: f' := upd this b (dstate d) in let: s' := (post_msg (dsoup d) (Msg (TMsg (t_snd st) msg) this to true)).1 in let: d' := DStatelet f' s' in (forall z, z == this = false -> getLocal z d' = getLocal z d) -> I d' (nodes p d').
Hypothesis HIstep : S_inv.
Definition snd_transI := SendTrans s_safe_cohI s_safe_inI s_safe_defI s_step_cohI.
End SendInvWrapper.
Section ReceiveInvWrapper.
Variable rt : receive_trans coh.
Definition receive_stepI: receive_step_t CohI := fun this from m d C pf => receive_step rt from m (proj1 C) pf.
Definition R_inv := forall d from this i (C : coh d) m (pf: this \in nodes p d), I d (nodes p d) -> find i (dsoup d) = Some (Msg m from this true) -> this \in dom (dstate d) -> msg_wf rt C this from m -> tag m = t_rcv rt -> let: loc' := receive_step rt from m C pf in let: s'' := consume_msg (dsoup d) i in let: f' := upd this loc' (dstate d) in let: d' := (DStatelet f' s'') in (forall z, z == this = false -> getLocal z d' = getLocal z d) -> I d' (nodes p d').
Hypothesis HIstep : R_inv.
Notation msg_wfI := (fun d (C : CohI d) => msg_wf rt (proj1 C)).
Definition rcv_transI := @ReceiveTrans _ CohI _ msg_wfI _ r_step_cohI.
End ReceiveInvWrapper.
Structure SendInv := SI { st : send_trans coh; st_inv : S_inv st; }.
Structure ReceiveInv := RI { rt : receive_trans coh; rt_inv : R_inv rt; }.
Structure InductiveInv := II { sts : seq SendInv; rts : seq ReceiveInv; _ : map st sts = snd_trans p; _ : map rt rts = rcv_trans p }.
Definition stsI sts := map (fun stt => @snd_transI (st stt) (@st_inv stt)) sts.
Definition rtsI rts := map (fun rtt => @rcv_transI (rt rtt) (@rt_inv rtt)) rts.
Import FunctionalExtensionality.
Variable ii : InductiveInv.
Definition ProtocolWithIndInv := @Protocol _ l _ _ _ us ur.
End ProtocolWithInvariant.
Section InductiveInvConj.
Variable p : protocol.
Definition s_inv_conj (I1 I2 : dstatelet -> pred nid -> Prop) (st : send_trans (coh p)) := S_inv (fun d n => I1 d n /\ I2 d n) st.
Definition r_inv_conj (I1 I2 : dstatelet -> pred nid -> Prop) (rt : receive_trans (coh p)) := R_inv (fun d n => I1 d n /\ I2 d n) rt.
End InductiveInvConj.
End ProtocolWithInvariant.
Module PWIExports.
Section PWIExports.
Import ProtocolWithInvariant.
Definition st_helper := st_helper.
Definition cohSt := cohSt.
Definition S_inv := ProtocolWithInvariant.S_inv.
Definition R_inv := ProtocolWithInvariant.R_inv.
Definition SendInv := SendInv.
Definition SI := SI.
Definition ReceiveInv := ReceiveInv.
Definition RI := RI.
Definition InductiveInv := InductiveInv.
Definition ProtocolWithIndInv := ProtocolWithIndInv.
End PWIExports.
End PWIExports.
Export PWIExports.

Lemma cohIVd d : cohI d -> valid (dstate d).
Proof.
Admitted.

Lemma cohIVs d : cohI d -> valid (dsoup d).
Proof.
Admitted.

Lemma cohIDom d : cohI d -> dom (dstate d) =i nodes p d.
Proof.
Admitted.

Lemma st_helper d : (getStatelet (toSt d) l) = d.
Proof.
Admitted.

Lemma cohSt d : coh d -> Coh W (toSt d).
Proof.
move=>C; split.
-
by apply/andP; rewrite valid_unit; split=>//; apply: validPt.
-
by apply: validPt.
-
by move=>z lc ls st; rewrite dom0.
-
by move=>z; rewrite !domPt inE.
move=>k; case B: (k \in dom (toSt d)); last first.
-
rewrite /getProtocol /getStatelet.
case: (dom_find k (toSt d))=>[->|v /find_some]; last by rewrite B.
rewrite domPt inE/= in B.
by case: (dom_find k (toSt p))=>[->|? /find_some]//; rewrite domPt inE/= B.
rewrite domPt inE/= in B; move/eqP: B=>B; subst k.
Admitted.

Lemma s_safe_cohI this to d m : send_safeI this to d m -> CohI d.
Proof.
Admitted.

Lemma s_safe_defI this to d msg : send_safeI this to d msg <-> exists b pf, @send_stepI this to d msg pf = Some b.
Proof.
move: (s_safe_def st this to d msg)=>H; split.
-
move=>S; case: (S)=>/H[b][pf]E H1; exists b.
exists (conj pf H1).
by rewrite /send_stepI (pf_irr (proj1 (conj pf H1)) pf).
Admitted.

Lemma s_step_cohI : s_step_coh_t CohI (t_snd st) send_stepI.
Proof.
have E1: (getProtocol W l) = p by rewrite /getProtocol/W/=findPt.
move/s_step_coh: (st)=>H.
move=>this to d msg [S]H1 b.
rewrite /send_stepI (pf_irr (proj1 (conj S H1)) S)=>E.
split=>//= ; first by apply: (H this to d msg S b E).
apply: (HIstep H1 E _)=>//.
Admitted.

Lemma r_step_cohI : r_step_coh_t msg_wfI (t_rcv rt) receive_stepI.
Proof.
have E1: (getProtocol W l) = p by rewrite /getProtocol/W/=findPt.
move=>d from this i C F m D N Wf T.
rewrite /receive_stepI/=.
set d' := {| dstate := upd this (receive_step rt from m (proj1 C) F) (dstate d); dsoup := consume_msg (dsoup d) i |}.
split; first by apply: (r_step_coh F D N Wf T).
-
apply: (HIstep (proj2 C) N D Wf T)=>//z N'.
Admitted.

Lemma us : uniq (map (@t_snd _ _) (stsI (sts ii))).
Proof.
case: ii=>sts rts Hs Hr; rewrite /stsI -seq.map_comp/=.
suff E: (t_snd (coh:=CohI) \o (fun stt : SendInv => snd_transI (st_inv (s:=stt)))) = fun stt => t_snd (st stt).
by rewrite E seq.map_comp; rewrite Hs; apply: snd_uniq.
Admitted.

Lemma ur : uniq (map (@t_rcv _ _) (rtsI (rts ii))).
Proof.
case: ii=>sts rts Hs Hr; rewrite /stsI -seq.map_comp/=.
suff E: (t_rcv (coh:=CohI) \o (fun rtt : ReceiveInv => rcv_transI (rt_inv (r:=rtt)))) = fun rtt => t_rcv (rt rtt).
by rewrite E seq.map_comp; rewrite Hr; apply: rcv_uniq.
Admitted.

Lemma stIn (s : SendInv) : s \In (sts ii) -> (snd_transI (@st_inv s)) \In (snd_trans ProtocolWithIndInv).
Proof.
Admitted.

Lemma rtIn (r : ReceiveInv) : r \In (rts ii) -> (rcv_transI (@rt_inv r)) \In (rcv_trans ProtocolWithIndInv).
Proof.
Admitted.

Lemma getInvSendTrans st z to msg s1 h : st \In (snd_trans ProtocolWithIndInv) -> forall (S : send_safe st z to (getStatelet s1 (plab p)) msg), Some h = send_step S -> exists st', [/\ st' \In get_st (mkWorld p) (plab p), t_snd st' = t_snd st, all_hooks_fire (mkWorld p) (plab p) (t_snd st') s1 z msg to & exists S': (send_safe st' z to (getStatelet s1 (plab p)) msg), Some h = send_step S'].
Proof.
simpl; case: ii=>sts rts HS HR/=; rewrite /stsI.
case/Mem_map_inv; case=>st' stI/= [->]H1; case=>S Is E.
rewrite /get_st/InMem!prEq; exists st'.
split=>//.
-
by rewrite -HS/=; apply: (Mem_map ProtocolWithInvariant.st H1).
rewrite/send_step/=/Transitions.send_step/=/send_stepI in E.
-
move=>??? F.
apply sym_eq in F.
move: F.
by move/find_some; rewrite dom0.
Admitted.

Lemma s_inv_conjC I1 I2 st : s_inv_conj I1 I2 st <-> s_inv_conj I2 I1 st.
Proof.
Admitted.

Lemma s_inv_conjA I1 I2 I3 st : s_inv_conj I1 (fun d n => I2 d n /\ I3 d n) st <-> s_inv_conj (fun d n => I1 d n /\ I2 d n) I3 st.
Proof.
Admitted.

Lemma s_safe_inI this to d m : send_safeI this to d m -> this \in nodes p d /\ to \in nodes p d.
Proof.
by case=>/s_safe_in.
