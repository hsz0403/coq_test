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

Lemma with_inv_step pr I (ii : InductiveInv pr I) z s1 s2: s1 \In Coh (mkWorld (ProtocolWithIndInv ii)) -> network_step (mkWorld pr) z s1 s2 -> network_step (mkWorld (ProtocolWithIndInv ii)) z s1 s2.
Proof.
move=>C'; move: (with_inv_coh C')=>C.
case; first by case=>_<-; apply: Idle.
move=>l st Hs to msg h H1 H2 _ S A E ->/=.
have Y : l = plab pr by rewrite -(cohD C) domPt inE/= in H2; move/eqP:H2.
subst l; move: st Hs H1 S E A; rewrite /get_st/InMem!prEq/==>st Hs H1 S E A.
suff X: exists st', [/\ st' \In get_st (mkWorld (ProtocolWithIndInv ii)) (plab pr), t_snd st' = t_snd st, all_hooks_fire (mkWorld (ProtocolWithIndInv ii)) (plab pr) (t_snd st') s1 z msg to & exists S': (send_safe st' z to (getStatelet s1 (plab pr)) msg), Some h = send_step S'].
case:X=>st'[Hs']Et A'[S']E'; rewrite -Et.
move: (with_inv_nodes ii (plab pr)); rewrite !prEq=>P.
by rewrite -P in H1; apply: (SendMsg (to:=to)(this:=z)(b:=h)(msg:=msg) Hs').
rewrite -(with_inv_labE ii)/get_st/InMem!prEq.
case: ii (@stIn _ _ ii) C' =>sts rts HS HR/= Hi C'.
rewrite -HS in Hs; move/Mem_map_inv: Hs=>[[st' stI]]/=[Es]Si; subst st'.
have G: I (getStatelet s1 (plab pr)) (nodes pr (getStatelet s1 (plab pr))).
+
by case: C'=>_ _ _ _/(_ (plab pr)); rewrite prEq; case.
move:(Hi _ Si)=>/={Hi Si}Hi; exists (@snd_transI pr I st stI); split=>//=.
rewrite /send_safeI /send_stepI/=.
by exists (conj S G); rewrite (pf_irr (proj1 (conj S G)) S).
move=>l rt Hr i from H1 H2 C1 msg E[F]Hw/=.
have Y : l = plab pr by rewrite -(cohD C) domPt inE/= in H2; move/eqP:H2.
subst l; move: rt Hr H1 E (coh_s _ C1) Hw.
rewrite /get_rt/InMem/=!prEq=>rt Hr H1 E C1' Hw .
have Hi: (coh (getProtocol (mkWorld (ProtocolWithIndInv ii)) (plab pr))) (getStatelet s1 (plab pr)) by case:C'=>_ _ _/(_ (plab pr)).
have Hz : z \in nodes (getProtocol (mkWorld (ProtocolWithIndInv ii)) (plab pr)) (getStatelet s1 (plab pr)) by rewrite (with_inv_nodes ii (plab pr)) prEq.
suff X: exists rt', [/\ rt' \In get_rt (mkWorld (ProtocolWithIndInv ii)) (plab pr), tag msg = t_rcv rt', msg_wf rt' Hi z from msg & receive_step rt from msg C1' H1 = receive_step rt' from msg Hi Hz].
case:X=>rt'[Hr']E' Hw' Gr G.
have pf: (z \in nodes (getProtocol (mkWorld (ProtocolWithIndInv ii)) (plab pr)) (getStatelet s1 (plab pr))) by rewrite prEq.
move: (@ReceiveMsg _ z s1 s2 (plab pr) rt' Hr' i from pf)=>/=.
rewrite -(cohD C) /= domPt inE eqxx/=; move/(_ is_true_true C' msg E')=>X.
subst s2; apply X; split=>//; clear X.
-
by rewrite (pf_irr (coh_s (plab pr) C') Hi).
congr (upd _ _); congr {| dstate := _ ; dsoup := _ |}; congr (upd _ _).
rewrite Gr; clear E E' Hw Hw' Hr Hr' Gr rt F H2 H1 C1 C.
rewrite (pf_irr pf Hz).
by rewrite (pf_irr Hi (coh_s (plab pr) C')).
rewrite /get_rt/InMem/=; move: C1' H1 Hi Hz Hw; rewrite !prEq=>C1' H1 Hi Hz Hw.
case: ii (@rtIn _ _ ii) C' Hi Hz=>/=sts rts HS HR/= Hi C'.
rewrite -HR in Hr; move/Mem_map_inv: Hr=>[[rt' rtI]]/=[Er]Ri; subst rt'.
case=>C1'' Inv Hz.
exists (@rcv_transI pr I rt rtI); split=>//.
-
by move: (@Hi _ Ri).
rewrite /receive_step/=/receive_stepI/=/receive_step/=.
-
by rewrite -(pf_irr C1' (proj1 (conj C1'' Inv))).
by rewrite ?(pf_irr C1' (proj1 (conj C1'' Inv))) ?(pf_irr H1 Hz).
