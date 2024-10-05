Require Import List Lia.
Require Import Undecidability.TM.SBTM.
Require Undecidability.StringRewriting.SR.
Require Import Undecidability.StringRewriting.Util.Definitions.
Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.StringRewriting.Reductions.HaltSBTMu_to_SRH.
Import ListNotations.
Set Default Proof Using "Type".
Section FixM.
Variable M : SBTM.
Notation END := 0.
Notation X := 1.
Notation "⦇" := 2.
Notation "⦈" := 3.
Notation tt := 4.
Notation ff := 5.
Notation "!! b" := (if b then tt else ff) (at level 1).
Notation "! p" := (@enc_state M p) (at level 1).
Variable q_halt : state M.
Definition all_symsX {B} f : list B := [f X ; f tt ; f ff].
Definition Del := concat (all_symsX (fun c => all_syms (fun a => ([!q_halt; c ; a], [!q_halt ; c])))) ++ all_syms (fun a => ([a; !q_halt], [!q_halt])) ++ all_symsX (fun c => ( [⦇; !q_halt; c ; ⦈], [END])).
End FixM.

Lemma backwards M t q1 q: (forall c, trans M (q,c) = None /\ (forall q', trans M (q', c) = None -> q' = q)) -> SR.rewt ((R M ++ Del M q) ++ map SR.swap (R M ++ Del M q)) (enc_conf M t q1) [0] -> exists t', eval M q1 t q t'.
Proof.
intros Hq H.
revert Hq.
remember [0] as x.
remember (enc_conf M t q1) as y.
induction H in q1, Heqy, Heqx, t |- *; subst; intros Hq.
+
edestruct enc_conf_END.
rewrite <- Heqy.
eauto.
+
rewrite map_app in H.
rewrite !rew_app_inv in H.
destruct H as [[H | H] | [H | H]].
*
eapply rev_sim in H as (q' & w & m & H1 & H3).
subst.
edestruct IHrewt as (H4 & H5); [reflexivity | eauto | eauto |].
eexists.
econstructor.
all: eassumption.
*
eapply rev_sim_Del in H as [-> [H | (t' & ->)]].
--
do 2 econstructor.
eapply Hq.
--
econstructor.
econstructor.
eapply Hq.
*
eapply rev_sim_swap in H as (q' & w & m & t' & H1 & H3 & H4).
subst.
edestruct IHrewt as (H4 & H5); [reflexivity | eauto | eauto |].
inversion H5; subst; clear H5; try congruence.
rewrite H in H1.
inversion H1; subst; clear H1.
eexists.
eassumption.
*
eapply rev_sim_Del_swap in H as [ -> (t' & ->)].
do 2 econstructor.
eapply Hq.
