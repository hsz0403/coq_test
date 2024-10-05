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

Lemma rev_sim_Del t q z : SR.rew Del (enc_conf M t q) z -> q = q_halt /\ (z = END \/ exists t', z = enc_conf M t' q_halt).
Proof.
intros H.
inversion H as [x y v u Hin HL HR]; subst z.
cbn -[Nat.add] in Hin.
destruct t as [[ls o] rs].
decompose [or] Hin; clear Hin.
all: try tauto.
all: try specialize H0 as [= <- <-].
all: try specialize H1 as [= <- <-].
all: cbn [app] in HL; match type of HL with | ?L = ?R => match L with context C [! ?q :: ?rs] => let ls := context C [@nil nat] in replace L with (ls ++ !q ++ rs) in HL; [ | cbn; now simpl_list] end end; eapply enc_conf_inv' in HL as (H1 & <- & H3).
1-6, 9-11: subst; destruct o as [ [] | ]; inversion H3; split; clear H3; try reflexivity.
1-6, 9: destruct rs as [ | [] rs]; inversion H2; subst; rewrite app_nil_r in *.
1-6: destruct x; inversion H1; subst.
1-6: right; (eexists (ls, None, rs) + eexists (ls, Some true, rs) + ( eexists (ls, Some false, rs))) ; cbn -[Nat.add]; now simpl_list.
4,5: subst; split; try reflexivity; right.
4,5: destruct x; inversion H1; subst; clear H1; destruct ls as [ | ? ls ]; [ now destruct x; inversion H3; clear H3 |]; cbn in H3; rewrite map_app in H3; cbn in H3; eapply app_inj_tail in H3 as [-> H3]; destruct b; inversion H3; exists (ls, o, rs); cbn; now simpl_list.
all: destruct x; inversion H1; subst; clear H1; cbn; eauto.
1,3,5: destruct ls as [ | []]; cbn in H4; [ destruct x; inversion H4 | | ]; rewrite map_app in H4; eapply app_inj_tail in H4 as [H4 [=]].
1,2: destruct rs as [ | []]; inversion H2; eauto.
