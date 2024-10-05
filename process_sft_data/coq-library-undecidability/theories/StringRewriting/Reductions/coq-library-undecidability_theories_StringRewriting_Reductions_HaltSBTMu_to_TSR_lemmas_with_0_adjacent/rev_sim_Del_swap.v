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

Lemma rev_sim_Del_swap t q z : SR.rew (map SR.swap Del) (enc_conf M t q) z -> q = q_halt /\ exists t', z = enc_conf M t' q_halt.
Proof.
intros H.
inversion H as [x y v u Hin HL HR]; subst z.
cbn -[Nat.add] in Hin.
destruct t as [[ls o] rs].
decompose [or] Hin; clear Hin.
all: try tauto.
all: try specialize H0 as [= <- <-].
all: try specialize H1 as [= <- <-].
1-8: cbn [app] in HL; match type of HL with | ?L = ?R => match L with context C [! ?q :: ?rs] => let ls := context C [@nil nat] in replace L with (ls ++ !q ++ rs) in HL; [ | cbn; now simpl_list] end end; eapply enc_conf_inv' in HL as (H1 & <- & H3).
1-6:destruct o as [ [] | ]; inversion H3; split; subst; try clear H3; try reflexivity.
all: rewrite ?app_nil_r in *; subst.
7,8: split; [ reflexivity | ].
1: exists (ls, None, true :: rs).
2: exists (ls, None, false :: rs).
3: exists (ls, Some true, true :: rs).
4: exists (ls, Some true, false :: rs).
5: exists (ls, Some false, true :: rs).
6: exists (ls, Some false, false :: rs).
1-6: cbn -[Nat.add]; now simpl_list.
1: exists (true :: ls, o, rs); cbn; now simpl_list.
1: exists (false :: ls, o, rs); cbn; now simpl_list.
all: edestruct enc_conf_END; rewrite <- HL; eauto.
