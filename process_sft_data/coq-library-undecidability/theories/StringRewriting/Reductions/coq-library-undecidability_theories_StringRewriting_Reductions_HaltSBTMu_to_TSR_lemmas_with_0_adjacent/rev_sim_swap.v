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

Lemma rev_sim_swap t q z : SR.rew (map SR.swap (R M)) (enc_conf M t q) z -> exists q' t' w m, trans M (q', curr t') = Some (q, w, m) /\ t = mv m (wr w t') /\ z = enc_conf M t' q'.
Proof.
intros H.
inversion H as [x y v u Hin HL HR]; subst z.
eapply in_map_iff in Hin as ([? ?] & [= -> ->] & Hin).
destruct t as [[ls o] rs].
eapply in_flat_map in Hin as (q_ & _ & Hq2).
unfold rules in Hq2.
rewrite ! in_app_iff in Hq2.
destruct Hq2 as [ Hq2 | [Hq2 | Hq2]].
all: destruct (trans M (q_, _)) as [ [[q' w] m] | ] eqn:Etrans; try destruct m eqn:Em; try destruct w as [[] | ] eqn:Ew; cbn -[Nat.add] in Hq2.
all: match type of Etrans with trans _ (_, ?c) = _ => (eapply help_exists1; exists c, q_, w, m) || exfalso end; rewrite ?Em, ?Ew; cbn [curr].
all: repeat match type of Hq2 with _ \/ _ => destruct Hq2 as [Hq2 | Hq2] end; inversion Hq2; subst u v; clear Hq2; cbn -[Nat.add].
all: try eapply help_exists2.
all: cbn [app] in HL; match type of HL with | ?L = ?R => match L with context C [! ?q :: ?c :: ?rs] => let ls := context C [@nil nat] in replace L with (ls ++ !q ++ [c] ++ rs) in HL; [ | cbn; now simpl_list] end end.
all: match type of HL with _ = enc_conf _ (?ls,?o,?rs) ?q => let H1 := fresh "H" in let H2 := fresh "H" in let H3 := fresh "H" in let H4 := fresh "H" in let HH := fresh "H" in eapply enc_conf_inv in HL as (H1 & -> & H3 & H4); try rewrite H4 in *; destruct o as [ [] | ]; inversion H3; clear H3; cbn in H1; rewrite ?app_nil_r in H1; subst; split ; [ eassumption | ] end.
all: try now (try (destruct rs as [ | [] rs]; cbn in H3; inversion H3; subst); destruct x; try (now inversion H0); cbn in H0; eapply cons_inj in H0 as [HH H0]; try rewrite HH in *; clear HH; [ destruct ls as [ | ? ls _ ] using rev_ind; cbn in H0; inversion H0; [ eexists [], _; split; reflexivity | exfalso; rewrite rev_app_distr in H0; cbn in H0; inversion H0 ] | destruct ls as [ | [] ls ]; cbn in H0; destruct x; inversion H0; rewrite map_app in H0; eapply app_inj_tail in H0 as []; lia ]).
all: try now ( try (destruct rs as [ | [] rs]; cbn in H3; inversion H3; subst); destruct x; try (now inversion H0); cbn in H0; eapply cons_inj in H0 as [HH H0]; try rewrite HH in *; clear HH; destruct ls; cbn in H0; try (rewrite map_app in H0; eapply app_inj_tail in H0 as [H0 H1]); [ destruct x; inversion H0 | destruct b; inversion H1 ; now ((eexists _, (_ :: _) + eexists _, []); split; try reflexivity; subst; cbn -[Nat.add]; now simpl_list)]).
all: try now (try (destruct rs as [ | [] rs]; cbn in H3; inversion H3; subst); now ((eexists (_ :: ls), rs + eexists _, (_ :: _) + eexists _, [] + eexists _, _ + eexists (_ :: ls), rs); split; try reflexivity; cbn; now simpl_list)).
