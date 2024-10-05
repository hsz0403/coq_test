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

Lemma enc_conf_END t q : ~ In END (@enc_conf M t q).
Proof.
destruct t as [[ls o] rs].
unfold enc_conf.
rewrite !in_app_iff, !in_map_iff; repeat setoid_rewrite <- in_rev.
cbn.
intros H.
decompose [or] H; try lia; firstorder; try lia.
all: try (destruct x; lia).
destruct o as [[]|]; cbn in *; lia.
