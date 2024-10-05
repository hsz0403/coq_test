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

Lemma sim_Del t : SR.rewt Del (enc_conf M t q_halt) [END].
Proof.
destruct t as [[ls o] rs].
transitivity (enc_conf M (ls, o, []) q_halt).
{
eapply rewt_subset.
2:{
unfold Del.
eapply incl_appl.
reflexivity.
}
induction rs.
-
reflexivity.
-
cbn -[Nat.add].
destruct o as [ [] | ], a; (econstructor; [ eapply do_rew; [ | | eapply enc_conf_equiv ] | eapply IHrs]).
do 2 right; now left.
reflexivity.
do 3 right; now left.
reflexivity.
do 4 right; now left.
reflexivity.
do 5 right; now left.
reflexivity.
do 0 right; now left.
reflexivity.
do 1 right; now left.
reflexivity.
}
transitivity (enc_conf M ([], o, []) q_halt).
{
eapply rewt_subset.
2:{
unfold Del.
eapply incl_appr.
eapply incl_appl.
reflexivity.
}
induction ls.
-
reflexivity.
-
cbn -[Nat.add].
destruct a; (econstructor; [ eapply do_rew; [ | | ] | eapply IHls]).
all: cbn - [Nat.add].
now left.
cbn -[Nat.add].
simpl_list.
cbn -[Nat.add].
instantiate (2 := 2 :: map (fun b : bool => !! b) (rev ls)).
reflexivity.
reflexivity.
right.
now left.
cbn -[Nat.add].
simpl_list.
cbn -[Nat.add].
instantiate (2 := 2 :: map (fun b : bool => !! b) (rev ls)).
reflexivity.
reflexivity.
}
destruct o as [ [] | ]; ( eapply rewt_subset; [ | do 2 eapply incl_appr; reflexivity ]); (cbn -[Nat.add]; econstructor; [ eapply do_rew with (x := []) (y := []); simpl_list; try reflexivity; cbn; eauto | reflexivity]).
