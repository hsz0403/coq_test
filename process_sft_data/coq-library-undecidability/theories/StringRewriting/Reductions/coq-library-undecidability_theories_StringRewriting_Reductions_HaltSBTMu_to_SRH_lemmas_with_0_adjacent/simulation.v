Require Import List Lia.
Require Import Undecidability.TM.SBTM.
Require Undecidability.StringRewriting.SR.
Require Import Undecidability.StringRewriting.Util.Definitions.
Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.
Import ListNotations.
Set Default Proof Using "Type".
Definition SRH' '(Rs, x, A) := exists y : list nat, SR.rewt Rs x y /\ exists a, In a A /\ In a y.
Section FixM.
Variable M : SBTM.
Notation X := 1.
Notation "⦇" := 2.
Notation "⦈" := 3.
Notation tt := 4.
Notation ff := 5.
Notation "!! b" := (if b then tt else ff) (at level 1).
Definition enc_state (q : Fin.t (S (num_states M))) := ((S ff) + proj1_sig (Fin.to_nat q)).
Notation "! p" := (enc_state p) (at level 1).
Fixpoint all_fins (n : nat) : list (Fin.t n) := match n with | 0 => nil | S n => Fin.F1 :: map Fin.FS (all_fins n) end.
Definition all_states {B} f : list B := flat_map f (all_fins (S (num_states M))).
Definition all_syms {B} f : list B := [f tt ; f ff].
Definition encode_sym (o : option bool) := match o with None => X | Some true => tt | Some false => ff end.
Definition encode_trans (c : option (state M * option bool * move)) (q : Fin.t (S (num_states M))) : option (nat * nat * nat * move) := option_map (fun '(s,o,m) => (!q, !s, encode_sym o, m)) c.
Definition rules q₁ : list (list nat * list nat):= match encode_trans (trans M (q₁, None)) q₁ with | Some (q₁, q₂, X, Lmove) => all_syms (fun l => ([l;q₁;X], [q₂;l])) ++ [([⦇;q₁;X],[⦇;q₂;X])] | Some (q₁, q₂, X, Nmove) => [([q₁;X], [q₂;X])] | Some (q₁, q₂, X, Rmove) => all_syms (fun r => ([q₁;X;r], [q₂;r])) ++ [([q₁;X;⦈],[q₂;X;⦈])] | Some (q₁, q₂, c, Lmove) => all_syms (fun l => ([l;q₁;X], [q₂;l;c])) ++ [([⦇;q₁;X],[⦇;q₂;X;c])] | Some (q₁, q₂, c, Nmove) => [([q₁;X], [q₂;c])] | Some (q₁, q₂, c, Rmove) => all_syms (fun r => ([q₁;X;r], [c;q₂;r])) ++ [([q₁;X;⦈],[c;q₂;X;⦈])] | None => [] end ++ let a := tt in match encode_trans (trans M (q₁, Some true)) q₁ with | Some (q₁, q₂, X, Lmove) => all_syms (fun l => ([l;q₁;a], [q₂;l;a])) ++ [([⦇;q₁;a],[⦇;q₂;X;a])] | Some (q₁, q₂, X, Nmove) => [([q₁;a], [q₂;a])] | Some (q₁, q₂, X, Rmove) => all_syms (fun r => ([q₁;a;r], [a;q₂;r])) ++ [([q₁;a;⦈],[a;q₂;X;⦈])] | Some (q₁, q₂, c, Lmove) => all_syms (fun l => ([l;q₁;a], [q₂;l;c])) ++ [([⦇;q₁;a],[⦇;q₂;X;c])] | Some (q₁, q₂, c, Rmove) => all_syms (fun r => ([q₁;a;r], [c;q₂;r])) ++ [([q₁;a;⦈],[c;q₂;X;⦈])] | Some (q₁, q₂, c, Nmove) => [([q₁;a], [q₂;c])] | None => [] end ++ let a := ff in match encode_trans (trans M (q₁, Some false)) q₁ with | Some (q₁, q₂, X, Lmove) => all_syms (fun l => ([l;q₁;a], [q₂;l;a])) ++ [([⦇;q₁;a],[⦇;q₂;X;a])] | Some (q₁, q₂, X, Rmove) => all_syms (fun r => ([q₁;a;r], [a;q₂;r])) ++ [([q₁;a;⦈],[a;q₂;X;⦈])] | Some (q₁, q₂, X, Nmove) => [([q₁;a], [q₂;a])] | Some (q₁, q₂, c, Lmove) => all_syms (fun l => ([l;q₁;a], [q₂;l;c])) ++ [([⦇;q₁;a],[⦇;q₂;X;c])] | Some (q₁, q₂, c, Rmove) => all_syms (fun r => ([q₁;a;r], [c;q₂;r])) ++ [([q₁;a;⦈],[c;q₂;X;⦈])] | Some (q₁, q₂, c, Nmove) => [([q₁;a], [q₂;c])] | None => [] end.
Definition R : SR.SRS nat := all_states rules.
Definition enc_conf '(ls, o, rs) (q : Fin.t (S (num_states M))) : list nat := [⦇] ++ map (fun b : bool => !!b) (rev ls) ++ [!q] ++ [encode_sym o] ++ map (fun b : bool => !!b) rs ++ [⦈].
End FixM.

Lemma simulation q1 q2 t1 t2 : eval M q1 t1 q2 t2 -> SR.rewt R (enc_conf t1 q1) (enc_conf t2 q2).
Proof.
induction 1.
-
econstructor.
-
econstructor.
2:eassumption.
clear - H.
destruct t as [[ls o] rs].
cbn in H.
eapply rew_subset with (2 := @rules_incl q).
unfold rules.
destruct o as [ [] | ] eqn:Eo; rewrite H; clear H.
1: eapply rew_subset; [ | eapply incl_appr, incl_appl, incl_refl ].
2: eapply rew_subset; [ | eapply incl_appr, incl_appr, incl_refl ].
3: eapply rew_subset; [ | eapply incl_appl, incl_refl ].
all:destruct w as [[] | ] eqn:Ew, m eqn:Em; cbn -[Nat.add].
all:try match goal with [ |- context[enc_conf match ?l with _ => _ end]] => destruct l as [ | [] ] eqn:El end; cbn -[Nat.add].
all: rewrite ?map_app; cbn [map app].
all:unfold all_syms.
Ltac inst_left := match goal with [ |- ?L = ?R ] => match L with context C [?x1 :: ?x2 :: ?x3 :: ?r] => let t := context C [@nil nat] in instantiate (2 := t) | context C [?x1 :: ?x2 :: ?r] => let t := context C [@nil nat] in instantiate (2 := t) end end.
Ltac help1 := cbn -[Nat.add]; simpl_list; cbn -[Nat.add];inst_left; cbn; now simpl_list.
Ltac help2 := cbn -[Nat.add]; now simpl_list.
all: eapply do_rew; [ (now left + (right; now left) + (right; right; now left) + (right; right; right; now left)) | help1 | help2].
