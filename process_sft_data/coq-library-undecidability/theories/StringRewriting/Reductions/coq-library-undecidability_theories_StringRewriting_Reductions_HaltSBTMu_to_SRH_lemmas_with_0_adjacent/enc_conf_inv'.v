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

Lemma enc_conf_inv' xs q ys ls o rs q' : xs ++ !q ++ ys = enc_conf (ls, o, rs) q' -> xs = [⦇] ++ map (fun b : bool => !!b) (rev ls) /\ q = q' /\ ys = encode_sym o :: map (fun b : bool => !!b) rs ++ [⦈].
Proof.
intros.
pose proof (H' := H).
cbn - [Nat.add] in H.
destruct xs; cbn -[Nat.add] in H; inversion H; subst n; clear H.
eapply list_prefix_inv' in H2 as (H1 & -> & H3).
-
subst.
repeat split.
eapply Fin.to_nat_inj.
unfold "!" in H1.
lia.
-
clear H'.
induction xs in ls, H2 |- *.
+
firstorder.
+
cbn -[Nat.add].
destruct ls as [ | ? ? _] using rev_ind.
*
cbn -[Nat.add] in H2.
inversion H2.
subst.
destruct xs; inversion H1; subst.
destruct o as [ [] | ]; cbn in H0; lia.
assert (In (!q) (map (fun b : bool => !! b) rs ++ [⦈])).
rewrite <- H3.
rewrite in_app_iff.
cbn[In].
solve [eauto].
eapply in_app_iff in H as [ (? & ? & ?) % in_map_iff | [ | []]]; try destruct x; cbn in H; lia.
*
rewrite rev_app_distr in H2.
cbn -[Nat.add] in H2.
inversion H2; subst.
intros [ | ].
--
destruct x; cbn in *; lia.
--
eapply IHxs.
2:eauto.
rewrite H1.
reflexivity.
-
intros (? & ? & ?) % in_map_iff.
destruct x; cbn in *; lia.
