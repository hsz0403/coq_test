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

Lemma rev_sim t q z : SR.rew R (enc_conf t q) z -> exists q' w m, trans M (q, curr t) = Some (q', w, m) /\ z = enc_conf (mv m (wr w t)) q'.
Proof.
intros H.
inversion H as [x y u v Hin HL HR]; subst z.
destruct t as [[ls o] rs].
eapply in_flat_map in Hin as (q_ & _ & Hq2).
unfold rules in Hq2.
rewrite ! in_app_iff in Hq2.
destruct Hq2 as [ Hq2 | [Hq2 | Hq2]].
all: destruct (trans M (q_, _)) as [ [[q' w] m] | ] eqn:Etrans; try destruct m eqn:Em; try destruct w as [[] | ] eqn:Ew; cbn -[Nat.add] in Hq2; (exists q', w, m || exfalso); rewrite ?Em, ?Ew.
all: repeat match type of Hq2 with _ \/ _ => destruct Hq2 as [Hq2 | Hq2] end; inversion Hq2; subst u v; clear Hq2; cbn -[Nat.add].
cbn [app] in HL.
all: cbn [app] in HL; match type of HL with | ?L = ?R => match L with context C [! ?q :: ?c :: ?rs] => let ls := context C [@nil nat] in replace L with (ls ++ !q ++ [c] ++ rs) in HL; [ | cbn; now simpl_list] end end.
all: match type of HL with _ = enc_conf (?ls,?o,?rs) ?q => let H1 := fresh "H" in let H2 := fresh "H" in let H3 := fresh "H" in let H4 := fresh "H" in let HH := fresh "H" in eapply enc_conf_inv in HL as (H1 & -> & H3 & H4); try rewrite H4 in *; destruct o as [ [] | ]; inversion H3; clear H3; cbn in H1; rewrite ?app_nil_r in H1; subst; split ; try eassumption; try reflexivity; (let x := match type of H1 with ?x ++ _ = _ => x end in destruct x; try (now inversion H1); cbn in H1; eapply cons_inj in H1 as [HH H1]; try rewrite HH in *; clear HH; now destruct ls as [ | []]; cbn in H1; [ reflexivity || destruct x; now inversion H1 | try rewrite map_app in H1; cbn in H1; (eapply app_inj_tail in H1 as [-> [=]] + (try eapply nil_app_tail in H1 as []) + (try eapply nil_app_tail' in H1 as []) ).. ]) + (destruct rs as [ | [] rs]; cbn in H4; eapply cons_inj in H4 as [ [=] H4]; rewrite ?H4 in *; clear H4; now cbn; simpl_list) end.
