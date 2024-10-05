Require Import List Lia Relations.Relation_Operators Relations.Operators_Properties.
Import ListNotations.
Require Import Undecidability.MinskyMachines.MM2.
Require Undecidability.CounterMachines.CM2.
From Undecidability.CounterMachines.Util Require Import Nat_facts List_facts MM2_facts CM2_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Module Argument.
Section MM2_CM2.
Variable (P: list mm2_instr).
Variables (a0 b0: nat).
Definition mm2_config : Set := (nat*(nat*nat)).
Definition fs (i: nat) : CM2.State := if i is S i then i + a0 + b0 else (length P) + a0 + b0.
Definition encode_instruction (mmi: mm2_instr) : CM2.Instruction := match mmi with | mm2_inc_a => CM2.inc false | mm2_inc_b => CM2.inc true | mm2_dec_a j => CM2.dec false (fs j) | mm2_dec_b j => CM2.dec true (fs j) end.
Definition M : list CM2.Instruction := (repeat (CM2.inc false) a0) ++ (repeat (CM2.inc true) b0) ++ map encode_instruction P.
Definition encode_config (x: mm2_config) : CM2.Config := let: (i, (a, b)) := x in {| CM2.state := fs i; CM2.value1 := a; CM2.value2 := b |}.
Inductive program_index : nat -> Prop := | seek_M_None {i} : nth_error M (fs i) = None -> (forall op, not (mm2_instr_at op i P)) -> program_index i | seek_M_Some {i op} : nth_error M (fs (1+i)) = Some (encode_instruction op) -> mm2_instr_at op (1+i) P -> program_index (1+i).
End MM2_CM2.
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma program_index_spec (i: nat) : program_index i.
Proof.
move Ht: (nth_error M (fs i)) => t.
case: t Ht.
-
move: i => [|i] op.
+
move=> ?.
have /nth_error_Some : nth_error M (fs 0) <> None by congruence.
rewrite length_M /=.
by lia.
+
move=> H.
have /nth_error_None : nth_error M (fs (S i)) <> None by congruence.
rewrite length_M /= => ?.
have /mm2_mmi_lookup [op' HP] : i < length P by lia.
move=> [:Hop'].
apply: (@seek_M_Some i op'); last (abstract: Hop').
*
rewrite /M HP seek_M nth_error_map nth_error_app2 ?firstn_length; first by lia.
by have ->: i - Nat.min i (length P) = 0 by lia.
*
do 2 eexists.
constructor; [by eassumption | rewrite firstn_length; by lia].
-
rewrite /M.
move=> Hi.
apply: seek_M_None; first done.
move=> op [l] [r] [HP ?].
subst i.
move: HP Hi => ->.
by rewrite seek_M nth_error_map nth_error_app2 ?PeanoNat.Nat.sub_diag.
