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

Lemma M_to_P_step (x: mm2_config) : CM2.halting M (encode_config x) \/ exists y, CM2.step M (encode_config x) = encode_config y /\ mm2_step P x y.
Proof.
move: x => [i [a b]].
rewrite /CM2.halting /=.
move: (program_index_spec i) => [{}i | {}i op] -> HiP; [by left | right].
have [y Hy] := @mm2_progress op (1 + i, (a, b)).
exists y.
constructor; [by inversion Hy | by exists op].
