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

Lemma M_to_P (n: nat) (x: mm2_config) : exists y, Nat.iter n (CM2.step M) (encode_config x) = encode_config y /\ clos_refl_trans _ (mm2_step P) x y.
Proof.
elim: n x; first by (move=> x; exists x; constructor; [done | by apply: rt_refl]).
move=> n + x.
move: (M_to_P_step x) => [Hx _| [y [HMxy HPxy]]].
-
exists x.
constructor; last by apply: rt_refl.
elim: n; [done | by move=> n /= ->].
-
move=> /(_ y) => [[z [? ?]]].
exists z.
constructor.
+
have ->: S n = 1 + n by lia.
by rewrite iter_plus /= HMxy.
+
apply: rt_trans; [apply: rt_step | eassumption]; done.
