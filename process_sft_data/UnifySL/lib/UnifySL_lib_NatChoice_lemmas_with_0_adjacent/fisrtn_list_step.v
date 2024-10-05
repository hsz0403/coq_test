Require Import Coq.Lists.List.
Require Import Coq.Logic.ClassicalChoice.
Module Type NAT_CHOICE.
Fixpoint fisrtn_list_from_fun {A: Type} (f: nat -> A) (n: nat) : list A := match n with | 0 => nil | S m => fisrtn_list_from_fun f m ++ f m :: nil end.
Axiom nat_stepwise_choice: forall {A: Type} (P: list A -> Prop), P nil -> (forall l, P l -> exists a, P (l ++ a :: nil)) -> exists f, forall n, P (fisrtn_list_from_fun f n).
End NAT_CHOICE.
Module NatChoice: NAT_CHOICE.
Section NatChoice.
Fixpoint fisrtn_list_from_fun {A: Type} (f: nat -> A) (n: nat) : list A := match n with | 0 => nil | S m => fisrtn_list_from_fun f m ++ f m :: nil end.
Context {A: Type} (P: list A -> Prop).
Definition State: Type := {l: list A | P l}.
Hypothesis H_init: P nil.
Definition state_nil: State := exist _ nil H_init.
Section step.
Variable F: State -> A.
Hypothesis HF: forall l: State, P (proj1_sig l ++ F l :: nil).
Fixpoint step (n: nat): State := match n with | 0 => state_nil | S m => exist _ _ (HF (step m)) end.
End step.
End NatChoice.
End NatChoice.
Export NatChoice.

Lemma fisrtn_list_step: forall n, fisrtn_list_from_fun (fun n0 : nat => F (step n0)) n = proj1_sig (step n).
Proof.
intros.
induction n.
+
simpl.
reflexivity.
+
simpl.
f_equal; auto.
