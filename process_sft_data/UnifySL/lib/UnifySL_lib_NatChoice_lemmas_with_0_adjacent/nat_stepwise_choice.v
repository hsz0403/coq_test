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

Lemma nat_stepwise_choice: (forall l, P l -> exists a, P (l ++ a :: nil)) -> exists f, forall n, P (fisrtn_list_from_fun f n).
Proof.
intros.
assert (forall (l: list A | P l), exists a : A, P (proj1_sig l ++ a :: nil)) as HH; [| clear H].
{
intros [l ?H].
apply H; auto.
}
apply choice in HH.
destruct HH as [f ?].
exists (fun n => f (step f H n)).
intros.
rewrite fisrtn_list_step.
apply (proj2_sig (step f H n)).
