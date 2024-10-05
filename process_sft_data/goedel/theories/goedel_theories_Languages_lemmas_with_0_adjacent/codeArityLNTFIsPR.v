Require Import Arith.
Require Import fol.
Require Import primRec.
Require Import Coq.Lists.List.
Inductive LNTFunction : Set := | Plus : LNTFunction | Times : LNTFunction | Succ : LNTFunction | Zero : LNTFunction.
Inductive LNNRelation : Set := LT : LNNRelation.
Definition LNTFunctionArity (x : LNTFunction) : nat := match x with | Plus => 2 | Times => 2 | Succ => 1 | Zero => 0 end.
Definition LNTArity (x : Empty_set + LNTFunction) : nat := match x return nat with | inl bot => Empty_set_rec (fun _ => nat) bot | inr y => LNTFunctionArity y end.
Definition LNNArity (x : LNNRelation + LNTFunction) : nat := match x return nat with | inl y => match y with | LT => 2 end | inr y => LNTFunctionArity y end.
Definition LNT : Language := language Empty_set LNTFunction LNTArity.
Definition LNN : Language := language LNNRelation LNTFunction LNNArity.
Definition codeLNTFunction (f : LNTFunction) : nat := match f with | Plus => 0 | Times => 1 | Succ => 2 | Zero => 3 end.
Definition codeLNTRelation (R : Empty_set) : nat := match R return nat with end.
Definition codeLNNRelation (R : LNNRelation) : nat := 0.
Definition codeArityLNNR (r : nat) := switchPR r 0 3.
Definition codeArityLNTR (r : nat) := 0.
Definition codeArityLNTF (f : nat) := switchPR f (switchPR (pred f) (switchPR (pred (pred f)) (switchPR (pred (pred (pred f))) 0 1) 2) 3) 3.

Lemma codeArityLNTFIsPR : isPR 1 codeArityLNTF.
Proof.
set (f := list_rec (fun _ => nat -> nat -> nat) (fun _ _ : nat => 0) (fun (a : nat) (l : list nat) (rec : nat -> nat -> nat) (n f : nat) => switchPR (iterate pred n f) (rec (S n) f) a)) in *.
assert (forall (l : list nat) (n : nat), isPR 1 (f l n)).
intro.
induction l as [| a l Hrecl]; intros.
simpl in |- *.
apply const1_NIsPR.
simpl in |- *.
apply compose1_3IsPR with (f1 := fun f0 : nat => iterate pred n f0) (f2 := fun f0 : nat => f l (S n) f0) (f3 := fun f0 : nat => a).
apply iterateIsPR with (g := pred) (n := n).
apply predIsPR.
apply Hrecl with (n := S n).
apply const1_NIsPR.
apply switchIsPR.
apply (H (3 :: 3 :: 2 :: 1 :: nil) 0).
