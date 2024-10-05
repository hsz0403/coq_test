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

Lemma codeArityLNTRIsCorrect1 : forall r : Relations LNT, codeArityLNTR (codeLNTRelation r) = S (arity LNT (inl _ r)).
Proof.
simple induction r.
