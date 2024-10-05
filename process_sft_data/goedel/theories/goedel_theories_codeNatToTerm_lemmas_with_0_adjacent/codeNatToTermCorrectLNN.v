Require Import primRec.
Require Import cPair.
Require Import Arith.
Require Import code.
Require Import folProp.
Require Import folProof.
Require Import Languages.
Require LNN.
Require LNT.
Definition natToTermLNN := LNN.natToTerm.
Definition natToTermLNT := LNT.natToTerm.
Definition codeNatToTerm : nat -> nat := nat_rec (fun _ => nat) (cPair 4 0) (fun _ rec : nat => cPair 3 (S (cPair rec 0))).

Lemma codeNatToTermCorrectLNN : forall n : nat, codeNatToTerm n = codeTerm LNN codeLNTFunction (natToTermLNN n).
Proof.
intro.
induction n as [| n Hrecn].
reflexivity.
simpl in |- *.
rewrite Hrecn.
reflexivity.
