From Undecidability.L.Datatypes Require Import LOptions LBool LNat Lists.
From Undecidability.L.Tactics Require Import LTactics ComputableTactics.
Require Import Nat.
Set Default Proof Using "Type".
Section demo.
Definition unit_enc := fun (x:unit) => I.
Instance register_unit : registered unit.
Proof.
register unit_enc.
Defined.
Definition on0 (f:nat->nat->nat) := f 0 0.
Instance term_on0 : computable on0.
Proof.
extract.
Section PaperExample.
Import ComputableTactics.
Import ComputableTactics.Intern.
Goal computable orb.
Proof.
extractAs s.
computable_using_noProof s.
cstep.
cstep.
cstep.
all: cstep.
Goal forall fT, computableTime' orb fT.
Proof.
intros.
extractAs s.
computable_using_noProof s.
cstep.
cstep.
cstep.
cstep.
1,2:cstep.
solverec.
Abort.
Goal computableTime' orb (fun _ _ => (cnst "c1",fun _ _ => (cnst "c2",tt))).
Proof.
extract.
solverec.
Abort.
Goal computableTime' orb (fun _ _ => (1,fun _ _ => (3,tt))).
Proof.
extract.
solverec.
Abort.
Import Datatypes.LNat.
Goal computable Nat.add.
Proof.
unfold Nat.add.
extractAs s.
computable_using_noProof s.
cstep.
all:cstep.
all:cstep.
Goal computable (fix f (x y z : nat) := y + match y with | S (S y) => S (f x y z) | _ => 0 end).
extractAs s.
computable_using_noProof s.
cstep.
all:cstep.
all:cstep.
all:cstep.
Import Datatypes.Lists.
Remove Hints term_map : typeclass_instances.
End PaperExample.
End demo.

Lemma unsupported : computable (fix f (y : nat) {struct y}:= match y with | S (S y) => f y | _ => S end).
extractAs s.
computable_using_noProof s.
repeat cstep.
Fail Guarded.
