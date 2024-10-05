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

Instance register_unit : registered unit.
Proof.
Admitted.

Instance term_on0 : computable on0.
Proof.
Admitted.

Lemma test_Some_nat : computable (@Some nat).
Proof.
Admitted.

Goal computable orb.
Proof.
extractAs s.
computable_using_noProof s.
cstep.
cstep.
cstep.
Admitted.

Goal computableTime' orb (fun _ _ => (cnst "c1",fun _ _ => (cnst "c2",tt))).
Proof.
extract.
Admitted.

Goal computableTime' orb (fun _ _ => (1,fun _ _ => (3,tt))).
Proof.
extract.
Admitted.

Goal computable Nat.add.
Proof.
unfold Nat.add.
extractAs s.
computable_using_noProof s.
cstep.
all:cstep.
Admitted.

Goal computable (fix f (x y z : nat) := y + match y with | S (S y) => S (f x y z) | _ => 0 end).
extractAs s.
computable_using_noProof s.
cstep.
all:cstep.
all:cstep.
Admitted.

Lemma supported3 : computable (fun (b:bool) => if b then (fix f x := match x with S x => f x | 0 => 0 end) else S).
extractAs s.
computable_using_noProof s.
cstep.
cstep.
all:cstep.
Admitted.

Lemma unsupported : computable (fix f (y : nat) {struct y}:= match y with | S (S y) => f y | _ => S end).
extractAs s.
computable_using_noProof s.
repeat cstep.
Admitted.

Lemma workarround : let f := (fix f (z y : nat) {struct y}:= match y with | S (S y) => f z y | _ => S z end) in computable (fun y z => f z y).
Proof.
intros f.
assert (computable f) by (unfold f;extract).
Admitted.

Lemma unsupported2 : computable 10.
Proof.
extract.
Admitted.

Goal computable (fun n : nat => 10).
Proof.
Admitted.

Lemma map_term A B (Rx : registered A) (Ry: registered B): computable (@map A B).
Proof.
extractAs s.
computable_using_noProof s.
cstep.
cstep.
Admitted.

Lemma termT_map A B (Rx : registered A) (Ry: registered B): computableTime' (@map A B) (fun f fT => (cnst "c",fun xs _ => (cnst ("f",xs),tt))).
Proof.
extractAs s.
computable_using_noProof s.
cstep.
cstep.
Admitted.

Lemma termT_map A B (Rx : registered A) (Ry: registered B): computableTime' (@map A B) (fun f fT => (cnst "c",fun xs _ => (cnst ("f",xs),tt))).
Proof.
extract.
Admitted.

Lemma term_map (X Y:Type) (Hx : registered X) (Hy:registered Y): computableTime' (@map X Y) (fun f fT => (1,fun l _ => (fold_right (fun x res => fst (fT x tt) + res + 12) 8 l,tt))).
Proof.
extract.
Admitted.

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
