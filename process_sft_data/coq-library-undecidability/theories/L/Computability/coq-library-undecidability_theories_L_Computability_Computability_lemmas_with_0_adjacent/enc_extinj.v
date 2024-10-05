From Undecidability.L Require Export L Datatypes.LNat Datatypes.LBool Functions.Encoding Computability.Seval.
Require Import Coq.Logic.ConstructiveEpsilon.
Definition cChoice := constructive_indefinite_ground_description_nat_Acc.
Definition bool_enc_inv b:= match b with | lam (lam (var 1)) => true | _ => false end.
Arguments lcomp_comp _{_} _ {_} _ _.

Lemma enc_extinj {X} {H:registered X} (m n:X) : enc m == enc n -> m = n.
Proof.
intros eq.
apply unique_normal_forms in eq; try Lproc.
now apply inj_enc.
