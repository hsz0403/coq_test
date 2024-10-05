From Undecidability.L Require Export L Datatypes.LNat Datatypes.LBool Functions.Encoding Computability.Seval.
Require Import Coq.Logic.ConstructiveEpsilon.
Definition cChoice := constructive_indefinite_ground_description_nat_Acc.
Definition bool_enc_inv b:= match b with | lam (lam (var 1)) => true | _ => false end.
Arguments lcomp_comp _{_} _ {_} _ _.

Lemma bool_enc_inv_correct : (forall x (y:bool), enc y = x -> y = bool_enc_inv x).
Proof.
intros x [];intros;subst;reflexivity.
