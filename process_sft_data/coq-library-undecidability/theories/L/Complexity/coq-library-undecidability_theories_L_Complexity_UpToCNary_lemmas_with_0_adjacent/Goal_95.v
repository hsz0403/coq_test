From Undecidability.L.Complexity Require Export UpToC GenericNary.
Require Import smpl.Smpl.
From Coq Require Import Setoid.
From Coq Require Import CRelationClasses CMorphisms.
From Undecidability.Shared.Libs.PSL Require FinTypes.
Local Set Universe Polymorphism.
Smpl Add 2 rewrite leToC_eta in *: nary_prepare.
Set Default Proof Using "Type".
Section workaround.
Local Generalizable Variables A R eqA B S eqB.
Global Instance pointwise_reflexive {A} `(reflb : Reflexive B eqB) : Reflexive (pointwise_relation A eqB) | 9.
Proof.
firstorder.
Global Instance pointwise_symmetric {A} `(symb : Symmetric B eqB) : Symmetric (pointwise_relation A eqB) | 9.
Proof.
firstorder.
Global Instance pointwise_transitive {A} `(transb : Transitive B eqB) : Transitive (pointwise_relation A eqB) | 9.
Proof.
firstorder.
Global Instance pointwise_equivalence {A} `(eqb : Equivalence B eqB) : Equivalence (pointwise_relation A eqB) | 9.
Proof.
firstorder.
Instance workaround1 : @subrelation Type (@eq Type) arrow.
Proof.
cbv.
firstorder congruence.
Global Instance workaround2 X Y: (subrelation (pointwise_relation X (@eq Y)) (Morphisms.pointwise_relation X eq)).
Proof.
firstorder.
End workaround.
Ltac domain_of_prod S := let S := constr:(S) in let S := eval simpl in S in list_of_tuple S.
Ltac leUpToC_domain G := match G with | @leUpToC ?F _ _ => let L := domain_of_prod F in let L := constr:(L) in exact (Mk_domain_of_goal L) end.
Hint Extern 0 Domain_of_goal => (mk_domain_getter leUpToC_domain) : domain_of_goal.
Smpl Add 6 first [nary simple apply upToC_add_nary | nary simple apply upToC_mul_c_l_nary | nary simple apply upToC_mul_c_r_nary | nary simple apply upToC_max_nary| nary simple apply upToC_min_nary | progress (nary simple apply upToC_c_nary) | _applyIfNotConst_nat (nary simple apply upToC_S_nary)] : upToC.
Ltac destruct_pair_rec p := lazymatch type of p with (_*_)%type=> let lhs := fresh "p" in let x := fresh "x" in destruct p as [lhs x];destruct_pair_rec lhs | _ => idtac end.
Ltac upToC_le_nary_solve := let x := fresh "x" in apply upToC_le;intros x;destruct_pair_rec x; first [nia|lia].
Smpl Add upToC_le_nary_solve : upToC_solve.
Goal @leUpToC (nat*bool*nat) (fun '(xxx,y,z) => xxx+2+3*z) (fun '(x,y,z) => x+z+1).
Proof.
smpl_upToC_solve.
Goal (fun '(x,y) => S x + 3 + S y) <=c (fun '(x,y) => x+y+1).
Proof.
timeout 20 (smpl_upToC_solve).
Goal (fun '(x,y) => 3) <=c (fun '(x,y) => x+y+1).
Proof.
smpl upToC.
smpl upToC_solve.
Section bla.
Import FinTypes.
End bla.

Goal (fun '(x,y) => 3) <=c (fun '(x,y) => x+y+1).
Proof.
smpl upToC.
smpl upToC_solve.
