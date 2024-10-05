From Undecidability.Shared.Libs.PSL Require Export BaseLists Filter.
Section Removal.
Variable X : eqType.
Implicit Types (x y: X) (A B: list X).
Definition rem A x : list X := filter (fun z => Dec (z <> x)) A.
End Removal.
Hint Resolve rem_not_in rem_incl rem_mono rem_cons rem_cons' rem_app rem_app' rem_in rem_neq rem_inclr : core.

Lemma rem_equi x A : x::A === x::rem A x.
Proof.
split; intros y; intros [[]|E]; decide (x=y) as [[]|D]; eauto using rem_in, rem_neq.
