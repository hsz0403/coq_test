From Undecidability.Shared.Libs.PSL Require Export BaseLists Filter.
Section Removal.
Variable X : eqType.
Implicit Types (x y: X) (A B: list X).
Definition rem A x : list X := filter (fun z => Dec (z <> x)) A.
End Removal.
Hint Resolve rem_not_in rem_incl rem_mono rem_cons rem_cons' rem_app rem_app' rem_in rem_neq rem_inclr : core.

Lemma rem_comm A x y : rem (rem A x) y = rem (rem A y) x.
Proof.
apply filter_comm.
