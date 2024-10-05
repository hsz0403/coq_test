From Undecidability.Shared.Libs.PSL Require Export BaseLists Filter.
Section Removal.
Variable X : eqType.
Implicit Types (x y: X) (A B: list X).
Definition rem A x : list X := filter (fun z => Dec (z <> x)) A.
End Removal.
Hint Resolve rem_not_in rem_incl rem_mono rem_cons rem_cons' rem_app rem_app' rem_in rem_neq rem_inclr : core.

Lemma rem_cons' A B x y : x el B -> rem A y <<= B -> rem (x::A) y <<= B.
Proof.
intros E F u G.
apply in_rem_iff in G as [[[]|G] H].
exact E.
apply F.
apply in_rem_iff.
auto.
