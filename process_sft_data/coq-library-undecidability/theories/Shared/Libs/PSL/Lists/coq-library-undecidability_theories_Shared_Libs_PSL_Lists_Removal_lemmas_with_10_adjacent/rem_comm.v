From Undecidability.Shared.Libs.PSL Require Export BaseLists Filter.
Section Removal.
Variable X : eqType.
Implicit Types (x y: X) (A B: list X).
Definition rem A x : list X := filter (fun z => Dec (z <> x)) A.
End Removal.
Hint Resolve rem_not_in rem_incl rem_mono rem_cons rem_cons' rem_app rem_app' rem_in rem_neq rem_inclr : core.

Lemma rem_not_in x y A : x = y \/ ~ x el A -> ~ x el rem A y.
Proof.
unfold rem.
rewrite in_filter_iff, Dec_reflect.
Admitted.

Lemma rem_incl A x : rem A x <<= A.
Proof.
Admitted.

Lemma rem_mono A B x : A <<= B -> rem A x <<= rem B x.
Proof.
Admitted.

Lemma rem_cons A B x : A <<= B -> rem (x::A) x <<= B.
Proof.
intros E y F.
apply E.
apply in_rem_iff in F.
Admitted.

Lemma rem_cons' A B x y : x el B -> rem A y <<= B -> rem (x::A) y <<= B.
Proof.
intros E F u G.
apply in_rem_iff in G as [[[]|G] H].
exact E.
apply F.
apply in_rem_iff.
Admitted.

Lemma rem_in x y A : x el rem A y -> x el A.
Proof.
Admitted.

Lemma rem_neq x y A : x <> y -> x el A -> x el rem A y.
Proof.
intros E F.
apply in_rem_iff.
Admitted.

Lemma rem_app x A B : x el A -> B <<= A ++ rem B x.
Proof.
intros E y F.
Admitted.

Lemma rem_app' x A B C : rem A x <<= C -> rem B x <<= C -> rem (A ++ B) x <<= C.
Proof.
Admitted.

Lemma rem_equi x A : x::A === x::rem A x.
Proof.
Admitted.

Lemma rem_fst x A : rem (x::A) x = rem A x.
Proof.
unfold rem.
Admitted.

Lemma rem_fst' x y A : x <> y -> rem (x::A) y = x::rem A y.
Proof.
intros E.
unfold rem.
Admitted.

Lemma rem_id x A : ~ x el A -> rem A x = A.
Proof.
intros D.
apply filter_id.
intros y E.
apply Dec_reflect.
Admitted.

Lemma rem_reorder x A : x el A -> A === x :: rem A x.
Proof.
intros D.
rewrite <- rem_equi.
Admitted.

Lemma rem_inclr A B x : A <<= B -> ~ x el A -> A <<= rem B x.
Proof.
intros D E y F.
apply in_rem_iff.
Admitted.

Lemma rem_comm A x y : rem (rem A x) y = rem (rem A y) x.
Proof.
apply filter_comm.
