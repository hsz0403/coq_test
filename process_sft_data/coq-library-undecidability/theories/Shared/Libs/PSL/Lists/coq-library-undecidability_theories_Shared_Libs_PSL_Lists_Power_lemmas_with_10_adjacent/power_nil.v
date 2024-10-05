From Undecidability.Shared.Libs.PSL Require Import BaseLists Dupfree.
Section Power.
Variable X : Type.
Fixpoint power (U: list X ) : list (list X) := match U with | nil => [nil] | x :: U' => power U' ++ map (cons x) (power U') end.
End Power.
Section PowerRep.
Variable X : eqType.
Implicit Types A U : list X.
Definition rep (A U : list X) : list X := filter (fun x => Dec (x el A)) U.
End PowerRep.

Lemma power_incl A U : A el power U -> A <<= U.
Proof.
revert A; induction U as [|x U]; cbn; intros A D.
-
destruct D as [[]|[]]; auto.
-
apply in_app_iff in D as [E|E].
now auto.
apply in_map_iff in E as [A' [E F]].
subst A.
Admitted.

Lemma rep_cons A x U : x el A -> rep A (x::U) = x :: rep A U.
Proof.
intros H.
apply filter_fst.
Admitted.

Lemma rep_cons' A x U : ~ x el A -> rep A (x::U) = rep A U.
Proof.
intros H.
apply filter_fst'.
Admitted.

Lemma rep_cons_eq x A U : ~ x el U -> rep (x::A) U = rep A U.
Proof.
intros D.
apply filter_pq_eq.
intros y E.
apply Dec_reflect_eq.
split.
-
intros [<-|F]; tauto.
-
Admitted.

Lemma rep_power A U : rep A U el power U.
Proof.
revert A; induction U as [|x U]; intros A.
-
cbn; auto.
-
decide (x el A) as [H|H].
+
rewrite (rep_cons _ H).
cbn.
auto using in_map.
+
rewrite (rep_cons' _ H).
cbn.
Admitted.

Lemma rep_incl A U : rep A U <<= A.
Proof.
intros x.
unfold rep.
rewrite in_filter_iff, Dec_reflect.
Admitted.

Lemma rep_in x A U : A <<= U -> x el A -> x el rep A U.
Proof.
intros D E.
Admitted.

Lemma rep_equi A U : A <<= U -> rep A U === A.
Proof.
intros D.
split.
now apply rep_incl.
intros x.
Admitted.

Lemma rep_mono A B U : A <<= B -> rep A U <<= rep B U.
Proof.
intros D.
apply filter_pq_mono.
Admitted.

Lemma rep_eq' A B U : (forall x, x el U -> (x el A <-> x el B)) -> rep A U = rep B U.
Proof.
intros D.
apply filter_pq_eq.
intros x E.
apply Dec_reflect_eq.
Admitted.

Lemma rep_eq A B U : A === B -> rep A U = rep B U.
Proof.
intros D.
apply filter_pq_eq.
intros x E.
apply Dec_reflect_eq.
Admitted.

Lemma power_nil U : nil el power U.
Proof.
induction U; cbn; auto.
