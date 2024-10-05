From Undecidability.Shared.Libs.PSL Require Import Base Bijection FiniteTypes.FinTypes.
Require Import Coq.Vectors.Fin.
Instance Fin_eq_dec n : eq_dec (Fin.t n).
Proof.
intros; hnf.
destruct (eqb x y) eqn:E.
-
left.
now eapply eqb_eq.
-
right.
intros H.
eapply eqb_eq in H.
congruence.
Defined.
Definition all_Fin n := nat_rec (fun n0 : nat => list (t n0)) [] (fun (n0 : nat) (IHn : list (t n0)) => F1 :: map FS IHn) n.
Definition pure (X:Type) (p: X -> Prop) {D:forall x, dec (p x)} x := if Dec (p x) then True else False.
Arguments pure {X} p {D} x.
Ltac impurify H := pose proof (pure_impure H) as impureH; try (clear H; rename impureH into H).
Arguments purify {X} {p} {D} {x} px.
Definition subtype {X:Type} (p: X -> Prop) {D: forall x, dec (p x)} := { x:X | pure p x}.
Arguments subtype {X} p {D}.
Instance subType_eq_dec X (_:eq_dec X) (p: X -> Prop) (_: forall x, dec (p x)): eq_dec (subtype p).
Proof.
intros y z.
destruct y as [x p1], z as [x' p2].
decide (x=x').
-
left.
now apply subtype_extensionality.
-
right.
intro H.
apply n.
now inv H.
Fixpoint toSubList (X: Type) (A: list X) (p: X -> Prop) (D:forall x, dec (p x)) : list (subtype p) := match A with | nil => nil | cons x A' => match Dec (p x) with | left px => (exist _ x (purify px)) :: toSubList A' D | right _ => toSubList A' _ end end.
Arguments toSubList {X} A p {D}.
Notation "'Subtype' p" := (finTypeC (EqType (subtype p))) (at level 5).
Instance fromListC (X: eqType) (A: list X) : Subtype (fun x => x el A).
Proof.
econstructor.
intros [x p].
apply enum_ok_fromList.
Defined.

Lemma enum_ok_fromList (X: eqType) (A: list X) x : count (undup (toSubList A (fun x => x el A))) x = 1.
Proof.
apply dupfreeCount.
-
apply dupfree_undup.
-
rewrite <- in_undup_iff.
apply countIn.
cbn in *.
rewrite toSubList_count.
destruct x as [x p].
cbn.
apply InCount.
now impurify p.
