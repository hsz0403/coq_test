Require Import List Arith Nat Lia Relations Bool.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list fin_base.
Set Implicit Arguments.
Section finite_t_upto.
Variable (X : Type) (R : X -> X -> Prop).
Definition fin_t_upto (P : X -> Type) := { l : _ & (forall x, P x -> exists y, In y l /\ R x y) *(forall x y, In x l -> R x y -> P y) }%type.
Definition finite_t_upto := { l : _ | forall x, exists y, In y l /\ R x y }.
Fact finite_t_fin_upto : (finite_t_upto -> fin_t_upto (fun _ => True)) * (fin_t_upto (fun _ => True) -> finite_t_upto).
Proof.
split.
+
intros (l & Hl); exists l; split; auto.
+
intros (l & H1 & H2); exists l; firstorder.
End finite_t_upto.
Arguments finite_t_upto : clear implicits.
Section finite_t_weak_dec_powerset.
Variable (X : Type).
Let wdec (R : X -> Prop) := forall x, R x \/ ~ R x.
Let pset_fin_t (l : list X) : { ll | forall R (_ : wdec R), exists T, In T ll /\ forall x, In x l -> R x <-> T x }.
Proof.
induction l as [ | x l IHl ].
+
exists ((fun _ => True) :: nil).
intros R HR; exists (fun _ => True); simpl; split; tauto.
+
destruct IHl as (ll & Hll).
exists (map (fun T a => x<>a /\ T a) ll ++ map (fun T a => x=a \/ T a) ll).
intros R HR.
destruct (Hll R) as (T & H1 & H2); auto.
destruct (HR x) as [ H0 | H0 ].
*
exists (fun a => x = a \/ T a); split.
-
apply in_or_app; right.
apply in_map_iff; exists T; auto.
-
intros y [ <- | H ]; simpl; try tauto.
rewrite H2; auto; split; auto.
intros [ -> | ]; auto.
apply H2; auto.
*
exists (fun a => x <> a /\ T a); split.
-
apply in_or_app; left.
apply in_map_iff; exists T; auto.
-
intros y [ <- | H ]; simpl; split; try tauto.
++
rewrite <- H2; auto; split; auto.
contradict H0; subst; auto.
++
rewrite <- H2; tauto.
End finite_t_weak_dec_powerset.

Let pset_fin_t (l : list X) : { ll | forall R (_ : wdec R), exists T, In T ll /\ forall x, In x l -> R x <-> T x }.
Proof.
induction l as [ | x l IHl ].
+
exists ((fun _ => True) :: nil).
intros R HR; exists (fun _ => True); simpl; split; tauto.
+
destruct IHl as (ll & Hll).
exists (map (fun T a => x<>a /\ T a) ll ++ map (fun T a => x=a \/ T a) ll).
intros R HR.
destruct (Hll R) as (T & H1 & H2); auto.
destruct (HR x) as [ H0 | H0 ].
*
exists (fun a => x = a \/ T a); split.
-
apply in_or_app; right.
apply in_map_iff; exists T; auto.
-
intros y [ <- | H ]; simpl; try tauto.
rewrite H2; auto; split; auto.
intros [ -> | ]; auto.
apply H2; auto.
*
exists (fun a => x <> a /\ T a); split.
-
apply in_or_app; left.
apply in_map_iff; exists T; auto.
-
intros y [ <- | H ]; simpl; split; try tauto.
++
rewrite <- H2; auto; split; auto.
contradict H0; subst; auto.
++
rewrite <- H2; tauto.
