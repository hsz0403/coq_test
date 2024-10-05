From Undecidability.FOL Require Import Util.Aczel.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Definition CE := forall (P Q : Acz -> Prop), (forall s, P s <-> Q s) -> P = Q.
Section Model.
Definition eqclass P := exists s, P = Aeq s.
Hypothesis ce : CE.
Definition SET' := { P | eqclass P }.
Definition class (X : SET') : Acz -> Prop := proj1_sig X.
Definition ele X Y := forall s t, (class X) s -> (class Y) t -> Ain s t.
Definition sub X Y := forall Z, ele Z X -> ele Z Y.
Hint Resolve Aeq_eqclass : core.
Definition classof (s : Acz) : SET' := exist _ (Aeq s) (Aeq_eqclass s).
Hint Resolve classof_class classof_eq classof_ele classof_sub : core.
Definition empty := classof AEmpty.
Definition upair' X Y u := exists s t, (class X) s /\ (class Y) t /\ Aeq u (Aupair s t).
Definition upair X Y := exist _ (upair' X Y) (upair_eqclass X Y).
Definition union' X t := exists s, (class X) s /\ Aeq t (Aunion s).
Definition union X := exist _ (union' X) (union_eqclass X).
Definition power' X t := exists s, (class X) s /\ Aeq t (Apower s).
Definition power X := exist _ (power' X) (power_eqclass X).
Definition empred (P : SET' -> Prop) := fun s => P (classof s).
Fact empred_Aeq P : cres Aeq (empred P).
Proof.
intros s s' H % classof_eq.
unfold empred.
now rewrite H.
Definition sep' P X t := exists s, (class X) s /\ Aeq t (Asep (empred P) s).
Definition sep P X := exist _ (sep' P X) (sep_eqclass P X).
Definition succ X := union (upair X (upair X X)).
Definition inductive X := ele empty X /\ forall Y, ele Y X -> ele (succ Y) X.
Definition om := classof Aom.
End Model.

Lemma upair_welldef s t : upair (classof s) (classof t) = classof (Aupair s t).
Proof.
pose (u := Aupair s t).
apply (class_eq (s:=u) (s':=u)); trivial.
exists s, t.
Admitted.

Lemma upairAx X Y Z : ele Z (upair X Y) <-> Z = X \/ Z = Y.
Proof.
destruct (classof_ex Z) as [u ->].
destruct (classof_ex X) as [s ->].
destruct (classof_ex Y) as [t ->].
repeat rewrite classof_eq.
rewrite upair_welldef, classof_ele.
Admitted.

Lemma union_welldef s : union (classof s) = classof (Aunion s).
Proof.
pose (t := Aunion s).
apply (class_eq (s:=t) (s':=t)); trivial.
exists s.
Admitted.

Lemma unionAx X Z : ele Z (union X) <-> exists Y, ele Y X /\ ele Z Y.
Proof.
destruct (classof_ex Z) as [u ->].
destruct (classof_ex X) as [s ->].
rewrite union_welldef, classof_ele, AunionAx.
split; intros [t H].
-
exists (classof t).
now repeat rewrite classof_ele.
-
destruct (classof_ex t) as [t' ->].
exists t'.
Admitted.

Lemma power_welldef s : power (classof s) = classof (Apower s).
Proof.
pose (t := Apower s).
apply (class_eq (s:=t) (s':=t)); trivial.
exists s.
Admitted.

Lemma powerAx X Y : ele Y (power X) <-> sub Y X.
Proof.
destruct (classof_ex Y) as [t ->].
destruct (classof_ex X) as [s ->].
rewrite power_welldef, classof_ele, classof_sub.
Admitted.

Lemma sep_welldef P s : sep P (classof s) = classof (Asep (empred P) s).
Proof.
pose (t := Asep (empred P) s).
apply (class_eq (s:=t) (s':=t)); trivial.
exists s.
Admitted.

Lemma sepAx P X Y : ele Y (sep P X) <-> ele Y X /\ P Y.
Proof.
destruct (classof_ex Y) as [s ->].
destruct (classof_ex X) as [t ->].
rewrite sep_welldef.
repeat rewrite classof_ele.
Admitted.

Lemma succ_eq s : succ (classof s) = classof (Asucc s).
Proof.
apply set_ext.
split; intros X H.
-
apply unionAx in H as [Y[H1 H2]].
destruct (classof_ex X) as [t ->].
apply classof_ele.
apply AunionAx.
apply upairAx in H1 as [->| ->].
+
exists s.
split; try now apply classof_ele.
apply AupairAx.
now left.
+
exists (Aupair s s).
rewrite AupairAx.
split; auto.
apply upairAx in H2.
rewrite !classof_eq in H2.
now apply AupairAx.
-
destruct (classof_ex X) as [t ->].
apply classof_ele in H.
apply AunionAx in H as [u[H1 H2]].
apply unionAx.
apply AupairAx in H1 as [H1| H1]; subst.
+
exists (classof u).
split; try now apply classof_ele.
apply upairAx.
left.
now apply classof_eq.
+
exists (upair (classof s) (classof s)).
rewrite upairAx.
split; auto.
rewrite H1 in H2.
apply AupairAx in H2.
rewrite <- !classof_eq in H2.
Admitted.

Lemma Ainductive_inductive s : Ainductive s <-> inductive (classof s).
Proof.
split; intros H.
-
split.
+
apply classof_ele.
apply H.
+
intros X H'.
destruct (classof_ex X) as [t ->].
rewrite succ_eq.
apply classof_ele, H.
now apply classof_ele.
-
split.
+
apply classof_ele.
apply H.
+
intros t Ht.
apply classof_ele.
rewrite <- succ_eq.
apply H.
Admitted.

Lemma om_Ax2 : forall X, inductive X -> sub om X.
Proof.
intros X H.
destruct (classof_ex X) as [s ->].
apply classof_sub.
Admitted.

Lemma om_Ax1 : inductive om.
Proof.
split.
-
apply classof_ele.
apply AomAx1.
-
intros X H.
destruct (classof_ex X) as [s ->].
rewrite succ_eq.
apply classof_ele, AomAx1.
now apply classof_ele.
