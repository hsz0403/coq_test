Require Export Arith.
Require Export misc.
Require Export groups.
Require Export Zbase.
Require Export Z_succ_pred.
Require Export Zadd.
Definition leZ (x y : Z) := match x return Prop with | OZ => match y return Prop with | OZ => True | pos n => True | neg n => False end | pos n => match y return Prop with | OZ => False | pos m => n <= m | neg m => False end | neg n => match y return Prop with | OZ => True | pos m => True | neg m => m <= n end end.
Definition ltZ (x y : Z) := leZ (succZ x) y.
Definition lt_absZ (x y : Z) := ltZ (absZ x) (absZ y).

Lemma sign_absZ : forall x : Z, leZ OZ (absZ x).
Proof.
intros; elim x; simpl in |- *.
exact I.
intro; simpl in |- *.
exact I.
intro; simpl in |- *.
Admitted.

Lemma tech_le_pos_abs : forall x : Z, leZ OZ x -> absZ x = x.
Proof.
intros x; elim x.
unfold absZ in |- *; reflexivity.
unfold absZ in |- *; reflexivity.
Admitted.

Theorem leZ_antisymmetric : antisym Z leZ.
Proof.
unfold antisym in |- *; intros x y; elim x.
elim y.
reflexivity.
intros; elim H0.
intros; elim H.
intros n; elim y.
intros; elim H.
simpl in |- *; intros; elim (le_antisym n n0 H H0); reflexivity.
intros; elim H.
intros n; elim y.
intros; elim H0.
intros; elim H0.
Admitted.

Lemma tech_lt_abs_OZ : forall x : Z, lt_absZ x (pos 0) -> x = OZ.
Proof.
simple induction x.
reflexivity.
unfold lt_absZ in |- *; unfold absZ in |- *; unfold ltZ in |- *; unfold leZ in |- *; intros.
elim (le_Sn_O n H).
unfold lt_absZ in |- *; unfold absZ in |- *; unfold ltZ in |- *; unfold leZ in |- *; intros.
Admitted.

Lemma tech_posOZ_pos : forall n : nat, leZ OZ (posOZ n).
Proof.
intros; elim n.
simpl in |- *; exact I.
Admitted.

Lemma le_opp_OZ_l : forall x : Z, leZ OZ x -> leZ (oppZ x) OZ.
Proof.
intros x; elim x.
simpl in |- *; intros; exact I.
simpl in |- *; intros; exact I.
Admitted.

Lemma le_opp_OZ2 : forall x y : Z, x = oppZ y -> leZ OZ x -> leZ OZ y -> x = y.
Proof.
intros.
rewrite (le_opp_OZ x y H H0 H1).
rewrite (opp_opp Z IdZ addZ OZ oppZ Z_group y I); elim H.
Admitted.

Lemma le_opp_OZ : forall x y : Z, x = oppZ y -> leZ OZ x -> leZ OZ y -> x = OZ.
Proof.
intros.
apply (leZ_antisymmetric x OZ).
rewrite H.
exact (le_opp_OZ_l y H1).
exact H0.
