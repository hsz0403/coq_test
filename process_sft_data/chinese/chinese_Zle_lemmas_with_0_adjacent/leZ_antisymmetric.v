Require Export Arith.
Require Export misc.
Require Export groups.
Require Export Zbase.
Require Export Z_succ_pred.
Require Export Zadd.
Definition leZ (x y : Z) := match x return Prop with | OZ => match y return Prop with | OZ => True | pos n => True | neg n => False end | pos n => match y return Prop with | OZ => False | pos m => n <= m | neg m => False end | neg n => match y return Prop with | OZ => True | pos m => True | neg m => m <= n end end.
Definition ltZ (x y : Z) := leZ (succZ x) y.
Definition lt_absZ (x y : Z) := ltZ (absZ x) (absZ y).

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
simpl in |- *; intros; elim (le_antisym n0 n H H0); reflexivity.
