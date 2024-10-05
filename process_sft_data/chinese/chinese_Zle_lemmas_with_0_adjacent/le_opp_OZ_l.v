Require Export Arith.
Require Export misc.
Require Export groups.
Require Export Zbase.
Require Export Z_succ_pred.
Require Export Zadd.
Definition leZ (x y : Z) := match x return Prop with | OZ => match y return Prop with | OZ => True | pos n => True | neg n => False end | pos n => match y return Prop with | OZ => False | pos m => n <= m | neg m => False end | neg n => match y return Prop with | OZ => True | pos m => True | neg m => m <= n end end.
Definition ltZ (x y : Z) := leZ (succZ x) y.
Definition lt_absZ (x y : Z) := ltZ (absZ x) (absZ y).

Lemma le_opp_OZ_l : forall x : Z, leZ OZ x -> leZ (oppZ x) OZ.
Proof.
intros x; elim x.
simpl in |- *; intros; exact I.
simpl in |- *; intros; exact I.
intros; elim H.
