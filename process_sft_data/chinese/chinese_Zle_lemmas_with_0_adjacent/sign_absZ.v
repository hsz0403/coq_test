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
exact I.
