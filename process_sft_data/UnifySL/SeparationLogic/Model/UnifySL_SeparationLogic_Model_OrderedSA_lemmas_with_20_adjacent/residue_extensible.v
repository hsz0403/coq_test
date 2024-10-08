Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.
Definition increasing {worlds: Type} {R: Relation worlds} {J: Join worlds}: worlds -> Prop := fun m => forall n n', join m n n' -> n <= n'.
Definition increasing' {worlds: Type} {R: Relation worlds} {J: Join worlds}: worlds -> Prop := fun m => forall n, m <= n -> increasing n.
Class IncreasingSeparationAlgebra (worlds: Type) {R: Relation worlds} {J: Join worlds }: Type := { all_increasing: forall x: worlds, increasing x }.
Definition residue {worlds: Type} {R: Relation worlds} {J: Join worlds} (m n: worlds): Prop := exists n', join n n' m /\ m <= n'.
Class ResidualSeparationAlgebra (worlds: Type) {R: Relation worlds} {J: Join worlds}: Type := { residue_exists: forall n: worlds, exists m, residue n m; }.
Class UnitalSeparationAlgebra (worlds: Type) {R: Relation worlds} {J: Join worlds}: Type := { incr_exists: forall n: worlds, exists m, residue n m /\ increasing m }.
Class UnitalSeparationAlgebra' (worlds: Type) {R: Relation worlds} {J: Join worlds}: Type := { incr'_exists: forall n: worlds, exists m, residue n m /\ increasing' m }.
Class IncreasingJoinSelfSeparationAlgebra (worlds: Type) {R: Relation worlds} {J: Join worlds}: Type := incr_join_self: forall m, increasing m -> join m m m.
Class IncreasingSplitSmallerSeparationAlgebra (worlds: Type) {R: Relation worlds} {J: Join worlds}: Type := incr_split_smaller: forall m1 m2 m, increasing m -> join m1 m2 m -> m1 <= m.
Class UpwardsClosedSeparationAlgebra (worlds: Type) {R: Relation worlds} {J: Join worlds}: Type := join_Korder_up: forall m n m1 m2: worlds, join m1 m2 m -> m <= n -> exists n1 n2, join n1 n2 n /\ m1 <= n1 /\ m2 <= n2.
Class DownwardsClosedSeparationAlgebra (worlds: Type) {R: Relation worlds} {J: Join worlds}: Type := join_Korder_down: forall m1 m2 m n1 n2: worlds, join m1 m2 m -> n1 <= m1 -> n2 <= m2 -> exists n, join n1 n2 n /\ n <= m.

Lemma incr_incr' {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation} {J: Join worlds}: forall m, increasing' m -> increasing m.
Proof.
intros.
apply H.
Admitted.

Lemma disc_incr_unit {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation} {J: Join worlds}: IdentityKripkeIntuitionisticModel worlds -> forall e, increasing e <-> unit_element e.
Proof.
intros; split; intros; hnf; intros.
-
hnf; intros.
apply H.
apply H0; auto.
-
Admitted.

Lemma unital_is_residual {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation} {J: Join worlds}: UnitalSeparationAlgebra worlds -> ResidualSeparationAlgebra worlds.
Proof.
constructor; intros.
destruct (incr_exists n) as [m [RES _]].
Admitted.

Lemma incr_unital_iff_residual {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation} {J: Join worlds}: IncreasingSeparationAlgebra worlds -> UnitalSeparationAlgebra worlds <-> ResidualSeparationAlgebra worlds.
Proof.
intros; split.
-
apply unital_is_residual; auto.
-
constructor; intros.
destruct (residue_exists n) as [m RES].
exists m; split; auto.
Admitted.

Lemma residual_extensible {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation} {J: Join worlds} {SA: SeparationAlgebra worlds} {dSA: DownwardsClosedSeparationAlgebra worlds} {resSA: ResidualSeparationAlgebra worlds}: forall u, exists e v, join u e v.
Proof.
intros.
destruct (residue_exists u) as [e ?].
apply residue_extensible in H.
destruct H as [v ?].
apply join_comm in H.
Admitted.

Lemma residue_extensible {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation} {J: Join worlds} {dSA: DownwardsClosedSeparationAlgebra worlds}: forall e u, residue u e -> exists v, join e u v.
Proof.
intros.
destruct H as [u' [? ?]].
pose proof join_Korder_down.
pose proof H1 _ _ _ _ _ H ltac:(reflexivity) H0.
firstorder.
