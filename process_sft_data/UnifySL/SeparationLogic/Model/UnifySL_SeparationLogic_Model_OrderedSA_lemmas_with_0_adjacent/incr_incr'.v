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
reflexivity.
