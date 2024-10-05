Require Import List Relation_Operators.
Definition stack : Set := list bool.
Definition state : Set := nat.
Definition config : Set := stack * stack * state.
Definition dir : Set := bool.
Definition symbol : Set := bool.
Definition instruction : Set := state * state * symbol * symbol * dir.
Definition ssm : Set := list instruction.
Inductive step (M : ssm) : config -> config -> Prop := (* transition AaxB -> AybB *) | step_l (x y: state) (a b: symbol) (A B: stack) : In (x, y, a, b, true) M -> step M (a::A, B, x) (A, b::B, y) (* transition AxbB -> AayB *) | step_r (x y: state) (a b: symbol) (A B: stack) : In (x, y, b, a, false) M -> step M (A, b::B, x) (a::A, B, y).
Definition reachable (M: ssm) : config -> config -> Prop := clos_refl_trans config (step M).
Definition confluent (M: ssm) := forall (X Y1 Y2: config), reachable M X Y1 -> reachable M X Y2 -> exists (Z: config), reachable M Y1 Z /\ reachable M Y2 Z.
Definition cssm := { M : ssm | confluent M }.
Definition bounded (M: ssm) (n: nat) : Prop := forall (X: config), exists (L: list config), (forall (Y: config), reachable M X Y -> In Y L) /\ length L <= n.
Definition CSSM_UB (M : cssm) := exists (n: nat), bounded (proj1_sig M) n.