Require Import List.
Definition State : Set := nat.
Record Config : Set := mkConfig { state : State; value1 : nat; value2 : nat }.
Inductive Instruction : Set := | inc : bool -> Instruction | dec : bool -> State -> Instruction.
Definition Cm2 : Set := list Instruction.
Definition step (M: Cm2) (x: Config) : Config := match nth_error M (state x) with | None => x (* halting configuration *) | Some (inc b) => (* increase counter, goto next state*) {| state := 1 + (state x); value1 := (if b then 0 else 1) + (value1 x); value2 := (if b then 1 else 0) + (value2 x) |} | Some (dec b y) => (* decrease counter, if successful goto state y *) if b then match value2 x with | 0 => {| state := 1 + (state x); value1 := value1 x; value2 := 0 |} | S n => {| state := y; value1 := value1 x; value2 := n |} end else match value1 x with | 0 => {| state := 1 + (state x); value1 := 0; value2 := value2 x |} | S n => {| state := y; value1 := n; value2 := value2 x |} end end.
Arguments step _ !x /.
Definition halting (M : Cm2) (x: Config) : Prop := step M x = x.
Definition CM2_HALT : Cm2 -> Prop := fun M => exists (n: nat), halting M (Nat.iter n (step M) {| state := 0; value1 := 0; value2 := 0 |}).