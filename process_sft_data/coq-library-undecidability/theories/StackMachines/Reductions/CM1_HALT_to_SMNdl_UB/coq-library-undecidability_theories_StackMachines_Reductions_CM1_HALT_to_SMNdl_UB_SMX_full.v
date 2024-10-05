Require Import List.
Import ListNotations.
Require Import Relation_Operators.
Set Default Proof Using "Type".
Section SMX.
Context {State Symbol : Set}.
Definition Stack : Set := list Symbol.
Definition Config : Set := Stack * Stack * State.
Definition Instruction : Set := Config * Config * bool.
Definition SMX : Set := list Instruction.
Inductive step (M : SMX) : Config -> Config -> Prop := | transition (v w r s r' s': Stack) (x y: State) (b: bool) : In ((r, s, x), (r', s', y), b) M -> step M (r ++ v, s ++ w, x) match b with | false => (r' ++ v, s' ++ w, y) | true => (s' ++ w, r' ++ v, y) end.
Definition deterministic (M: SMX) := forall (X Y Z: Config), step M X Y -> step M X Z -> Y = Z.
Definition reachable (M: SMX) : Config -> Config -> Prop := clos_refl_trans Config (step M).
Definition bounded (M: SMX) (n: nat) : Prop := forall (X: Config), exists (L: list Config), (forall (Y: Config), reachable M X Y -> In Y L) /\ length L <= n.
End SMX.