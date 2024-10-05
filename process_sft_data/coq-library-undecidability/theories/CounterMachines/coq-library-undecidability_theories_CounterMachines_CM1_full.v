Require Import List Nat.
Definition State : Set := nat.
Record Config : Set := mkConfig { state : State; value : nat }.
Definition Instruction : Set := State * nat.
Definition Cm1 : Set := list Instruction.
Definition step (M: Cm1) (x: Config) : Config := match (value x), (nth_error M (state x)) with | 0, _ => x (* halting configuration *) | _, None => x (* halting configuration *) | _, Some (p, n) => match modulo (value x) (n+1) with | 0 => {| state := p; value := ((value x) * (n+2)) / (n+1) |} | _ => {| state := 1 + state x; value := value x |} end end.
Arguments step _ !x /.
Definition halting (M : Cm1) (x: Config) : Prop := step M x = x.
Definition CM1_HALT : { M : Cm1 | Forall (fun '(_, n) => n < 4) M } -> Prop := fun '(exist _ M _) => exists n, halting M (Nat.iter n (step M) {| state := 0; value := 1 |}).