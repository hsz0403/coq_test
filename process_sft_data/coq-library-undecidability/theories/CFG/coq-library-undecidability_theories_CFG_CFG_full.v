Require Import List.
Import ListNotations.
Definition stack (X : Type) := list (list X * list X).
Notation sig := nat.
Definition rule : Type := sig * list sig.
Definition cfg : Type := sig * list rule.
Definition rules (G : cfg) := snd G.
Definition startsym (G : cfg) := fst G.
Inductive rew_cfg : cfg -> list sig -> list sig -> Prop := | rewR R x a y v : In (a, v) (rules R) -> rew_cfg R (x++[a]++y) (x++v++y).
Hint Constructors rew_cfg : core.
Inductive rewt (S: cfg) (x: list sig) : list sig -> Prop := | rewtRefl : rewt S x x | rewtRule y z : rewt S x y -> rew_cfg S y z -> rewt S x z.
Hint Constructors rewt : core.
Definition terminal G x := ~ exists y, rew_cfg G x y.
Definition L (G : cfg) x := rewt G [startsym G] x /\ terminal G x.
Definition CFP : cfg -> Prop := fun G => exists x, L G x /\ x = List.rev x.
Definition CFI : cfg * cfg -> Prop := fun '(G1, G2) => exists x, L G1 x /\ L G2 x.