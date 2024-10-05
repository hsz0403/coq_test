Require Import Arith Lia List.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Class Enumerable (X: Type) := { to_nat : X -> nat; of_nat : nat -> X; enumP {x: X} : of_nat (to_nat x) = x }.
Instance nat_Enumerable : Enumerable nat.
Proof.
by exists id id.
Instance bool_Enumerable : Enumerable bool.
Proof.
exists (fun b => if b then 1 else 0) (fun n => if n is 0 then false else true).
by case.
Module nat2_Enumerable.
Definition encode '(x, y) : nat := y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).
Definition decode (n : nat) : nat * nat := nat_rec _ (0, 0) (fun _ '(x, y) => if x is S x then (x, S y) else (S y, 0)) n.
End nat2_Enumerable.
Instance nat2_Enumerable : Enumerable (nat * nat).
Proof.
exists nat2_Enumerable.encode nat2_Enumerable.decode.
move=> ?.
by apply: nat2_Enumerable.decode_encode.
Instance prod_Enumerable {X Y: Type} {enumX: Enumerable X} {enumY: Enumerable Y} : Enumerable (X * Y).
Proof.
exists (fun '(x, y) => to_nat (to_nat x, to_nat y)) (fun n => match of_nat n with | (n1, n2) => (of_nat n1, of_nat n2) end).
move=> [x y].
by rewrite ?enumP.
Instance sum_Enumerable {X Y: Type} {enumX: Enumerable X} {enumY: Enumerable Y} : Enumerable (X + Y).
Proof.
exists (fun t => match t with | inl x => to_nat (0, to_nat x) | inr y => to_nat (1, to_nat y) end) (fun n => match of_nat n with | (0, n) => inl (of_nat n) | (1, n) => inr (of_nat n) | _ => inl (of_nat n) end).
by case => ?; rewrite ?enumP.
Module list_Enumerable.
Section list_Enumerable_Section.
Variables (X: Type) (enumX: Enumerable X).
Fixpoint encode (L: list X) : nat := if L is x :: L then 1+nat2_Enumerable.encode (1 + to_nat x, encode L) else 1+nat2_Enumerable.encode (0, 0).
Fixpoint decode (i: nat) (n: nat) : list X := if i is S i then match nat2_Enumerable.decode (n-1) with | (0, _) => [] | (S n1, n2) => (of_nat n1) :: decode i n2 end else [].
Opaque nat2_Enumerable.encode nat2_Enumerable.decode.
End list_Enumerable_Section.
End list_Enumerable.
Instance list_Enumerable {X: Type} {enumX: Enumerable X} : Enumerable (list X).
Proof.
exists (list_Enumerable.encode X enumX) (fun n => list_Enumerable.decode X enumX n n).
move=> ?.
by apply: list_Enumerable.decode_encode.

Lemma to_nat_inj {X: Type} {enumX: Enumerable X} {x y: X}: to_nat x = to_nat y <-> x = y.
Proof.
constructor; last by move->.
move /(f_equal of_nat).
Admitted.

Lemma enumarableI {X Y: Type} {enum: Enumerable X} (to_X: Y -> X) (of_X: X -> Y) : (forall (y: Y), of_X (to_X y) = y) -> Enumerable Y.
Proof.
move=> cancel.
exists (fun y => to_nat (to_X y)) (fun x => of_X (of_nat x)).
move=> y.
Admitted.

Instance nat_Enumerable : Enumerable nat.
Proof.
Admitted.

Instance bool_Enumerable : Enumerable bool.
Proof.
exists (fun b => if b then 1 else 0) (fun n => if n is 0 then false else true).
Admitted.

Lemma decode_encode {xy: nat * nat} : decode (encode xy) = xy.
Proof.
move Hn: (encode xy) => n.
elim: n xy Hn.
{
by move=> [[|?] [|?]].
}
move=> n IH [x [|y [H]]] /=.
-
move: x => [|x [H]] /=; first done.
by rewrite (IH (0, x)) /= -?H ?Nat.add_0_r.
-
Admitted.

Lemma encode_non_decreasing (x y: nat) : x + y <= encode (x, y).
Proof.
Admitted.

Instance nat2_Enumerable : Enumerable (nat * nat).
Proof.
exists nat2_Enumerable.encode nat2_Enumerable.decode.
move=> ?.
Admitted.

Instance prod_Enumerable {X Y: Type} {enumX: Enumerable X} {enumY: Enumerable Y} : Enumerable (X * Y).
Proof.
exists (fun '(x, y) => to_nat (to_nat x, to_nat y)) (fun n => match of_nat n with | (n1, n2) => (of_nat n1, of_nat n2) end).
move=> [x y].
Admitted.

Instance sum_Enumerable {X Y: Type} {enumX: Enumerable X} {enumY: Enumerable Y} : Enumerable (X + Y).
Proof.
exists (fun t => match t with | inl x => to_nat (0, to_nat x) | inr y => to_nat (1, to_nat y) end) (fun n => match of_nat n with | (0, n) => inl (of_nat n) | (1, n) => inr (of_nat n) | _ => inl (of_nat n) end).
Admitted.

Lemma decode_encode {L: list X} : decode (encode L) (encode L) = L.
Proof.
suff: forall i, encode L <= i -> decode i (encode L) = L by (apply; lia).
move=> i.
elim: i L; first by (move=> [|? L] /=; lia).
move=> i IH [|x L] /= ?; first done.
rewrite Nat.sub_0_r nat2_Enumerable.decode_encode enumP IH; last done.
have := nat2_Enumerable.encode_non_decreasing (S (@to_nat X enumX x)) (encode L).
Admitted.

Instance list_Enumerable {X: Type} {enumX: Enumerable X} : Enumerable (list X).
Proof.
exists (list_Enumerable.encode X enumX) (fun n => list_Enumerable.decode X enumX n n).
move=> ?.
by apply: list_Enumerable.decode_encode.
