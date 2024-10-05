Require Import List.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.Synthetic.Definitions.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition bin (x: list nat) : list bool := flat_map (fun (a : nat) => true :: (repeat false a) ++ [true]) x.
Definition bin_map A := map (fun '(x, y) => (bin x, bin y)) A.

Lemma debin {A: list (list bool * list bool)} {P : list (list nat * list nat)} : incl A (bin_map P) -> exists B, A = bin_map B /\ incl B P.
Proof.
elim: A.
{
move=> *.
exists [].
by constructor.
}
move=> a A IH /incl_consE [+ +].
move /(@in_map_iff) => [[x' y'] [<- ?]].
move /IH => [B [-> HB]].
exists ((x', y') :: B).
constructor; first done.
by move=> ? [<- | /HB].
