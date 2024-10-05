Require Import List.
Import ListNotations.
Require Import Undecidability.PCP.PCP.
Require Import Undecidability.Synthetic.Definitions.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition bin (x: list nat) : list bool := flat_map (fun (a : nat) => true :: (repeat false a) ++ [true]) x.
Definition bin_map A := map (fun '(x, y) => (bin x, bin y)) A.

Theorem reduction : MPCP ⪯ MPCPb.
Proof.
pose f := fun '((x, y), P) => ((bin x, bin y), bin_map P).
exists f.
move=> [[x y] P].
constructor; move=> [A].
{
move=> [HA1 HA2].
exists (bin_map A).
constructor.
{
move=> a /in_map_iff [?] [<- /HA1] ?.
rewrite -/(map _ ((x, y) :: P)).
by apply: in_map.
}
by rewrite tau1_bin_map tau2_bin_map -?bin_appP -eq_binP.
}
rewrite /bin_map -/(map _ ((x, y) :: P)) -/(bin_map _).
move=> [/debin [B [-> ?]]].
rewrite tau1_bin_map tau2_bin_map -?bin_appP -eq_binP => ?.
by exists B.
