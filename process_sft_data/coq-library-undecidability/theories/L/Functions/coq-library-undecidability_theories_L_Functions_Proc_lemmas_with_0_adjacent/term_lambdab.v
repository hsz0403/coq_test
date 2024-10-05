From Undecidability.L Require Import Computability.Decidability Datatypes.LNat L.
Require Import Nat.
Fixpoint boundb (k : nat) (t : term) : bool := match t with | var n => negb (k <=? n) | app s t => andb (boundb k s) (boundb k t) | lam s => boundb (S k) s end.
Instance term_boundb : computableTime' boundb (fun _ _ => (5,fun s _ => (size s * 31+9,tt))).
Proof.
extract.
solverec.
unfold c__leb2, leb_time, c__leb.
nia.
Definition closedb := boundb 0.
Instance termT_closedb : computableTime' closedb (fun s _ => (size s * 31+15,tt)).
Proof.
change closedb with (fun x => boundb 0 x).
extract.
solverec.
Definition lambdab (t : term) : bool := match t with | lam _ => true | _ => false end.
Instance term_lambdab : computableTime' lambdab (fun _ _ => (11,tt)).
Proof.
extract.
solverec.

Instance term_lambdab : computableTime' lambdab (fun _ _ => (11,tt)).
Proof.
extract.
solverec.
