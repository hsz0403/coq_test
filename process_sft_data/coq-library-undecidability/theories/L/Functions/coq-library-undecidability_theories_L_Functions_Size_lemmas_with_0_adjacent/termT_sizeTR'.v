From Undecidability.L Require Import Tactics.LTactics Functions.Encoding Prelim.LoopSum Functions.LoopSum Functions.UnboundIteration.
Require Import Nat.
From Undecidability.L.Datatypes Require Import Lists.
Instance term_size' : computable size'.
Proof.
extract.
Abort.
Import Util.L_facts.
Definition sizeTR' '(stack,res) : (list term * nat) + nat := match stack with [] => inr res | s::stack => match s with var n => inl (stack,S (n + res)) | app s t => inl (s::t::stack,S res) | lam s => inl (s::stack,S res) end end.
Fixpoint sizeTR'_fuel (s:term) : nat := match s with var _ => 1 | app s t => 1 + (sizeTR'_fuel s + sizeTR'_fuel t) | lam s => 1 + sizeTR'_fuel s end.
Instance termT_sizeTR' : computableTime' sizeTR' (fun x _ => (let '(stack,res) := x in match stack with var n ::_ => n*11 | _ => 0 end + 35,tt)).
Proof.
extract.
solverec.
unfold LNat.c__add1, LNat.add_time, LNat.c__add.
nia.
Instance termT_size : computableTime' size (fun s _ => (108 * size s + 50,tt)).
Proof.
eexists.
eapply computesTime_timeLeq.
2:{
unshelve (eapply uiter_total_instanceTime with (1 := sizeTR_correct) (preprocessT:=(fun _ _ => (5,tt)))).
4:{
extract.
solverec.
}
2:{
apply termT_sizeTR'.
}
}
split.
2:exact Logic.I.
cbn [fst].
erewrite uiterTime_bound_recRel with (iterT := fun _ '(stack,res) => ((sumn (map size stack)) * 108 + 35 + 9)) (P:= fun n x => True).
{
cbn [length map sumn].
Lia.lia.
}
{
intros n [stack res] H.
cbn.
destruct stack as [|[[]| |]].
2-5:split;[easy|].
all:cbn [length map sumn sizeTR'_fuel size];try Lia.lia.
}
all:easy.

Instance termT_sizeTR' : computableTime' sizeTR' (fun x _ => (let '(stack,res) := x in match stack with var n ::_ => n*11 | _ => 0 end + 35,tt)).
Proof.
extract.
solverec.
unfold LNat.c__add1, LNat.add_time, LNat.c__add.
nia.
