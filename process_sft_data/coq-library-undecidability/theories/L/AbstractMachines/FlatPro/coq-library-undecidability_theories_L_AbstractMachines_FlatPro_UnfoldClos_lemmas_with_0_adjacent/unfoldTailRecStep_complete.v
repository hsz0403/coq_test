From Undecidability.L.AbstractMachines.FlatPro Require Import LM_heap_correct LM_heap_def.
From Undecidability.L.Prelim Require Import LoopSum.
Set Default Proof Using "Type".
Section fixH.
Variable H : Heap.
Definition unfoldTailRecStep '(stack,res) : (list (HClos*nat) * Pro) + option Pro := match stack with | ((a,P),k)::stack => match P with c::P => match c with varT n => if ( k <=? n) then match lookup H a (n-k) with | Some (b,Q) => inl (((b,Q),1)::(a,retT::P,S k)::stack,lamT::res) | None => inr None end else inl ((a,P,k)::stack,varT n::res) | appT => inl ((a,P,k)::stack,appT::res) | lamT => inl ((a,P,S k)::stack,lamT::res) | retT => inl ((a,P,pred k)::stack,retT::res) end | [] => inl (stack,res) end | [] => inr (Some res) end.
End fixH.

Lemma unfoldTailRecStep_complete a k s s' n: unfolds H a k s s' -> L_facts.size s' * 3 + 2 <= n -> loopSum n unfoldTailRecStep ([(a,(compile s),k)],[]) = Some (Some (rev (compile s'))).
Proof.
intros ? ?.
edestruct unfoldTailRecStep_complete' with (P:=@nil Tok) as (n'&eq1&?).
eassumption.
rewrite app_nil_r in eq1.
eapply loopSum_mono with (n:=n'+2).
now Lia.nia.
rewrite eq1.
cbn.
now rewrite app_nil_r.
