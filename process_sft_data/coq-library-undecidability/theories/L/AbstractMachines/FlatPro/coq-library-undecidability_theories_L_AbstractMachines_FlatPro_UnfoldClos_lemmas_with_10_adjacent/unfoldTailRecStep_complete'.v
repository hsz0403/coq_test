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
Admitted.

Lemma unfoldTailRecStep_complete' a k s P s' stack res fuel: unfolds H a k s s' -> exists n, loopSum (n + fuel) unfoldTailRecStep ((a,compile s++P,k)::stack,res) = loopSum fuel unfoldTailRecStep ((a,P,k)::stack,rev (compile s')++res) /\ n <= L_facts.size s' *3.
Proof.
induction 1 in fuel,stack,res,P|-* using unfolds_ind'.
-
eexists (1).
cbn [loopSum unfoldTailRecStep plus compile].
cbn.
destruct (Nat.leb_spec0 k n).
now lia.
easy.
-
subst P0.
edestruct (IHunfolds []) with (fuel := S (fuel +1)) as (n'&eq1&?).
erewrite app_nil_r in eq1.
cbn in eq1.
eexists (S (n' + 2)).
cbn.
destruct (Nat.leb_spec0 k n).
2:now lia.
rewrite H1.
cbn.
replace (n' + 2 + fuel) with (n' + S (fuel + 1)) by nia.
rewrite eq1.
replace (fuel +1) with (S fuel) by nia.
cbn.
repeat (autorewrite with list;cbn).
easy.
-
cbn.
edestruct (IHunfolds (retT :: P)) with (fuel := S fuel) as (n'&eq1&?).
cbn in eq1.
repeat (autorewrite with list;cbn).
rewrite <- eq1.
exists (S n' + 1).
cbn.
now rewrite <- Nat.add_assoc.
-
cbn.
rewrite <- !app_assoc.
specialize (IHunfolds2 ([appT] ++ P)) as (n2&IH2&?).
specialize (IHunfolds1 (compile t ++ [appT] ++ P)) as (n1&IH1&?).
eexists (n1+n2+1).
rewrite <- !Nat.add_assoc.
rewrite IH1,IH2.
cbn.
repeat (autorewrite with list;cbn).
easy.
