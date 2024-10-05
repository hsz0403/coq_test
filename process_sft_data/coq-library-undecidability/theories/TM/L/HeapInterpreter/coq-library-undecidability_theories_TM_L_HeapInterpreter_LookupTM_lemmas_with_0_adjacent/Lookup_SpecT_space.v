From Undecidability Require Import TM.Code.ProgrammingTools LM_heap_def.
From Undecidability.TM.L Require Import Alphabets.
From Undecidability Require Import TM.Code.ListTM TM.Code.CasePair TM.Code.CaseSum TM.Code.CaseNat Hoare.Hoare.
Set Default Proof Using "Type".
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Section Lookup.
Variable sigLookup : finType.
Variable retr_clos_lookup : Retract sigHClos sigLookup.
Variable retr_heap_lookup : Retract sigHeap sigLookup.
Definition retr_nat_clos_ad : Retract sigNat sigHClos := Retract_sigPair_X _ _.
Definition retr_nat_lookup_clos_ad : Retract sigNat sigLookup := ComposeRetract retr_clos_lookup retr_nat_clos_ad.
Definition retr_nat_clos_var : Retract sigNat sigHClos := Retract_sigPair_Y _ _.
Definition retr_nat_lookup_clos_var : Retract sigNat sigLookup := ComposeRetract retr_clos_lookup retr_nat_clos_var.
Definition retr_nat_heap_entry : Retract sigNat sigHeap := Retract_sigList_X (Retract_sigOption_X (Retract_sigPair_Y _ (Retract_id _))).
Local Definition retr_nat_lookup_entry : Retract sigNat sigLookup := ComposeRetract retr_heap_lookup retr_nat_heap_entry.
Definition retr_clos_heap : Retract sigHClos sigHeap := _.
Definition retr_clos_lookup_heap : Retract sigHClos sigLookup := ComposeRetract retr_heap_lookup retr_clos_heap.
Definition retr_hent_heap : Retract sigHEntr sigHeap := _.
Local Definition retr_hent_lookup : Retract sigHEntr sigLookup := ComposeRetract retr_heap_lookup retr_hent_heap.
Definition retr_hent'_heap : Retract sigHEntr' sigHeap := _.
Local Definition retr_hent'_lookup : Retract sigHEntr' sigLookup := ComposeRetract retr_heap_lookup retr_hent'_heap.
Definition Lookup_Step : pTM sigLookup^+ (option bool) 5 := If (Nth' retr_heap_lookup retr_nat_lookup_clos_ad @ [|Fin0; Fin1; Fin4; Fin3|]) (If (CaseOption sigHEntr'_fin ⇑ retr_hent_lookup @ [|Fin4|]) (CasePair sigHClos_fin sigHAdd_fin ⇑ retr_hent'_lookup @ [|Fin4; Fin3|];; If (CaseNat ⇑ retr_nat_lookup_clos_var @ [|Fin2|]) (Return (CopyValue _ @ [|Fin4; Fin1|];; (* n = S n' *) Translate retr_nat_lookup_entry retr_nat_lookup_clos_ad @ [|Fin1|];; Reset _ @ [|Fin4|];; Reset _ @ [|Fin3 |]) None) (* continue *) (Return (Reset _ @ [|Fin4|];; (* n = 0 *) Reset _ @ [|Fin2|];; Translate retr_clos_lookup_heap retr_clos_lookup @ [|Fin3|]) (Some true))) (* return true *) (Return Nop (Some false))) (* return false *) (Return Nop (Some false)) (* return false *) .
Definition Lookup_Step_size (H : Heap) (a n : nat) : Vector.t (nat->nat) 5 := match nth_error H a with | Some (Some (g, b)) => match n with | S n' => [|(* 0 *) Nth'_size H a @>Fin0; (* 1 *) Nth'_size H a @>Fin1 >> CopyValue_size b; (* 2 *) S; (* 3 *) Nth'_size H a @>Fin3 >> CasePair_size1 g >> Reset_size g; (* 4 *) Nth'_size H a @>Fin2 >> CaseOption_size_Some >> CasePair_size0 g >> Reset_size b|] | 0 => [|(* 0 *) Nth'_size H a @>Fin0; (* 1 *) Nth'_size H a @>Fin1; (* 2 *) Reset_size 0; (* 3 *) Nth'_size H a @>Fin3 >> CasePair_size1 g; (* 4 *) Nth'_size H a @>Fin2 >> CaseOption_size_Some >> CasePair_size0 g >> Reset_size b|] end | _ => default (* not specified *) end.
Local Definition Lookup_Step_steps_CaseNat (n: nat) (e': HClos * HAdd) := let (g,b) := (fst e', snd e') in match n with | S _ => 1 + CopyValue_steps b + 1 + Translate_steps b + 1 + Reset_steps b + Reset_steps g | O => 1 + Reset_steps b + 1 + Reset_steps 0 + Translate_steps g end.
Local Definition Lookup_Step_steps_CaseOption (n:nat) (e: HEntr) := match e with | Some ((g, b) as e') => 1 + CasePair_steps g + 1 + CaseNat_steps + Lookup_Step_steps_CaseNat n e' | None => 0 end.
Local Definition Lookup_Step_steps_Nth' H a n := match nth_error H a with | Some e => 1 + CaseOption_steps + Lookup_Step_steps_CaseOption n e | None => 0 end.
Definition Lookup_Step_steps (H: Heap) (a: HAdd) (n: nat) := 1 + Nth'_steps H a + Lookup_Step_steps_Nth' H a n.
Definition Lookup := While Lookup_Step.
Fixpoint Lookup_size (H : Heap) (a n : nat) {struct n} : Vector.t (nat -> nat) 5 := match nth_error H a with | Some (Some (g, b)) => match n with | S n' => Lookup_Step_size H a n >>> Lookup_size H b n' | 0 => Lookup_Step_size H a n end | _ => default (* not specified *) end.
Definition Lookup_Rel : pRel sigLookup^+ bool 5 := fun tin '(yout, tout) => forall (H: Heap) (a n: nat) (s0 s1 s2 s3 s4 : nat), let size := Lookup_size H a n in tin[@Fin0] ≃(;s0) H -> tin[@Fin1] ≃(retr_nat_lookup_clos_ad ; s1) a -> tin[@Fin2] ≃(retr_nat_lookup_clos_var; s2) n -> isVoid_size tin[@Fin3] s3 -> isVoid_size tin[@Fin4] s4 -> match yout with | true => exists g, lookup H a n = Some g /\ tout[@Fin0] ≃(;size @>Fin0 s0) H /\ (* [H] is saved *) isVoid_size tout[@Fin1] (size @>Fin1 s1) /\ (* [a] is discarded *) isVoid_size tout[@Fin2] (size @>Fin2 s2) /\ (* [n] is discarded *) tout[@Fin3] ≃(retr_clos_lookup; size @>Fin3 s3) g /\ (* result *) isVoid_size tout[@Fin4] (size @>Fin4 s4) (* internal tape *) | false => lookup H a n = None (* Tapes are not specified *) end.
Arguments Lookup_Step_size : simpl never.
Fixpoint Lookup_steps (H : Heap) (a : HAdd) (n : nat) : nat := match nth_error H a with | Some (Some (g, b)) => match n with | 0 => Lookup_Step_steps H a n | S n' => 1 + Lookup_Step_steps H a n + Lookup_steps H b n' end | _ => Lookup_Step_steps H a n end.
Definition Lookup_T : tRel sigLookup^+ 5 := fun tin k => exists (H: Heap) (a n: nat), tin[@Fin0] ≃ H /\ tin[@Fin1] ≃(retr_nat_lookup_clos_ad) a /\ tin[@Fin2] ≃(retr_nat_lookup_clos_var) n /\ isVoid tin[@Fin3] /\ isVoid tin[@Fin4] /\ Lookup_steps H a n <= k.
End Lookup.
Arguments Lookup_steps : simpl never.
Arguments Lookup_size : simpl never.

Lemma Lookup_SpecT_space H a n ss: TripleT ≃≃([],withSpace [| ≃(_) H ; ≃(retr_nat_lookup_clos_ad) a;≃(retr_nat_lookup_clos_var) n;Void;Void |] ss) (Lookup_steps H a n) Lookup (fun yout => ≃≃([yout = match lookup H a n with Some _ => true | _ => false end] , withSpace match lookup H a n with Some g => [| ≃(_) H;Void;Void;≃(retr_clos_lookup) g; Void|] | _ => SpecVTrue end (appSize (Lookup_size H a n) ss))).
Proof.
unfold Lookup.
eapply While_SpecTReg with (PRE := fun '(a,n,ss) => (_,_))(INV := fun '(a,n,ss) y => ([y = match nth_error H a with | Some (Some _) => match n with | 0 => Some true | S _ => None end | _ => Some false end],_)) (POST := fun '(a,n,ss) y => (_,_)) (f__step := fun '(a,n,ss) => Lookup_Step_steps H a n ) (f__loop := fun '(a,n,ss) => _ ) (x:= (a,n,ss));clear a n ss;intros [[a n] ss].
{
eapply ConsequenceT.
eapply Lookup_Step_SpecT_space.
2:intros.
1,2:cbn - [appSize SpecVTrue].
1,2:now tspec_ext.
reflexivity.
}
all:cbn - [SpecVTrue appSize Lookup_size].
remember (Lookup_size H a n) as F eqn:HF.
remember (Lookup_steps H a n) as F' eqn:HF'.
split.
-
destruct n;unfold Lookup_size in HF;unfold Lookup_steps in HF';fold Lookup_size in HF;fold Lookup_steps in HF'.
+
intros ? H'.
cbn[lookup Lookup_Step_size].
destruct nth_error as [[[]| ]| ] eqn:Hnth.
all:split;[ | subst F';reflexivity].
all:revert H';intros [= ->].
now rewrite <- HF.
1-2:tspec_ext.
+
intros ? H'.
cbn [lookup].
unfold Lookup_Step_steps.
destruct nth_error as [[[]| ]| ] eqn:Hnth.
easy.
all:split;[ | subst F';reflexivity].
all:inv H'.
all:tspec_ext.
-
destruct (nth_error H a) as [[[g' b]| ]| ] eqn:Hnth.
2-3:easy.
destruct n as [ | n].
easy.
intros _.
cbn [lookup].
rewrite Hnth.
unfold Lookup_size in HF;fold Lookup_size in HF.
rewrite Hnth in HF.
eexists (b,n,_).
repeat apply conj.
+
subst F.
cbn.
tspec_ext.
+
subst F'.
cbn.
rewrite Hnth.
reflexivity.
+
intros.
subst F.
reflexivity.
