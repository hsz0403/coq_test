From Undecidability.TM.Code Require Import ProgrammingTools.
From Undecidability Require Import TM.Code.CaseNat.
Local Arguments skipn { A } !n !l.
Local Arguments Encode_nat : simpl never.
Definition Add_Step : pTM sigNat^+ (option unit) 2 := If (LiftTapes CaseNat [|Fin1|]) (Return (LiftTapes Constr_S [|Fin0|]) None) (Return Nop (Some tt)).
Definition Add_Loop : pTM sigNat^+ unit 2 := While Add_Step.
Definition Add_Main : pTM sigNat^+ unit 4 := LiftTapes (CopyValue _) [|Fin1; Fin2|];; (* copy n to a *) LiftTapes (CopyValue _) [|Fin0; Fin3|];; (* copy m to b *) LiftTapes Add_Loop [|Fin2; Fin3|].
Definition Add := Add_Main;; (* Initialisation and main loop *) LiftTapes (Reset _) [|Fin3|].
Definition Add_Step_Rel : pRel sigNat^+ (option unit) 2 := fun tin '(yout, tout) => forall a b sa sb, tin [@Fin0] ≃(;sa) a -> tin [@Fin1] ≃(;sb) b -> match yout, b with | Some tt, O => (* break *) tout[@Fin0] ≃(;sa) a /\ tout[@Fin1] ≃(;sb) b | None, S b' => tout[@Fin0] ≃(;pred sa) S a /\ tout[@Fin1] ≃(;S sb) b' | _, _ => False end.
Definition Add_Loop_Rel : pRel sigNat^+ unit 2 := ignoreParam ( fun tin tout => forall a b sa sb, tin [@Fin0] ≃(;sa) a -> tin [@Fin1] ≃(;sb) b -> tout[@Fin0] ≃(;sa-b) b + a /\ tout[@Fin1] ≃(;sb+b) 0 ).
Definition Add_Main_Rel : pRel sigNat^+ unit 4 := ignoreParam ( fun tin tout => forall m n sm sn s2 s3, tin [@Fin0] ≃(;sm) m -> tin [@Fin1] ≃(;sn) n -> isVoid_size tin[@Fin2] s2 -> isVoid_size tin[@Fin3] s3 -> tout[@Fin0] ≃(;sm) m /\ tout[@Fin1] ≃(;sn) n /\ tout[@Fin2] ≃(; s2 - (S (size n)) - m) m + n /\ tout[@Fin3] ≃(; s3 - (2 + m) + m) 0 ).
Goal forall (x m : nat), x - m + m >= x.
Proof.
intros.
lia.
Definition Add_space2 (m n : nat) (so : nat) := so + m - n - 2.
Definition Add_space3 (m : nat) (s3 : nat) := 2 + (s3 - (2 + m) + m).
Definition Add_Rel : pRel sigNat^+ unit 4 := ignoreParam (fun tin tout => forall (m : nat) (n : nat) (sx sy so s3 : nat), tin[@Fin0] ≃(;sx) m -> tin[@Fin1] ≃(;sy) n -> isVoid_size tin[@Fin2] so -> isVoid_size tin[@Fin3] s3 -> tout[@Fin0] ≃(;sx) m /\ (* First input value stayes unchanged *) tout[@Fin1] ≃(;sy) n /\ (* Second input value stayes unchanged *) tout[@Fin2] ≃(;Add_space2 m n so) (m + n) /\ isVoid_size tout[@Fin3] (Add_space3 m s3) ).
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Definition Add_Loop_steps b := 9 + 10 * b.
Definition Add_Main_steps m n := 85 + 12 * n + 22 * m.
Definition Add_Main_T : tRel sigNat^+ 4 := fun tin k => exists m n, tin[@Fin0] ≃ m /\ tin[@Fin1] ≃ n /\ isVoid tin[@Fin2] /\ isVoid tin[@Fin3] /\ Add_Main_steps m n <= k.
Definition Add_steps m n := 98 + 12 * n + 22 * m.
Definition Add_T : tRel sigNat^+ 4 := fun tin k => exists m n, tin[@Fin0] ≃ m /\ tin[@Fin1] ≃ n /\ isVoid tin[@Fin2] /\ isVoid tin[@Fin3] /\ Add_steps m n <= k.
Definition Mult_Step : pTM sigNat^+ (option unit) 5 := If (LiftTapes CaseNat [|Fin0|]) (Return ( LiftTapes Add [|Fin1; Fin2; Fin3; Fin4|];; (* Add(n, c, c') *) LiftTapes (MoveValue _) [|Fin3; Fin2|] ) (None)) (* continue *) (Return Nop (Some tt)).
Definition Mult_Loop := While Mult_Step.
Definition Mult_Main : pTM sigNat^+ unit 6 := LiftTapes (CopyValue _) [|Fin0; Fin5|];; (* m' := m *) LiftTapes (Constr_O) [|Fin2|];; (* c := 0 *) LiftTapes Mult_Loop [|Fin5; Fin1; Fin2; Fin3; Fin4|].
Definition Mult : pTM sigNat^+ unit 6 := Mult_Main;; LiftTapes (Reset _) [|Fin5|].
Definition Mult_Step_Rel : pRel sigNat^+ (option unit) 5 := fun tin '(yout, tout) => forall (c m' n : nat) (sm sn sc s3 s4 : nat), tin[@Fin0] ≃(;sm) m' -> tin[@Fin1] ≃(;sn) n -> tin[@Fin2] ≃(;sc) c -> isVoid_size tin[@Fin3] s3 -> isVoid_size tin[@Fin4] s4 -> match yout, m' with | (Some tt), O => (* return *) tout[@Fin0] ≃(;sm) m' /\ tout[@Fin1] ≃(;sn) n /\ tout[@Fin2] ≃(;sc) c /\ isVoid_size tout[@Fin3] s3 /\ isVoid_size tout[@Fin4] s4 | None, S m'' => (* continue *) tout[@Fin0] ≃(;S sm) m'' /\ tout[@Fin1] ≃(;sn) n /\ tout[@Fin2] ≃(;sc-n) n + c /\ isVoid_size tout[@Fin3] (2 + n + c + Add_space2 n c s3) /\ isVoid_size tout[@Fin4] (Add_space3 n s4) | _, _ => False end.
Fixpoint Mult_Loop_space34 (m' n c : nat) (s3 s4 : nat) { struct m' } : Vector.t nat 2 := match m' with | 0 => [| s3; s4 |] | S m'' => Mult_Loop_space34 m'' n (n + c) (2 + n + c + Add_space2 n c s3) (Add_space3 n s4) end.
Definition Mult_Loop_Rel : pRel sigNat^+ unit 5 := ignoreParam ( fun tin tout => forall c m' n sm sn sc s3 s4, tin[@Fin0] ≃(;sm) m' -> tin[@Fin1] ≃(;sn) n -> tin[@Fin2] ≃(;sc) c -> isVoid_size tin[@Fin3] s3 -> isVoid_size tin[@Fin4] s4 -> tout[@Fin0] ≃(;sm+m') 0 /\ tout[@Fin1] ≃(;sn) n /\ tout[@Fin2] ≃(;sc-m'*n) m' * n + c /\ isVoid_size tout[@Fin3] (Mult_Loop_space34 m' n c s3 s4)[@Fin0] /\ isVoid_size tout[@Fin4] (Mult_Loop_space34 m' n c s3 s4)[@Fin1] ).
Definition Mult_Main_Rel : pRel sigNat^+ unit 6 := ignoreParam ( fun tin tout => forall (m n : nat) (sm sn so s3 s4 s5 : nat), tin[@Fin0] ≃(;sm) m -> tin[@Fin1] ≃(;sn) n -> isVoid_size tin[@Fin2] so -> isVoid_size tin[@Fin3] s3 -> isVoid_size tin[@Fin4] s4 -> isVoid_size tin[@Fin5] s5 -> tout[@Fin0] ≃(;sm) m /\ tout[@Fin1] ≃(;sn) n /\ tout[@Fin2] ≃(;so-m*n) m * n /\ isVoid_size tout[@Fin3] ((Mult_Loop_space34 m n 0 s3 s4)[@Fin0]) /\ isVoid_size tout[@Fin4] ((Mult_Loop_space34 m n 0 s3 s4)[@Fin1]) /\ tout[@Fin5] ≃(;s5+m) 0 ).
Definition Mult_Rel : pRel sigNat^+ unit 6 := ignoreParam (fun tin tout => forall (m : nat) (n : nat) (sm sn so s3 s4 s5 : nat), tin[@Fin0] ≃(;sm) m -> tin[@Fin1] ≃(;sn) n -> isVoid_size tin[@Fin2] so -> isVoid_size tin[@Fin3] s3 -> isVoid_size tin[@Fin4] s4 -> isVoid_size tin[@Fin5] s5 -> tout[@Fin0] ≃(;sm) m /\ tout[@Fin1] ≃(;sn) n /\ tout[@Fin2] ≃(;so-m*n) m * n /\ isVoid_size tout[@Fin3] ((Mult_Loop_space34 m n 0 s3 s4)[@Fin0]) /\ isVoid_size tout[@Fin4] ((Mult_Loop_space34 m n 0 s3 s4)[@Fin1]) /\ isVoid_size tout[@Fin5] (S (S (m + s5))) ).
Definition Mult_Step_steps m' n c := match m' with | O => 6 | _ => 168 + 33 * c + 39 * n end.
Fixpoint Mult_Loop_steps m' n c := match m' with | O => S (Mult_Step_steps m' n c) | S m'' => S (Mult_Step_steps m' n c) + Mult_Loop_steps m'' n (n + c) end.
Definition Mult_Main_steps m n := 44 + 12 * m + Mult_Loop_steps m n 0.
Definition Mult_Main_T : tRel sigNat^+ 6 := fun tin k => exists m n, tin[@Fin0] ≃ m /\ tin[@Fin1] ≃ n /\ isVoid tin[@Fin2] /\ (forall i : Fin.t 3, isVoid tin[@FinR 3 i]) /\ Mult_Main_steps m n <= k.
Definition Mult_steps m n := 13 + Mult_Main_steps m n.
Definition Mult_T : tRel sigNat^+ 6 := fun tin k => exists m n, tin[@Fin0] ≃ m /\ tin[@Fin1] ≃ n /\ isVoid tin[@Fin2] /\ (forall i : Fin.t 3, isVoid tin[@FinR 3 i]) /\ Mult_steps m n <= k.

Lemma Add_Loop_Terminates : projT1 Add_Loop ↓ (fun tin i => exists (a b:nat), tin[@Fin0] ≃ a /\ tin[@Fin1] ≃ b /\ Add_Loop_steps b <= i).
Proof.
eapply TerminatesIn_monotone.
{
unfold Add_Loop.
TM_Correct.
-
eapply RealiseIn_Realise.
apply Add_Step_Sem.
-
eapply RealiseIn_TerminatesIn.
apply Add_Step_Sem.
}
{
unfold Add_Loop_steps.
apply WhileCoInduction.
intros tin i (a&b&HEncA&HEncB&Hi).
destruct b.
-
exists 9.
repeat split.
+
lia.
+
intros o tmid H.
cbn in H.
modpon H;[].
destruct o; auto.
-
exists 9.
repeat split.
+
lia.
+
intros o tmid H.
cbn in H.
modpon H.
cbn -[plus mult] in *.
destruct o as [ () | ]; auto.
destruct H.
exists (9 + b * 10).
repeat split.
*
do 2 eexists.
repeat split; eauto.
lia.
*
lia.
Admitted.

Lemma Add_Main_Terminates : projT1 Add_Main ↓ Add_Main_T.
Proof.
unfold Add_Main, Add_Main_steps.
eapply TerminatesIn_monotone.
{
TM_Correct.
-
apply Add_Loop_Terminates.
}
{
intros tin k (m&n&HEncM&HEncN&HOut&HRight3&Hk).
unfold Add_Main_steps in *.
exists (37 + 12 * n), (47 + 22 * m).
repeat split; cbn.
-
cbn.
exists n.
split; eauto.
unfold CopyValue_steps.
rewrite Encode_nat_hasSize.
lia.
-
lia.
-
intros tmid ymid.
intros (H1&H2).
TMSimp.
modpon H1.
exists (37 + 12 * m), (Add_Loop_steps m).
repeat split.
+
exists m.
split.
eauto.
unfold CopyValue_steps.
rewrite Encode_nat_hasSize.
lia.
+
unfold Add_Loop_steps.
lia.
+
intros tmid2_ () (HComp & HInj).
TMSimp.
modpon HComp.
do 2 eexists; repeat split; eauto; do 2 eexists; eassumption.
Admitted.

Lemma Add_Terminates : projT1 Add ↓ Add_T.
Proof.
unfold Add, Add_steps.
eapply TerminatesIn_monotone.
{
TM_Correct.
-
apply Add_Main_Realise.
-
apply Add_Main_Terminates.
}
{
intros tin k (m&n&HEncM&HEncN&HOut&HInt&Hk).
exists (Add_Main_steps m n), 12.
repeat split.
-
cbn.
exists m, n.
repeat split; eauto.
-
unfold Add_Main_steps.
unfold Add_steps in *.
lia.
-
intros tmid () HComp.
cbn in *.
modpon HComp.
exists 0.
split.
eauto.
unfold MoveRight_steps.
cbn.
auto.
Admitted.

Lemma Mult_Step_Realise : Mult_Step ⊨ Mult_Step_Rel.
Proof.
eapply Realise_monotone.
{
unfold Mult_Step.
TM_Correct.
-
apply Add_Computes.
}
{
intros tin (yout, tout) H.
intros c m' n sm sn sc s3 s4 HEncM' HEncN HEncC HInt3 HInt4.
TMSimp.
destruct H; TMSimp.
-
rename H into HCaseNat, H1 into HAdd, H3 into HMove.
modpon HCaseNat.
destruct m' as [ | m']; auto.
modpon HAdd.
modpon HMove.
repeat split; auto.
+
contains_ext.
unfold MoveValue_size_y.
rewrite !Encode_nat_hasSize.
lia.
+
isVoid_mono.
unfold Add_space2.
unfold MoveValue_size_x.
rewrite Encode_nat_hasSize.
lia.
-
modpon H.
destruct m' as [ | m']; auto.
Admitted.

Lemma Mult_Loop_Realise : Mult_Loop ⊨ Mult_Loop_Rel.
Proof.
eapply Realise_monotone.
{
unfold Mult_Loop.
TM_Correct.
eapply Mult_Step_Realise.
}
{
eapply WhileInduction; intros; intros c m' n sm sn sc s3 s4 HEncM' HEncN HEncC HInt3 HInt4; TMSimp.
-
modpon HLastStep.
destruct m' as [ | m']; auto.
modpon HLastStep.
auto.
-
modpon HStar.
destruct m' as [ | m']; auto.
destruct HStar as (HStar1&HStar2&HStar3&HStar4&HStar5).
modpon HLastStep.
rewrite Nat.add_assoc in *.
replace (n + m' * n + c) with (m' * n + n + c) by lia.
repeat split; auto.
contains_ext.
f_equal.
now rewrite Nat.mul_succ_l.
Admitted.

Lemma Mult_Main_Realise : Mult_Main ⊨ Mult_Main_Rel.
Proof.
eapply Realise_monotone.
{
unfold Mult_Main.
TM_Correct.
-
apply Mult_Loop_Realise.
}
{
intros tin ((), tout) H.
intros m n sm sn s0 s3 s4 s5 HEncM HEncN Hout HInt3 HInt4 HInt5.
TMSimp.
modpon H.
modpon H0.
modpon H2.
rewrite Nat.add_0_r in H4.
repeat split; eauto.
{
contains_ext.
unfold CopyValue_size, Constr_O_size.
cbn.
lia.
}
{
contains_ext.
unfold CopyValue_size, Constr_O_size.
cbn.
lia.
}
Admitted.

Lemma Mult_Computes : Mult ⊨ Mult_Rel.
Proof.
eapply Realise_monotone.
{
unfold Mult.
TM_Correct.
-
eapply Mult_Main_Realise.
}
{
intros tin ((), tout) H.
cbn.
intros m n sm sn so s3 s4 s5 HEncM HEncN HOut HInt3 HInt4 HInt5.
TMSimp.
rename H into HMain, H0 into HReset.
modpon HMain.
modpon HReset.
repeat split; auto.
{
isVoid_mono.
unfold Reset_size.
rewrite !Encode_nat_hasSize.
cbn.
lia.
}
Admitted.

Lemma Mult_Step_Terminates : projT1 Mult_Step ↓ (fun tin k => exists m' n c, tin[@Fin0] ≃ m' /\ tin[@Fin1] ≃ n /\ tin[@Fin2] ≃ c /\ isVoid tin[@Fin3] /\ isVoid tin[@Fin4] /\ Mult_Step_steps m' n c <= k).
Proof.
eapply TerminatesIn_monotone.
{
unfold Mult_Step.
TM_Correct.
-
apply Add_Computes.
-
apply Add_Terminates.
}
{
intros tin k.
intros (m'&n&c&HEncM'&HEncN&HEncC&HInt3&HInt4&Hk).
destruct m' as [ | m']; cbn.
-
exists 5, 0.
cbn in *; repeat split; eauto.
intros tmid y (HComp&HInj).
TMSimp.
modpon HComp.
destruct y; auto.
-
exists 5, (162 + 33 * c + 39 * n); cbn in *; repeat split; eauto.
intros tmid y (HComp&HInj).
TMSimp.
modpon HComp.
cbn in *.
destruct y; auto.
exists (Add_steps n c), (63 + 21 * c + 17 * n); cbn in *; repeat split.
do 2 eexists.
repeat split; eauto.
unfold Add_steps.
lia.
intros tmid0_ () (HComp2&HInj).
TMSimp.
modpon HComp2.
do 2 eexists.
repeat split; eauto.
unfold MoveValue_steps.
rewrite !Encode_nat_hasSize.
lia.
Admitted.

Lemma Mult_Loop_Terminates : projT1 Mult_Loop ↓ (fun tin i => exists m' n c, tin[@Fin0] ≃ m' /\ tin[@Fin1] ≃ n /\ tin[@Fin2] ≃ c /\ isVoid tin[@Fin3] /\ isVoid tin[@Fin4] /\ Mult_Loop_steps m' n c <= i).
Proof.
eapply TerminatesIn_monotone.
{
unfold Mult_Loop.
TM_Correct.
-
apply Mult_Step_Realise.
-
apply Mult_Step_Terminates.
}
{
apply WhileCoInduction.
intros tin k (m'&n&c&HEncM'&HEncN&HEncC&HRight3&HRight4&Hk).
destruct m' as [ | m''] eqn:E; cbn in *; exists (Mult_Step_steps m' n c).
{
repeat split.
-
do 3 eexists.
repeat split; eauto.
cbn.
unfold Mult_Step_steps.
destruct m'; lia.
-
intros o tmid H1.
modpon H1.
destruct o as [ () | ]; auto.
destruct H1 as (HComp1&HComp2&HComp3&HComp4&HComp5).
subst.
cbn.
lia.
}
{
repeat split.
-
do 3 eexists.
repeat split; eauto.
cbn.
unfold Mult_Step_steps.
destruct m'; lia.
-
intros o tmid H1.
modpon H1.
destruct o as [ () | ]; auto.
destruct H1 as (HComp1&HComp2&HComp3&HComp4&HComp5).
cbn.
eexists.
repeat split.
+
do 3 eexists.
repeat split; eauto.
+
cbn.
rewrite <- Hk.
subst.
clear_all.
unfold Mult_Step_steps.
lia.
}
Admitted.

Lemma Mult_Main_Terminates : projT1 Mult_Main ↓ Mult_Main_T.
Proof.
eapply TerminatesIn_monotone.
{
unfold Mult_Main.
TM_Correct.
-
apply Mult_Loop_Terminates.
}
{
intros tin k (m&n&HEncM&HEncN&HOut&HInt&Hk).
cbn in *.
unfold Mult_Main_steps in Hk.
specializeFin HInt; clear HInt.
exists (37 + 12 * m), (6 + Mult_Loop_steps m n 0).
repeat split; try lia.
{
eexists.
repeat split; eauto.
unfold CopyValue_steps.
rewrite Encode_nat_hasSize; cbn.
lia.
}
intros tmid () (H1&H2); TMSimp.
modpon H1.
exists 5, (Mult_Loop_steps m n 0).
repeat split; try lia.
{
unfold Constr_O_steps.
lia.
}
intros tmid2 () (H2&HInj2); TMSimp.
modpon H2.
do 3 eexists.
repeat split; eauto.
Admitted.

Lemma Mult_Terminates : projT1 Mult ↓ Mult_T.
Proof.
eapply TerminatesIn_monotone.
{
unfold Mult.
TM_Correct.
-
apply Mult_Main_Realise.
-
apply Mult_Main_Terminates.
}
{
intros tin k (m&n&HEncM&HEncN&HOut&HInt&Hk).
cbn in *.
unfold Mult_steps in Hk.
exists (Mult_Main_steps m n), 12.
repeat split; try lia.
do 2 eexists; repeat split; eauto.
intros tmid () H1; TMSimp.
specialize (HInt Fin0) as HInt0.
specialize (HInt Fin1) as HInt4.
specialize (HInt Fin2) as HInt5.
modpon H1.
exists 0.
split; auto.
}
