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
