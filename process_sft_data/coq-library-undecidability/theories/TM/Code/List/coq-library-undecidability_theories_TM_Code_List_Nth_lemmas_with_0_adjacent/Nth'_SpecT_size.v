From Undecidability Require Import ProgrammingTools Hoare.
From Undecidability Require Import CaseNat CaseList CaseSum.
Local Arguments skipn { A } !n !l.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Local Arguments Encode_list : simpl never.
Local Arguments Encode_nat : simpl never.
Set Default Proof Using "Type".
Section Nth'.
Variable (sig sigX : finType) (X : Type) (cX : codable sigX X).
Variable (retr1 : Retract (sigList sigX) sig) (retr2 : Retract sigNat sig).
Local Instance retr_X_list' : Retract sigX sig := ComposeRetract retr1 (Retract_sigList_X _).
Definition Nth'_Step_size {sigX X : Type} {cX : codable sigX X} (n : nat) (l : list X) : Vector.t (nat -> nat) 3 := match n, l with | S n', x :: l' => [| CaseList_size0 x; S; CaseList_size1 x >> Reset_size x|] | 0, x :: x' => [|fun s0 => CaseList_size0 x s0; id; fun s2 => CaseList_size1 x s2|] | 0, nil => [|id; id; id|] | S n', nil => [|id; fun s1 => S s1; id|] end.
Definition Nth'_Step : pTM sig^+ (option bool) 3 := If (LiftTapes (ChangeAlphabet CaseNat _) [|Fin1|]) (If (LiftTapes (ChangeAlphabet (CaseList sigX) _) [|Fin0; Fin2|]) (* n = S n' *) (Return (LiftTapes (Reset _) [|Fin2|]) None) (* l = x :: l'; continue *) (Return Nop (Some false))) (* l = nil; return false *) (Relabel (LiftTapes (ChangeAlphabet (CaseList sigX) _) [|Fin0; Fin2|]) Some) (* n = 0 *) .
Definition Nth'_Step_steps {sigX X : Type} {cX : codable sigX X} (l : list X) (n : nat) := match n, l with | S n', x :: l' => 2 + CaseNat_steps + CaseList_steps_cons x + Reset_steps x | S n', nil => 2 + CaseNat_steps + CaseList_steps_nil | O, x :: l' => 1 + CaseNat_steps + CaseList_steps_cons x | O, nil => 1 + CaseNat_steps + CaseList_steps_nil end.
Definition Nth'_Step_steps_CaseList (xs : list X) := match xs with | x :: xs' => 1 + CaseList_steps_cons x + Reset_steps x | nil => 1 + CaseList_steps_nil end.
Fixpoint Nth'_Loop_size {sigX X : Type} {cX : codable sigX X} (n : nat) (l : list X) {struct n} : Vector.t (nat -> nat) 3 := match n, l with | S n', x :: l' => Nth'_Step_size n l >>> Nth'_Loop_size n' l' | _, _ => Nth'_Step_size n l end.
Definition Nth'_Loop := While Nth'_Step.
Fixpoint Nth'_Loop_steps {sigX X : Type} {cX : codable sigX X} (l : list X) (n : nat) { struct l } := match n, l with | S n', x :: l' => S (Nth'_Step_steps l n) + Nth'_Loop_steps l' n' (* continue *) | S n', nil => Nth'_Step_steps l n (* return *) | O, x :: l' => Nth'_Step_steps l n (* return *) | O, nil => Nth'_Step_steps l n (* only [CaseNat] and [If] *) end.
Definition Nth' : pTM sig^+ bool 4 := LiftTapes (CopyValue _) [|Fin0; Fin3|];; (* Save l (on t0) to t3 *) If (LiftTapes (Nth'_Loop) [|Fin3; Fin1; Fin2|]) (* Execute the loop with the copy of l *) (Return (LiftTapes (Reset _) [|Fin3|];; (* Reset the copy of [l] *) LiftTapes (Reset _) [|Fin1|] (* Reset [n] *) ) true) (Return (LiftTapes (Reset _) [|Fin3|];; (* Reset the copy of [l] *) LiftTapes (Reset _) [|Fin1|] (* Reset [n] *) ) false) .
Definition Nth'_size {sigX X : Type} {cX : codable sigX X} (l : list X) (n : nat) := [| id; (Nth'_Loop_size n l)[@Fin1] >> Reset_size (n - (S (length l))); (Nth'_Loop_size n l)[@Fin2]; CopyValue_size l >> (Nth'_Loop_size n l)[@Fin0] >> Reset_size (skipn (S n) l) |].
Definition Nth'_steps {sigX X : Type} {cX : codable sigX X} (l : list X) (n : nat) := 3 + CopyValue_steps l + Nth'_Loop_steps l n + Reset_steps (skipn (S n) l) + Reset_steps (n - S (length l)).
Section Legacy.
Definition Nth'_Rel : pRel sig^+ bool 4 := fun tin '(yout, tout) => forall (l : list X) (n : nat) s0 s1 s2 s3, tin[@Fin0] ≃(;s0) l -> tin[@Fin1] ≃(;s1) n -> isVoid_size tin[@Fin2] s2 -> isVoid_size tin[@Fin3] s3 -> match yout with | true => exists (x : X), nth_error l n = Some x /\ tout[@Fin0] ≃(;(Nth'_size l n)[@Fin0]s0) l /\ isVoid_size tout[@Fin1] ((Nth'_size l n)[@Fin1]s1) /\ tout[@Fin2] ≃(;(Nth'_size l n)[@Fin2]s2) x /\ isVoid_size tout[@Fin3] ((Nth'_size l n)[@Fin3]s3) | false => nth_error l n = None /\ tout[@Fin0] ≃(;(Nth'_size l n)[@Fin0]s0) l /\ isVoid_size tout[@Fin1] ((Nth'_size l n)[@Fin1]s1) /\ isVoid_size tout[@Fin2] ((Nth'_size l n)[@Fin2]s2) /\ isVoid_size tout[@Fin3] ((Nth'_size l n)[@Fin3]s3) end.
Definition Nth'_T : tRel sig^+ 4 := fun tin k => exists (l : list X) (n : nat), tin[@Fin0] ≃ l /\ tin[@Fin1] ≃ n /\ isVoid tin[@Fin2] /\ isVoid tin[@Fin3] /\ Nth'_steps l n <= k.
End Legacy.
End Nth'.
Arguments Nth'_steps {sigX X cX} : simpl never.
Arguments Nth'_size {sigX X cX} : simpl never.

Lemma Nth'_SpecT_size (xs : list X) (n : nat) (ss : Vector.t nat 4) : TripleT (≃≃([],withSpace ([|Contains _ xs; Contains _ n; Void; Void|]) ss)) (Nth'_steps xs n) Nth' (fun yout => ≃≃([yout = match nth_error xs n with None => false | _ => true end], withSpace match nth_error xs n with | Some x => [|Contains _ xs; Void; Contains _ x;Void|] | None => [|Contains _ xs; Void; Void;Void|] end (appSize (Nth'_size xs n) ss))).
Proof.
unfold Nth'.
hstep; cbn.
hstep; cbn.
apply CopyValue_SpecT_size.
cbn.
intros _.
eapply If_SpecTReg; cbn.
-
hstep; cbn.
eapply ConsequenceT_pre.
apply Nth'_Loop_SpecT_size.
tspec_ext.
reflexivity.
-
cbn.
destruct (nth_error xs n) as [ x | ].
all:hintros [=].
hstep; cbn.
hstep; cbn.
hstep; cbn.
apply Reset_SpecT_space with (X := list X).
cbn.
intros [].
eauto.
hstep; cbn.
apply Reset_SpecT_space with (X := nat).
reflexivity.
cbn.
intros _.
cbn.
tspec_ext.
-
cbn.
destruct (nth_error xs n) as [ x | ].
all:hintros [=].
hstep; cbn.
hstep; cbn.
hstep; cbn.
apply Reset_SpecT_space with (X := list X).
cbn.
intros [].
eauto.
hstep; cbn.
apply Reset_SpecT_space with (X := nat).
reflexivity.
cbn.
intros _.
tspec_ext.
-
cbn.
destruct b;reflexivity.
-
unfold Nth'_steps.
lia.
