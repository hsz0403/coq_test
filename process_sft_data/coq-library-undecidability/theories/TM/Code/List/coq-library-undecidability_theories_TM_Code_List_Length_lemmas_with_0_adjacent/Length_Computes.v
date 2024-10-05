From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import CaseNat CaseList CaseSum.
Local Arguments skipn { A } !n !l.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Local Arguments Encode_list : simpl never.
Local Arguments Encode_nat : simpl never.
Set Default Proof Using "Type".
Section Lenght.
Variable sig sigX : finType.
Variable (X : Type) (cX : codable sigX X).
Variable (retr1 : Retract (sigList sigX) sig) (retr2 : Retract sigNat sig).
Local Instance retr_X_list' : Retract sigX sig := ComposeRetract retr1 (Retract_sigList_X _).
Definition Length_Step : pTM sig^+ (option unit) 3 := If (LiftTapes (ChangeAlphabet (CaseList _) _) [|Fin0; Fin2|]) (Return (LiftTapes (Reset _) [|Fin2|];; LiftTapes (ChangeAlphabet (Constr_S) _) [|Fin1|]) (None)) (* continue *) (Return Nop (Some tt)) (* break *) .
Definition Length_Step_size {sigX X : Type} {cX : codable sigX X} (x : X) : Vector.t (nat -> nat) 3 := [| CaseList_size0 x; pred; CaseList_size1 x >> Reset_size x|].
Definition Length_Step_Rel : pRel sig^+ (option unit) 3 := fun tin '(yout, tout) => forall (xs : list X) (n : nat) (s0 s1 s2 : nat), tin[@Fin0] ≃(;s0) xs -> tin[@Fin1] ≃(;s1) n -> isVoid_size tin[@Fin2] s2 -> match yout, xs with | (Some tt), nil => (* break *) tout[@Fin0] ≃(;s0) xs /\ tout[@Fin1] ≃(;s1) n /\ isVoid_size tout[@Fin2] s2 | None, x :: xs' => (* continue *) tout[@Fin0] ≃(; (Length_Step_size x)[@Fin0]s0) xs' /\ tout[@Fin1] ≃(; (Length_Step_size x)[@Fin1]s1) S n /\ isVoid_size tout[@Fin2] ((Length_Step_size x)[@Fin2]s2) | _, _ => False end.
Definition Length_Step_steps {sigX X : Type} {cX : codable sigX X} (xs : list X) := match xs with | nil => 1 + CaseList_steps_nil | x :: xs' => 2 + CaseList_steps_cons x + Reset_steps x + Constr_S_steps end.
Definition Length_Step_T : tRel sig^+ 3 := fun tin k => exists (xs : list X) (n : nat), tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ n /\ isVoid tin[@Fin2] /\ Length_Step_steps xs <= k.
Definition Length_Loop := While Length_Step.
Fixpoint Length_Loop_size {sigX X : Type} {cX : codable sigX X} (xs : list X) : Vector.t (nat->nat) 3 := match xs with | nil => [|id;id;id|] | x :: xs' => Length_Step_size x >>> Length_Loop_size xs' end.
Definition Length_Loop_Rel : pRel sig^+ unit 3 := ignoreParam ( fun tin tout => forall (xs : list X) (n : nat) (s0 s1 s2:nat), tin[@Fin0] ≃(;s0) xs -> tin[@Fin1] ≃(;s1) n -> isVoid_size tin[@Fin2] s2 -> tout[@Fin0] ≃(; (Length_Loop_size xs)[@Fin0]s0) @nil X /\ tout[@Fin1] ≃(; (Length_Loop_size xs)[@Fin1]s1) n + length xs /\ isVoid_size tout[@Fin2] ((Length_Loop_size xs)[@Fin2]s2) ).
Fixpoint Length_Loop_steps {sigX X : Type} {cX : codable sigX X} (xs : list X) : nat := match xs with | nil => Length_Step_steps xs | x :: xs' => S (Length_Step_steps xs) + Length_Loop_steps xs' end.
Definition Length_Loop_T : tRel sig^+ 3 := fun tin k => exists (xs : list X) (n : nat), tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ n /\ isVoid tin[@Fin2] /\ Length_Loop_steps xs <= k.
Definition Length : pTM sig^+ unit 4 := LiftTapes (CopyValue _) [|Fin0; Fin3|];; LiftTapes (ChangeAlphabet Constr_O _) [|Fin1|];; LiftTapes (Length_Loop) [|Fin3; Fin1; Fin2|];; LiftTapes (ResetEmpty1 _) [|Fin3|].
Definition Length_size {sigX X : Type} {cX : codable sigX X} (xs : list X) : Vector.t (nat->nat) 4 := [|id; (* 0 *) Constr_O_size >> (Length_Loop_size xs)[@Fin1]; (* 1 *) (Length_Loop_size xs)[@Fin2]; (* 2 *) CopyValue_size xs >> (Length_Loop_size xs)[@Fin0] >> Reset_size (@nil X) (* 3 *) |].
Definition Length_Rel : pRel sig^+ unit 4 := ignoreParam ( fun tin tout => forall (xs : list X) (s0 s1 s2 s3 : nat), tin[@Fin0] ≃(;s0) xs -> isVoid_size tin[@Fin1] s1 -> isVoid_size tin[@Fin2] s2 -> isVoid_size tin[@Fin3] s3 -> tout[@Fin0] ≃(; (Length_size xs)[@Fin0]s0) xs /\ tout[@Fin1] ≃(; (Length_size xs)[@Fin1]s1) length xs /\ isVoid_size tout[@Fin2] ((Length_size xs)[@Fin2]s2) /\ isVoid_size tout[@Fin3] ((Length_size xs)[@Fin3]s3) ).
Definition Length_steps {sigX X : Type} {cX : codable sigX X} (xs : list X) := 36 + 12 * size xs + Length_Loop_steps xs.
Definition Length_T : tRel sig^+ 4 := fun tin k => exists (xs : list X), tin[@Fin0] ≃ xs /\ isVoid tin[@Fin1] /\ isVoid tin[@Fin2] /\ isVoid tin[@Fin3] /\ Length_steps xs <= k.
End Lenght.
Arguments Length_steps {sigX X cX} : simpl never.
Arguments Length_size {sigX X cX} : simpl never.
From Undecidability.L.Complexity Require Import UpToC.
Section Length_steps_nice.
Variable (sigX X : Type) (cX : codable sigX X).
End Length_steps_nice.

Lemma Length_Computes : Length ⊨ Length_Rel.
Proof.
eapply Realise_monotone.
{
unfold Length.
TM_Correct.
-
apply Length_Loop_Realise.
-
eapply RealiseIn_Realise.
apply ResetEmpty1_Sem with (X := list X).
}
{
intros tin ((), tout) H.
intros xs s0 s1 s2 s3 HEncXs Hout HInt2 HInt3.
TMSimp.
modpon H.
modpon H0.
modpon H2.
modpon H4.
repeat split; auto.
}
