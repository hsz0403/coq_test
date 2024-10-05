From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import Hoare.HoareLogic Hoare.HoareCombinators Hoare.HoareRegister Hoare.HoareTactics Hoare.HoareTacticsView.
From Undecidability Require Import CaseNat.
From Coq Require Import ArithRing.
Arguments mult : simpl never.
Arguments plus : simpl never.
Set Warnings "-undo-batch-mode,-non-interactive".
Set Default Proof Using "Type".
From Undecidability Require Import TM.Code.Copy.
Definition CopyValue_sizefun {sigX X : Type} {cX : codable sigX X} (x : X) : Vector.t (nat->nat) 2 := [|id; CopyValue_size x|].
Definition MoveValue_size {X Y sigX sigY : Type} {cX : codable sigX X} {cY : codable sigY Y} (x : X) (y : Y) : Vector.t (nat->nat) 2 := [|MoveValue_size_x x; MoveValue_size_y x y|].
Definition CaseNat_size (n : nat) : Vector.t (nat->nat) 1 := match n with | O => [|id|] | S n' => [|S|] end.
Ltac hstep_Nat := lazymatch goal with | [ |- TripleT ?P ?k Constr_O ?Q ] => eapply Constr_O_SpecT_size (* We only use register-machines. There is no need to have lemmas without register specifications. This was only done here for demonstration purposes. *) | [ |- TripleT ?P ?k Constr_S ?Q ] => eapply Constr_S_SpecT_size | [ |- TripleT ?P ?k CaseNat ?Q ] => eapply CaseNat_SpecT_size end.
Smpl Add hstep_Nat : hstep_Spec.
Definition IncrementTwice_steps := 1 + Constr_S_steps + Constr_S_steps.
Definition IncrementTwice : pTM sigNat^+ unit 1 := Constr_S;; Constr_S.
Definition Incr2 : pTM sigNat^+ unit 2 := Constr_S@[|Fin0|];; Constr_S@[|Fin1|].
Definition Incr2_steps := 1 + Constr_S_steps + Constr_S_steps.
Definition Incr3 : pTM sigNat^+ unit 3 := Constr_S@[|Fin0|];; Constr_S@[|Fin1|];; IncrementTwice@[|Fin2|].
Definition Incr3_steps := 2 + Constr_S_steps + Constr_S_steps + IncrementTwice_steps.
Definition Add_Step : pTM sigNat^+ (option unit) 2 := If (CaseNat @ [|Fin1|]) (Return (Constr_S @ [|Fin0|]) None) (Return Nop (Some tt)).
Definition Add_Step_Post : nat*nat -> option unit -> Assert sigNat^+ 2 := fun '(a,b) => (fun yout => ≃≃(([yout = if b then Some tt else None] ,[|Contains _ (match b with 0 => a | _ => S a end);Contains _ (pred b)|]))).
Definition Add_Loop : pTM sigNat^+ unit 2 := While Add_Step.
Definition Add_Step_steps : nat := 9.
Definition Add_Step_size (a b : nat) : Vector.t (nat->nat) 2 := match b with | 0 => [|id; id|] | S b' => [|S; S|] end.
Definition Add_Loop_steps b := 9 + 10 * b.
Fixpoint Add_Loop_size (a b : nat) : Vector.t (nat->nat) 2 := match b with | O => Add_Step_size a b | S b' => Add_Step_size a b >>> Add_Loop_size (S a) b' end.
Definition Add : pTM sigNat^+ unit 4 := LiftTapes (CopyValue _) [|Fin1; Fin2|];; (* copy n to a *) LiftTapes (CopyValue _) [|Fin0; Fin3|];; (* copy m to b *) LiftTapes Add_Loop [|Fin2; Fin3|];; (* Main loop *) LiftTapes (Reset _) [|Fin3|].
Definition Add_steps m n := 98 + 12 * n + 22 * m.
Definition Add_space (a b : nat) : Vector.t (nat->nat) 4 := [|(*0*) id; (*1*) id; (*2*) CopyValue_size b >> Add_Loop_size b a @>Fin0; (*3*) CopyValue_size a >> (Add_Loop_size b a @>Fin1) >> Reset_size 0 |].
Definition Mult_Step : pTM sigNat^+ (option unit) 5 := If (LiftTapes CaseNat [|Fin0|]) (Return ( LiftTapes Add [|Fin1; Fin2; Fin3; Fin4|];; (* Add(n, c, c') *) LiftTapes (MoveValue _) [|Fin3; Fin2|] ) (None)) (* continue *) (Return Nop (Some tt)).
Definition Mult_Step_Post : nat*nat*nat -> option unit -> Assert sigNat^+ 5 := fun '(m',n,c) => (fun yout => ≃≃([yout = if m' then Some tt else None], [|Contains _ (pred m'); Contains _ n; Contains _ ( if m' then c else (n + c)); Void; Void|])).
Definition Mult_Step_steps m' n c := match m' with | O => 6 | _ => 168 + 33 * c + 39 * n end.
Definition Mult_Step_space m' n c : Vector.t (nat->nat) 5 := match m' with | 0 => [|id; id; id; id; id|] | S m'' => [| (*0*) S; (*1*) Add_space n c @> Fin0; (* = [id] *) (*2*) (Add_space n c @> Fin1) >> MoveValue_size_y (n+c) c; (*3*) (Add_space n c @> Fin2) >> MoveValue_size_x (n+c); (*4*) (Add_space n c @>Fin3) |] end.
Definition Mult_Loop := While Mult_Step.
Fixpoint Mult_Loop_steps m' n c := match m' with | O => S (Mult_Step_steps m' n c) | S m'' => S (Mult_Step_steps m' n c) + Mult_Loop_steps m'' n (n + c) end.
Fixpoint Mult_Loop_size m' n c := match m' with | 0 => Mult_Step_space m' n c (* [id;...;id] *) | S m'' => Mult_Step_space m' n c >>> Mult_Loop_size m'' n (n+c) end.
Definition Mult : pTM sigNat^+ unit 6 := LiftTapes (CopyValue _) [|Fin0; Fin5|];; (* m' := m *) LiftTapes (Constr_O) [|Fin2|];; (* c := 0 *) LiftTapes Mult_Loop [|Fin5; Fin1; Fin2; Fin3; Fin4|];; (* Main loop *) LiftTapes (Reset _) [|Fin5|].
Definition Mult_steps (m n : nat) : nat := 12 * m + Mult_Loop_steps m n 0 + 57.
Definition Mult_size_bug (m n : nat) : Vector.t (nat->nat) 6 := [|(*0*) id; (*1*) Mult_Loop_size m n 0 @> Fin1; (*2*) Constr_O_size >> Mult_Loop_size m n 0 @> Fin2; (*3*) Mult_Loop_size m n 0 @> Fin3; (*4*) Mult_Loop_size m n 0 @> Fin4; (*5*) CopyValue_size m >> Mult_Loop_size m n 0 @> Fin4 (* Something wrong here! *) |].

Lemma Constr_S_SpecT_pure (y : nat) : TripleT (fun tin => tin[@Fin0] ≃ y) (Constr_S_steps) (Constr_S) (fun _ tout => tout[@Fin0] ≃ S y).
Proof.
eapply RealiseIn_TripleT.
-
apply Constr_S_Sem.
-
intros tin [] tout H1 H2.
cbn in *.
unfold tspec in *.
modpon H1.
contains_ext.
