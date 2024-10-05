From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import Hoare.Hoare.
From Undecidability Require Import CaseNat.
Require Import ArithRing.
Arguments mult : simpl never.
Arguments plus : simpl never.
Definition Add_Step : pTM sigNat^+ (option unit) 2 := If (CaseNat @ [|Fin1|]) (Return (Constr_S @ [|Fin0|]) None) (Return Nop (Some tt)).
Definition Add_Step_steps : nat := 9.
Definition Add_Step_size (a b : nat) : Vector.t (nat->nat) 2 := match b with | 0 => [|id; id|] | S b' => [|S; S|] end.
Definition Add_Loop : pTM sigNat^+ unit 2 := While Add_Step.
Definition Add_Loop_steps b := 9 + 10 * b.
Fixpoint Add_Loop_size (a b : nat) : Vector.t (nat->nat) 2 := match b with | O => Add_Step_size a b | S b' => Add_Step_size a b >>> Add_Loop_size (S a) b' end.
Definition Add : pTM sigNat^+ unit 4 := LiftTapes (CopyValue _) [|Fin1; Fin2|];; (* copy n to a *) LiftTapes (CopyValue _) [|Fin0; Fin3|];; (* copy m to b *) LiftTapes Add_Loop [|Fin2; Fin3|];; (* Main loop *) LiftTapes (Reset _) [|Fin3|].
Definition Add_steps m n := 98 + 12 * n + 22 * m.
Definition Add_space (a b : nat) : Vector.t (nat->nat) 4 := [|(*0*) id; (*1*) id; (*2*) CopyValue_size b >> Add_Loop_size b a @>Fin0; (*3*) CopyValue_size a >> (Add_Loop_size b a @>Fin1) >> Reset_size 0 |].
Definition Mult_Step : pTM sigNat^+ (option unit) 5 := If (LiftTapes CaseNat [|Fin0|]) (Return ( LiftTapes Add [|Fin1; Fin2; Fin3; Fin4|];; (* Add(n, c, c') *) LiftTapes (MoveValue _) [|Fin3; Fin2|] ) (None)) (* continue *) (Return Nop (Some tt)).
Definition Mult_Step_steps m' n c := match m' with | O => 6 | _ => 168 + 33 * c + 39 * n end.
Definition Mult_Step_space m' n c : Vector.t (nat->nat) 5 := match m' with | 0 => [|id; id; id; id; id|] | S m'' => [| (*0*) S; (*1*) Add_space n c @> Fin0; (* = [id] *) (*2*) (Add_space n c @> Fin1) >> MoveValue_size_y (n+c) c; (*3*) (Add_space n c @> Fin2) >> MoveValue_size_x (n+c); (*4*) (Add_space n c @>Fin3) |] end.
Definition Mult_Loop := While Mult_Step.
Fixpoint Mult_Loop_steps m' n c := match m' with | O => S (Mult_Step_steps m' n c) | S m'' => S (Mult_Step_steps m' n c) + Mult_Loop_steps m'' n (n + c) end.
Fixpoint Mult_Loop_size m' n c := match m' with | 0 => Mult_Step_space m' n c (* [id;...;id] *) | S m'' => Mult_Step_space m' n c >>> Mult_Loop_size m'' n (n+c) end.
Definition Mult : pTM sigNat^+ unit 6 := LiftTapes (CopyValue _) [|Fin0; Fin5|];; (* m' := m *) LiftTapes (Constr_O) [|Fin2|];; (* c := 0 *) LiftTapes Mult_Loop [|Fin5; Fin1; Fin2; Fin3; Fin4|];; (* Main loop *) LiftTapes (Reset _) [|Fin5|].
Definition Mult_steps (m n : nat) : nat := 12 * m + Mult_Loop_steps m n 0 + 57.
Definition Mult_size (m n : nat) : Vector.t (nat->nat) 6 := [|(*0*) id; (*1*) Mult_Loop_size m n 0 @> Fin1; (*2*) Constr_O_size >> Mult_Loop_size m n 0 @> Fin2; (*3*) Mult_Loop_size m n 0 @> Fin3; (*4*) Mult_Loop_size m n 0 @> Fin4; (*5*) CopyValue_size m >> Mult_Loop_size m n 0 @> Fin0 >> Reset_size 0 |].

Lemma Add_Loop_SpecT_size (a b : nat) (ss : Vector.t nat 2) : TripleT (≃≃([], withSpace ( [|Contains _ a; Contains _ b|]) ss)) (Add_Loop_steps b) (Add_Loop) (fun _ => tspec ([], withSpace [|Contains _ (a+b); Contains _ 0|] (appSize (Add_Loop_size a b) ss))).
Proof.
eapply While_SpecTReg with (PRE := fun '(a,b,ss) => (_,_)) (INV := fun '(a,b,ss) y => (_,_)) (POST := fun '(a,b,ss) y => (_,_)) (f__loop := fun '(a,b,ss) => _) (f__step := fun '(a,b,ss) => _) (x := (a,b,ss)); clear a b ss; intros ((x,y),ss).
-
apply Add_Step_SpecT_space.
-
cbn.
split.
+
intros [].
split.
2:unfold Add_Step_steps, Add_Loop_steps;lia.
destruct y as [ | y']; cbn in *.
2:easy.
tspec_ext.
f_equal.
nia.
+
destruct y as [ | y']; cbn in *.
easy.
intros _.
eexists (S x, y', _); cbn.
repeat split.
*
tspec_ext.
*
unfold Add_Step_steps, Add_Loop_steps.
lia.
*
tspec_ext.
f_equal.
nia.
