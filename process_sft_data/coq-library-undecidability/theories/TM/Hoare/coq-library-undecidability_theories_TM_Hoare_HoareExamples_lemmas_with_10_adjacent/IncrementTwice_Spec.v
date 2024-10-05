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

Lemma Constr_O_Spec : Triple (≃≃([], [|Void|])) Constr_O (fun _ => ≃≃([], [|Contains _ 0|])).
Proof.
eapply TripleT_Triple.
Admitted.

Lemma Constr_S_SpecT_size : forall (y : nat) ss, TripleT (≃≃([], withSpace ( [|Contains _ y|]) ss)) Constr_S_steps Constr_S (fun _ => ≃≃([], withSpace ( [|Contains _ (S y)|]) (appSize [|S|] ss))).
Proof.
intros y ss.
start_TM.
eapply RealiseIn_TripleT.
-
apply Constr_S_Sem.
-
intros tin [] tout H HEnc.
unfold withSpace in *|-.
cbn in *.
specialize (HEnc Fin0).
simpl_vector in *; cbn in *.
modpon H.
hnf.
Admitted.

Lemma Constr_S_SpecT : forall (y : nat), TripleT (≃≃([], [|Contains _ y|])) Constr_S_steps Constr_S (fun _ => ≃≃([], [|Contains _ (S y)|])).
Proof.
intros.
Admitted.

Lemma Constr_S_Spec : forall (y : nat), Triple (≃≃([], [|Contains _ y|])) Constr_S (fun _ => ≃≃([], [|Contains _ (S y)|])).
Proof.
intros y.
eapply TripleT_Triple.
Admitted.

Lemma CaseNat_SpecT_size (y : nat) (ss : Vector.t nat 1) : TripleT (≃≃([], withSpace ( [|Contains _ y|]) ss)) CaseNat_steps CaseNat (fun yout => tspec ([if yout then y <> 0 else y = 0], (withSpace [|Contains _ (pred y)|] (appSize (CaseNat_size y) ss)))).
Proof.
start_TM.
eapply RealiseIn_TripleT.
-
apply CaseNat_Sem.
-
intros tin yout tout H HEnc.
unfold withSpace in *|-.
specialize (HEnc Fin0).
simpl_vector in *; cbn in *.
modpon H.
destruct yout, y; cbn in *; auto.
+
hnf.
split.
easy.
intros i; destruct_fin i; cbn; eauto.
+
hnf.
split.
easy.
Admitted.

Lemma CaseNat_SpecT (y : nat) : TripleT (≃≃([], [|Contains _ y|])) CaseNat_steps CaseNat (fun yout => tspec ([if yout then y <> 0 else y = 0],[|Contains _ (pred y)|])).
Proof.
eapply TripleT_RemoveSpace.
Admitted.

Lemma CaseNat_Spec (y : nat) : Triple (≃≃([], [|Contains _ y|])) CaseNat (fun yout => tspec ([if yout then y <> 0 else y = 0],[|Contains _ (pred y)|])).
Proof.
eapply TripleT_Triple.
Admitted.

Lemma Constr_S_Spec_con (n : nat) (Q : Assert sigNat^+ 1) : (forall tout, ≃≃([], [|Contains _ (S n)|]) tout -> Q tout) -> Triple (≃≃([], [|Contains _ n|])) Constr_S (fun _ => Q).
Proof.
Admitted.

Lemma IncrementTwice_Spec_pure (y : nat) : Triple (fun tin => tin[@Fin0] ≃ y) (IncrementTwice) (fun _ tout => tout[@Fin0] ≃ S (S y)).
Proof.
start_TM.
eapply Seq_Spec.
-
apply Constr_S_Spec_pure.
-
cbn.
intros _.
apply Constr_S_Spec_pure.
Restart.
start_TM.
unfold IncrementTwice.
hsteps.
apply Constr_S_Spec_pure.
cbn.
intros _.
Admitted.

Lemma IncrementTwice_SpecT_pure (y : nat) : TripleT (fun tin => tin[@Fin0] ≃ y) (IncrementTwice_steps) (IncrementTwice) (fun _ tout => tout[@Fin0] ≃ S (S y)).
Proof.
start_TM.
eapply Seq_SpecT.
-
apply Constr_S_SpecT_pure.
-
cbn.
intros _.
apply Constr_S_SpecT_pure.
-
reflexivity.
Restart.
start_TM.
unfold IncrementTwice.
hsteps.
apply Constr_S_SpecT_pure.
cbn.
intros _.
apply Constr_S_SpecT_pure.
Admitted.

Lemma IncrementTwice_SpecT (y : nat) : TripleT (≃≃([], [|Contains _ y|])) (IncrementTwice_steps) (IncrementTwice) (fun _ => ≃≃([], [|Contains _ (S (S y))|])).
Proof.
start_TM.
eapply Seq_SpecT.
-
apply Constr_S_SpecT.
-
cbn.
intros _.
apply Constr_S_SpecT.
-
reflexivity.
Restart.
start_TM.
unfold IncrementTwice.
hstep.
apply Constr_S_SpecT.
cbn.
intros _.
apply Constr_S_SpecT.
Restart.
unfold IncrementTwice.
hsteps_cbn.
eauto.
Admitted.

Lemma Incr2_Spec : forall (x y : nat), Triple (≃≃([], [|Contains _ x; Contains _ y|])) Incr2 (fun _ => ≃≃([], [|Contains _ (S x); Contains _ (S y)|])).
Proof.
intros x y.
start_TM.
eapply Seq_Spec.
-
eapply LiftTapes_Spec.
+
smpl_dupfree.
+
cbn.
apply Constr_S_Spec.
-
cbn.
intros _.
eapply LiftTapes_Spec_con.
+
smpl_dupfree.
+
cbn.
apply Constr_S_Spec.
+
cbn.
auto.
Restart.
intros x y.
unfold Incr2.
hsteps_cbn.
Admitted.

Lemma Incr2_SpecT : forall (x y : nat), TripleT (≃≃([], [|Contains _ x; Contains _ y|])) Incr2_steps Incr2 (fun _ => ≃≃([], [|Contains _ (S x); Contains _ (S y)|])).
Proof.
intros x y.
start_TM.
eapply Seq_SpecT.
-
eapply LiftTapes_SpecT.
+
smpl_dupfree.
+
cbn.
apply Constr_S_SpecT.
-
intros [].
cbn [Frame].
eapply LiftTapes_SpecT_con.
+
smpl_dupfree.
+
cbn.
apply Constr_S_SpecT.
+
cbn.
auto.
-
reflexivity.
Restart.
intros x y.
unfold Incr2.
hsteps_cbn.
Admitted.

Lemma Incr3_Spec : forall (x y z : nat), Triple (≃≃([], [|Contains _ x; Contains _ y; Contains _ z|])) Incr3 (fun _ => ≃≃([], [|Contains _ (S x); Contains _ (S y); Contains _ (S (S z))|])).
Proof.
intros x y z.
start_TM.
eapply Seq_Spec.
-
eapply LiftTapes_Spec.
+
smpl_dupfree.
+
cbn.
apply Constr_S_Spec.
-
intros [].
cbn [Frame].
eapply Seq_Spec.
+
eapply LiftTapes_Spec.
*
smpl_dupfree.
*
cbn.
apply Constr_S_Spec.
+
intros [].
cbn [Frame].
eapply LiftTapes_Spec_con.
*
smpl_dupfree.
*
cbn.
apply IncrementTwice_Spec.
*
cbn.
auto.
Restart.
intros x y z.
unfold Incr3.
hsteps_cbn.
apply IncrementTwice_Spec.
cbn.
Admitted.

Lemma Incr3_SpecT : forall (x y z : nat), TripleT (≃≃([], [|Contains _ x; Contains _ y; Contains _ z|])) (Incr3_steps) Incr3 (fun _ => ≃≃([], [|Contains _ (S x); Contains _ (S y); Contains _ (S (S z))|])).
Proof.
intros x y z.
start_TM.
eapply Seq_SpecT.
-
eapply LiftTapes_SpecT.
+
smpl_dupfree.
+
cbn.
apply Constr_S_SpecT.
-
intros [].
cbn [Frame].
eapply Seq_SpecT.
+
eapply LiftTapes_SpecT.
*
smpl_dupfree.
*
cbn.
apply Constr_S_SpecT.
+
intros [].
cbn [Frame].
eapply LiftTapes_SpecT_con.
*
smpl_dupfree.
*
cbn.
apply IncrementTwice_SpecT.
*
cbn.
auto.
+
reflexivity.
-
reflexivity.
Restart.
intros x y z.
unfold Incr3.
hsteps_cbn.
apply IncrementTwice_SpecT.
cbn.
eauto.
reflexivity.
Admitted.

Lemma Add_Step_Spec (a b : nat) : Triple (≃≃([], [|Contains _ a; Contains _ b|])) Add_Step (Add_Step_Post (a,b)).
Proof.
start_TM.
eapply If_Spec.
-
apply LiftTapes_Spec.
+
smpl_dupfree.
+
cbn.
eapply CaseNat_Spec.
-
cbn.
hintros ?.
destruct b as [ | b']; cbn [Frame].
contradiction.
eapply Return_Spec_con.
+
cbn [Vector.nth Vector.caseS Vector.case0].
apply LiftTapes_Spec.
*
smpl_dupfree.
*
cbn [Downlift select].
apply Constr_S_Spec.
+
cbn.
intros.
tspec_ext.
-
cbn.
hintros ->.
eapply Return_Spec_con.
+
cbn [Vector.nth Vector.caseS Vector.case0].
apply Nop_Spec.
+
intros [].
Admitted.

Lemma Add_Loop_Spec (a b : nat) : Triple (≃≃([], [|Contains _ a; Contains _ b|])) Add_Loop (fun _ => ≃≃([], [|Contains _ (a+b); Contains _ 0|])).
Proof.
eapply While_SpecReg with (P := fun '(a,b) => (_,_)) (Q := fun '(a,b) y => (_,_)) (* to be instantiated by the first proof obligation *) (R := fun '(a,b) y => (_,_)) (x := (a,b)).
-
intros (x,y).
eapply Add_Step_Spec.
-
intros (x,y);cbn.
split.
+
intros [].
destruct y; intros [=].
replace (x+0) with x by lia.
auto.
+
destruct y;intros [=].
eexists (_,_).
split.
*
tspec_ext.
*
cbn.
tspec_ext.
f_equal.
Admitted.

Lemma Add_Step_SpecT (a b : nat) : TripleT (≃≃([], [|Contains _ a; Contains _ b|])) Add_Step_steps Add_Step (Add_Step_Post (a,b)).
Proof.
start_TM.
unfold Add_Step.
eapply If_SpecT with (k3 := 0).
hsteps.
all:cbn beta.
-
destruct b as [ | b']; cbn in *; auto.
all:hintros ?.
contradiction.
hsteps.
cbn.
tspec_ext.
-
destruct b as [ | b']; cbn in *; auto.
all:hintros ?.
2:congruence.
hsteps.
cbn.
tspec_ext.
-
cbn.
intros.
destruct yout.
reflexivity.
unfold CaseNat_steps, Add_Step_steps.
Admitted.

Lemma Add_Step_SpecT_space (a b : nat) (ss : Vector.t nat 2) : TripleT (≃≃([], withSpace ( [|Contains _ a; Contains _ b|]) ss)) Add_Step_steps Add_Step (fun yout => ≃≃([yout = if b then Some tt else None] ,withSpace [|Contains _ (match b with 0 => a | _ => S a end);Contains _ (pred b)|] (appSize (Add_Step_size a b) ss))).
Proof.
start_TM.
unfold Add_Step.
eapply If_SpecT with (k3 := 0).
-
hsteps_cbn.
-
cbn.
hintros ?.
destruct b as [ | b']; cbn in *.
easy.
hsteps_cbn; cbn.
tspec_ext.
-
cbn.
hintros ->.
hsteps.
cbn.
tspec_ext.
-
intros.
destruct yout.
+
reflexivity.
+
unfold CaseNat_steps, Add_Step_steps.
Admitted.

Lemma Add_Loop_SpecT (a b : nat) : TripleT (≃≃([], [|Contains _ a; Contains _ b|])) (Add_Loop_steps b) (Add_Loop) (fun _ => ≃≃([], [|Contains _ (a+b); Contains _ 0|])).
Proof.
unfold Add_Loop.
eapply While_SpecTReg with (PRE := fun '(a,b) => (_,_)) (INV := fun '(a,b) y => (_,_)) (POST := fun '(a,b) y => (_,_)) (f__step := fun '(a,b) => _) (f__loop := fun '(a,b) => _) (x := (a,b)).
-
intros (x,y).
eapply Add_Step_SpecT.
-
intros (x,y);cbn.
split.
+
intros [].
split.
*
destruct y as [ | y'];cbn.
2:intros;congruence.
tspec_ext.
f_equal.
nia.
*
unfold Add_Step_steps,Add_Loop_steps.
nia.
+
destruct y as [ | y']; cbn in *; auto.
easy.
intros _.
eexists (S x, y') (* or [eexists (_,_)] *); cbn.
repeat split.
*
tspec_ext.
*
unfold Add_Step_steps, Add_Loop_steps.
lia.
*
tspec_ext.
f_equal.
Admitted.

Lemma IncrementTwice_Spec (y : nat) : Triple (≃≃([], [|Contains _ y|])) (IncrementTwice) (fun _ => ≃≃([], [|Contains _ (S (S y))|])).
Proof.
start_TM.
eapply Seq_Spec.
-
apply Constr_S_Spec.
-
cbn.
intros _.
apply Constr_S_Spec.
Restart.
start_TM.
unfold IncrementTwice.
hstep.
apply Constr_S_Spec.
cbn.
intros _.
apply Constr_S_Spec.
Restart.
start_TM.
unfold IncrementTwice.
hsteps_cbn.
eauto.
