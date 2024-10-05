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

Lemma CopyValue_SpecT_size (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) (ss : Vector.t nat 2) : TripleT (≃≃([],withSpace [|Contains _ x; Void|] ss)) (CopyValue_steps x) (CopyValue sig) (fun _ => ≃≃([],withSpace ([|Contains _ x; Contains _ x|]) (appSize (CopyValue_sizefun x) ss))).
Proof.
start_TM.
eapply Realise_TripleT.
-
eapply CopyValue_Realise.
-
eapply CopyValue_Terminates.
-
intros tin [] tout H HEnc.
unfold withSpace in HEnc.
cbn in *.
specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1.
cbn in *.
cbn in *; simpl_vector in *; cbn in *.
modpon H.
intros i; destruct_fin i; cbn in *; eauto.
-
intros tin k HEnc.
unfold withSpace in HEnc.
cbn in *.
specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1.
cbn in *; simpl_vector in *; cbn in *.
Admitted.

Lemma CopyValue_SpecT (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) : TripleT (≃≃([],[|Contains _ x; Void|])) (CopyValue_steps x) (CopyValue sig) (fun _ => ≃≃([],[|Contains _ x; Contains _ x|])).
Proof.
eapply TripleT_RemoveSpace.
cbn.
intros s.
Admitted.

Lemma Reset_SpecT_space (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) (ss : Vector.t nat 1) : TripleT (≃≃([],withSpace ([|Contains _ x|]) ss)) (Reset_steps x) (Reset sig) (fun _ => ≃≃([],withSpace ([|Void|]) (appSize [|Reset_size x|] ss))).
Proof.
start_TM.
eapply Realise_TripleT.
-
eapply Reset_Realise.
-
eapply Reset_Terminates.
-
intros tin [] tout H HEnc.
unfold withSpace in HEnc.
cbn in *.
specialize (HEnc Fin0); cbn in *.
simpl_vector in *; cbn in *.
modpon H.
intros i; destruct_fin i; cbn; eauto.
-
intros tin k HEnc.
unfold withSpace in HEnc.
cbn in *.
specialize (HEnc Fin0).
simpl_vector in *; cbn in *.
Admitted.

Lemma Reset_SpecT (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) : TripleT (≃≃([],[|Contains _ x|])) (Reset_steps x) (Reset sig) (fun _ => ≃≃([], [|Void|])).
Proof.
eapply TripleT_RemoveSpace.
Admitted.

Lemma Reset_Spec (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) : Triple (≃≃([], [|Contains _ x|])) (Reset sig) (fun _ => ≃≃([], [|Void|])).
Proof.
eapply TripleT_Triple.
Admitted.

Lemma MoveValue_SpecT_size (sig : finType) (sigX sigY X Y : Type) (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) (ss : Vector.t nat 2) : TripleT (≃≃([], withSpace ( [|Contains _ x; Contains _ y|]) ss)) (MoveValue_steps x y) (MoveValue sig) (fun _ => ≃≃([], withSpace ( [|Void; Contains _ x|]) (appSize (MoveValue_size x y) ss))).
Proof.
start_TM.
eapply Realise_TripleT.
-
apply MoveValue_Realise with (X := X) (Y := Y).
-
apply MoveValue_Terminates with (X := X) (Y := Y).
-
intros tin [] tout H HEnc.
unfold withSpace in HEnc.
cbn in *.
specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1.
simpl_vector in *; cbn in *.
modpon H.
intros i; destruct_fin i; cbn; eauto.
-
intros tin k HEnc.
unfold withSpace in HEnc.
cbn in *.
specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1.
simpl_vector in *; cbn in *.
Admitted.

Lemma MoveValue_SpecT (sig : finType) (sigX sigY X Y : Type) (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) : TripleT (≃≃([], [|Contains _ x; Contains _ y|])) (MoveValue_steps x y) (MoveValue sig) (fun _ => ≃≃([], [|Void; Contains _ x|])).
Proof.
eapply TripleT_RemoveSpace.
Admitted.

Lemma MoveValue_Spec (sig : finType) (sigX sigY X Y : Type) (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) : Triple (≃≃([], [|Contains _ x; Contains _ y|])) (MoveValue sig) (fun _ => ≃≃([], [|Void; Contains _ x|])).
Proof.
eapply TripleT_Triple.
Admitted.

Lemma Constr_O_Spec_pure : Triple (fun tin => isVoid tin[@Fin0]) (Constr_O) (fun _ tout => tout[@Fin0] ≃ 0).
Proof.
eapply TripleT_Triple.
Admitted.

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
Admitted.

Lemma Constr_S_Spec_pure (y : nat) : Triple (fun tin => tin[@Fin0] ≃ y) (Constr_S) (fun _ tout => tout[@Fin0] ≃ (S y)).
Proof.
eapply TripleT_Triple.
Admitted.

Lemma Constr_O_SpecT_size (ss : Vector.t nat 1) : TripleT (≃≃([], withSpace ( [|Void|]) ss)) Constr_O_steps Constr_O (fun _ => ≃≃([], withSpace ( [|Contains _ 0|]) (appSize [|Constr_O_size|] ss))).
Proof.
start_TM.
eapply RealiseIn_TripleT.
-
apply Constr_O_Sem.
-
intros tin [] tout H1 H2.
unfold withSpace in H2.
cbn in *.
unfold tspec in *.
specialize (H2 Fin0).
simpl_vector in *; cbn in *.
modpon H1.
hnf.
Admitted.

Lemma Constr_O_SpecT : TripleT (≃≃([], [|Void|])) Constr_O_steps Constr_O (fun _ => ≃≃([], [|Contains _ 0|])).
Proof.
Admitted.

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

Lemma Constr_O_SpecT_pure : TripleT (fun tin => isVoid tin[@Fin0]) (Constr_O_steps) (Constr_O) (fun _ tout => tout[@Fin0] ≃ 0).
Proof.
start_TM.
eapply RealiseIn_TripleT.
-
apply Constr_O_Sem.
-
intros tin [] tout H1 H2.
cbn in *.
unfold tspec in *.
modpon H1.
unfold_abbrev.
contains_ext.
