From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import CaseNat CaseList CaseSum.
From Undecidability.TM Require Hoare.
Local Arguments skipn { A } !n !l.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Local Arguments Encode_list : simpl never.
Local Arguments Encode_nat : simpl never.
Set Default Proof Using "Type".
From Undecidability Require Import TM.Basic.Mono TM.Code.Copy.
Section ListStuff.
Variable X : Type.
End ListStuff.
Section Append.
Variable (sigX : finType) (X : Type) (cX : codable sigX X).
Hypothesis (defX: inhabitedC sigX).
Notation sigList := (FinType (EqType (sigList sigX))) (only parsing).
Let stop : sigList^+ -> bool := fun x => match x with | inl (START) => true (* halt at the start symbol *) | _ => false end.
Definition App'_size {sigX X : Type} {cX : codable sigX X} (xs : list X) (s1 : nat) := s1 - (size (Encode_list cX) xs - 1).
Definition App'_Rel : Rel (tapes sigList^+ 2) (unit * tapes sigList^+ 2) := ignoreParam (fun tin tout => forall (xs ys : list X) (s0 s1 : nat), tin[@Fin0] ≃(;s0) xs -> tin[@Fin1] ≃(;s1) ys -> tout[@Fin0] ≃(;s0) xs /\ tout[@Fin1] ≃(;App'_size xs s1) xs ++ ys).
Definition App' : pTM sigList^+ unit 2 := LiftTapes (MoveRight _;; Move Lmove;; Move Lmove) [|Fin0|];; CopySymbols_L stop.
Definition App'_steps {sigX X : Type} {cX : codable sigX X} (xs : list X) := 29 + 12 * size xs.
Definition App'_T : tRel sigList^+ 2 := fun tin k => exists (xs ys : list X), tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ ys /\ App'_steps xs <= k.
Import Hoare.
Definition App'_sizeV (xs : list X) := [| id; App'_size xs |].
Definition App :pTM _ _ 2 := App' @ [|Fin0; Fin1|];; MoveValue _ @ [|Fin1; Fin0|].
Definition App_size (Q Q' : list X) : Vector.t (nat->nat) 2 := [| MoveValue_size_y (Q ++ Q') Q; App'_size Q >> MoveValue_size_x (Q ++ Q') |].
Definition App_Rel : pRel ((sigList sigX) ^+) unit 2 := ignoreParam ( fun tin tout => forall (Q Q' : list X) (s0 s1 : nat), tin[@Fin0] ≃(;s0) Q -> tin[@Fin1] ≃(;s1) Q' -> tout[@Fin0] ≃(;App_size Q Q' @>Fin0 s0) Q ++ Q' /\ isVoid_size tout[@Fin1] (App_size Q Q' @>Fin1 s1) ).
Arguments App_size : simpl never.
Definition App_steps (Q Q': list X) := 1 + App'_steps Q + MoveValue_steps (Q ++ Q') Q.
Definition App_T : tRel (sigList sigX) ^+ 2 := fun tin k => exists (Q Q' : list X), tin[@Fin0] ≃ Q /\ tin[@Fin1] ≃ Q' /\ App_steps Q Q' <= k.
End Append.
Import Hoare.
Ltac hstep_App := lazymatch goal with | [ |- TripleT ?P ?k (App' _) ?Q ] => eapply App'_SpecT | [ |- TripleT ?P ?k (App _) ?Q ] => eapply App_SpecT end.
Smpl Add hstep_App : hstep_Spec.
Arguments App'_steps {sigX X cX} : simpl never.
Arguments App'_size {sigX X cX} : simpl never.
Arguments App_steps {sigX X cX} : simpl never.
Arguments App_size {sigX X cX} : simpl never.
From Undecidability.L.Complexity Require Import UpToC.
Section App_nice.
Variable (sigX X : Type) (cX : codable sigX X).
End App_nice.

Lemma pair_eq (A B : Type) (a1 a2 : A) (b1 b2 : B) : (a1, b1) = (a2, b2) -> a1 = a2 /\ b1 = b2.
Proof.
intros H.
Admitted.

Lemma map_removelast (A B : Type) (f : A -> B) (l : list A) : map f (removelast l) = removelast (map f l).
Proof.
induction l as [ | a l IH]; cbn in *; auto.
destruct l as [ | a' l]; cbn in *; auto.
f_equal.
Admitted.

Corollary removelast_app_singleton (xs : list X) (x : X) : removelast (xs ++ [x]) = xs.
Proof.
destruct xs.
reflexivity.
rewrite removelast_app.
cbn.
rewrite app_nil_r.
reflexivity.
Admitted.

Corollary removelast_cons (xs : list X) (x : X) : xs <> nil -> removelast (x :: xs) = x :: removelast xs.
Proof.
intros.
change (x :: xs) with ([x] ++ xs).
Admitted.

Corollary removelast_length (xs : list X) : length (removelast xs) = length xs - 1.
Proof.
destruct (app_or_nil xs) as [ -> | (x&xs'&->)].
-
cbn.
reflexivity.
-
rewrite removelast_app_singleton.
rewrite app_length.
cbn.
Admitted.

Lemma App'_Realise : App' ⊨ App'_Rel.
Proof.
eapply Realise_monotone.
{
unfold App'.
TM_Correct.
-
apply MoveRight_Realise with (X := list X).
}
{
intros tin ((), tout) H.
cbn.
intros xs ys s0 s1 HEncXs HEncYs.
destruct HEncXs as (ls1&HEncXs&Hs0), HEncYs as (ls2&HEncYs&Hs1).
TMSimp; clear_trivial_eqs.
rename H into HMoveRight; rename H0 into HCopy.
modpon HMoveRight.
repeat econstructor.
destruct HMoveRight as (ls3&HEncXs').
TMSimp.
unfold App'_size in *.
pose proof app_or_nil xs as [ -> | (xs'&x&->) ]; cbn in *; auto.
-
rewrite CopySymbols_L_Fun_equation in HCopy; cbn in *.
inv HCopy; TMSimp.
repeat econstructor.
+
lia.
+
rewrite Encode_list_hasSize.
cbn.
lia.
-
cbv [Encode_list] in *; cbn in *.
rewrite encode_list_app in HCopy.
cbn in *.
rewrite !map_rev, !map_map, <- map_rev in HCopy.
rewrite rev_app_distr in HCopy.
rewrite <- tl_rev in HCopy.
rewrite map_app, <- !app_assoc in HCopy.
rewrite <- tl_map in HCopy.
rewrite map_rev in HCopy.
cbn in *.
rewrite <- app_assoc in HCopy.
cbn in *.
rewrite !List.map_app, !List.map_map in HCopy.
rewrite rev_app_distr in HCopy.
cbn in *.
rewrite map_rev, tl_rev in HCopy.
rewrite app_comm_cons, app_assoc in HCopy.
rewrite CopySymbols_L_correct_moveleft in HCopy; cbn in *; auto.
+
rewrite rev_app_distr, rev_involutive, <- app_assoc in HCopy.
inv HCopy; TMSimp.
*
rewrite <- app_assoc.
cbn.
repeat econstructor.
--
f_equal.
cbn.
rewrite encode_list_app.
rewrite map_map, map_app, <- app_assoc.
cbn.
f_equal.
++
now rewrite rev_involutive, map_removelast.
++
f_equal.
now rewrite map_app, List.map_map, <- app_assoc.
--
lia.
--
f_equal.
cbn.
rewrite rev_involutive, <- !app_assoc, !map_map.
rewrite !encode_list_app.
rewrite map_app, <- app_assoc.
rewrite <- map_removelast.
f_equal.
cbn [encode_list].
rewrite removelast_cons by (intros (?&?) % appendNil; congruence).
cbn.
f_equal.
rewrite !map_app, <- !app_assoc.
rewrite !removelast_app by congruence.
now rewrite !map_app, <- !app_assoc, !map_map.
--
simpl_list.
rewrite encode_list_app.
rewrite skipn_length.
cbn.
simpl_list.
rewrite removelast_length.
cbn.
simpl_list.
simpl_list.
rewrite removelast_length.
cbn.
lia.
+
cbn.
intros ? [ (?&<-&?) % in_rev % in_map_iff | H' % in_rev ] % in_app_iff.
cbn.
auto.
cbn in *.
rewrite rev_involutive, <- map_removelast in H'.
apply in_app_iff in H' as [ (?&<-&?) % in_map_iff | [ <- | [] ] ].
all: auto.
Admitted.

Lemma App'_Terminates : projT1 App' ↓ App'_T.
Proof.
eapply TerminatesIn_monotone.
{
unfold App'.
TM_Correct.
-
apply MoveRight_Realise with (X := list X).
-
apply MoveRight_Realise with (X := list X).
-
apply MoveRight_Terminates with (X := list X).
}
{
intros tin k (xs&ys&HEncXS&HEncYs&Hk).
unfold App'_steps in *.
exists (12+4*size xs), (16+8*size xs).
repeat split; cbn; try lia.
exists (8+4*size xs), 3.
repeat split; cbn; try lia.
eauto.
intros tmid1 () H.
modpon H.
exists 1, 1.
repeat split; try lia.
eauto.
intros tmid ().
intros H; TMSimp; clear_trivial_eqs.
modpon H.
destruct H as (ls&HEncXs); TMSimp.
cbv [Encode_list]; cbn in *.
destruct (app_or_nil xs) as [-> | (xs'&x&->)]; cbn in *.
{
rewrite CopySymbols_L_steps_equation.
cbn.
lia.
}
{
rewrite encode_list_app.
rewrite map_rev, map_map, <- map_rev.
rewrite rev_app_distr.
cbn.
rewrite <- app_assoc, rev_app_distr, <- app_assoc.
cbn.
rewrite CopySymbols_L_steps_moveleft; cbn; auto.
rewrite map_length, !app_length, rev_length.
cbn.
rewrite map_length, rev_length, !app_length, !map_length.
cbn.
rewrite removelast_length.
lia.
}
Admitted.

Lemma App'_SpecT (xs ys:list X) ss: TripleT ≃≃([],withSpace [|Contains _ xs;Contains _ ys|] ss) (App'_steps xs) App' (fun _ => ≃≃([],withSpace [|Contains _ xs;Contains _ (xs++ys)|] (appSize (App'_sizeV xs) ss ))).
Proof.
unfold withSpace in *.
eapply Realise_TripleT.
now apply App'_Realise.
now apply App'_Terminates.
-
intros tin yout tout H [_ HEnc]%tspecE.
cbn in *.
specializeFin HEnc.
simpl_vector in *; cbn in *.
modpon H.
tspec_solve.
-
intros tin k [_ HEnc]%tspecE Hk.
cbn in *.
specializeFin HEnc.
simpl_vector in *; cbn in *.
do 2 eexists.
repeat split.
1-2:contains_ext.
Admitted.

Lemma App_Realise : App ⊨ App_Rel.
Proof.
eapply Realise_monotone.
{
unfold App.
TM_Correct.
-
apply App'_Realise.
}
{
intros tin ((), tout) H.
intros Q Q' s0 s1 HEncQ HEncQ'.
TMSimp.
modpon H.
modpon H0.
auto.
Admitted.

Lemma App_Terminates : projT1 App ↓ App_T.
Proof.
eapply TerminatesIn_monotone.
{
unfold App.
TM_Correct.
-
apply App'_Realise.
-
apply App'_Terminates.
}
{
intros tin k (Q&Q'&HEncQ&HEncQ'&Hk).
exists (App'_steps Q), (MoveValue_steps (Q++Q') Q); cbn; repeat split; try lia.
hnf; cbn.
eauto.
now rewrite Hk.
intros tmid () (HApp&HInjApp); TMSimp.
modpon HApp.
exists (Q++Q'), Q.
repeat split; eauto.
Admitted.

Lemma App_SpecT (xs ys:list X) ss: TripleT ≃≃([],withSpace [|Contains _ xs;Contains _ ys|] ss) (App_steps xs ys) App (fun _ => ≃≃([],withSpace [|Contains _ (xs++ys);Void|] (appSize (App_size xs ys) ss ))).
Proof.
unfold withSpace in *.
eapply Realise_TripleT.
now apply App_Realise.
now apply App_Terminates.
-
intros tin yout tout H [_ HEnc]%tspecE.
cbn in *.
specializeFin HEnc.
simpl_vector in *; cbn in *.
modpon H.
tspec_solve.
-
intros tin k [_ HEnc]%tspecE Hk.
cbn in *.
specializeFin HEnc.
simpl_vector in *; cbn in *.
do 2 eexists.
repeat split.
1-2:contains_ext.
Admitted.

Lemma app_or_nil (xs : list X) : xs = nil \/ exists ys y, xs = ys ++ [y].
Proof.
induction xs as [ | x xs IH]; cbn in *.
-
now left.
-
destruct IH as [ -> | (ys&y&->) ].
+
right.
exists nil, x.
cbn.
reflexivity.
+
right.
exists (x :: ys), y.
cbn.
reflexivity.
