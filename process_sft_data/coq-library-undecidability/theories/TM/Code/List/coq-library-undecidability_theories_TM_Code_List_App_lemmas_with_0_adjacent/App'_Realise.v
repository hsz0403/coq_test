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
}
