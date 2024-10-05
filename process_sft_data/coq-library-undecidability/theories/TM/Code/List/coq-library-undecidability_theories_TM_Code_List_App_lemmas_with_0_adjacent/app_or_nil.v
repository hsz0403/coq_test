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
