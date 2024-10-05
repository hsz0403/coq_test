Require Import FunInd.
From Undecidability Require Import TM.Util.Prelim.
From Undecidability Require Import TM.Basic.Basic.
From Undecidability Require Import TM.Combinators.Combinators.
From Undecidability.TM.Compound Require Import TMTac Multi MoveToSymbol.
Require Recdef.
Set Default Proof Using "Type".
Section Compare.
Import Recdef.
Variable sig : finType.
Variable stop : sig -> bool.
Definition Compare_Step : pTM sig (option bool) 2 := Switch (CaseChar2 (fun c1 c2 => match c1, c2 with | Some c1, Some c2 => if (stop c1) && (stop c2) then Some true (* both stop symbols were reached at the same time ~> strings are equal *) else if (stop c1) || (stop c2) then Some false (* Only one stop symbol was reached ~> one string is longer *) else if Dec (c1 = c2) then None (* up to here, the strings are the same *) else Some false (* symbols differ! *) | _, _ => Some false (* At least one string not terminated *) end)) (fun x : option bool => match x with | Some b => Return Nop (Some b) | None => Return (MovePar Rmove Rmove) None end).
Definition Compare_Step_Rel : pRel sig (option bool) 2 := fun tin '(yout, tout) => match current tin[@Fin0], current tin[@Fin1] with | Some c1, Some c2 => if (stop c1) && (stop c2) then yout = Some true /\ tout = tin else if (stop c1) || (stop c2) then yout = Some false /\ tout = tin else if Dec (c1 = c2) then yout = None /\ tout[@Fin0] = tape_move_right tin[@Fin0] /\ tout[@Fin1] = tape_move_right tin[@Fin1] else yout = Some false /\ tout = tin | _, _ => yout = Some false /\ tout = tin end.
Definition Compare := While Compare_Step.
Definition Compare_fun_measure (t : tape sig * tape sig) : nat := length (tape_local (fst t)).
Function Compare_fun (t : tape sig * tape sig) {measure Compare_fun_measure t} : bool * (tape sig * tape sig) := match (current (fst t)), (current (snd t)) with | Some c1, Some c2 => if (stop c1) && (stop c2) then (true, t) else if (stop c1) || (stop c2) then (false, t) else if Dec (c1 = c2) then Compare_fun (tape_move_right (fst t), tape_move_right (snd t)) else (false, t) | _, _ => (false, t) end.
Proof.
intros (t1&t2).
intros c1 Hc1 c2 Hc2 HStopC1 HStopC2.
cbn in *.
destruct t1; cbn in *; inv Hc1.
destruct t2; cbn in *; inv Hc2.
unfold Compare_fun_measure.
cbn.
simpl_tape.
intros.
lia.
Definition Compare_Rel : pRel sig bool 2 := fun tin '(yout, tout) => (yout, (tout[@Fin0], tout[@Fin1])) = Compare_fun (tin[@Fin0], tin[@Fin1]).
Local Arguments plus : simpl never.
Function Compare_steps (t : tape sig * tape sig) { measure Compare_fun_measure} : nat := match (current (fst t)), (current (snd t)) with | Some c1, Some c2 => if (stop c1) && (stop c2) then 5 else if (stop c1) || (stop c2) then 5 else if Dec (c1 = c2) then 6 + Compare_steps (tape_move_right (fst t), tape_move_right (snd t)) else 5 | _, _ => 5 end.
Proof.
intros (t1&t2).
intros c1 Hc1 c2 Hc2 HStopC1 HStopC2.
cbn in *.
destruct t1; cbn in *; inv Hc1.
destruct t2; cbn in *; inv Hc2.
unfold Compare_fun_measure.
cbn.
simpl_tape.
intros.
lia.
Definition Compare_T : tRel sig 2 := fun tin k => Compare_steps (tin[@Fin0], tin[@Fin1]) <= k.
End Compare.
Section CompareLists.
Variable X : eqType.
Definition list_comperasion (xs ys : list X) : Prop := xs = ys \/ (exists a b l1 l2 l3, a <> b /\ xs = l1 ++ a :: l2 /\ ys = l1 ++ b :: l3) \/ (exists a l1 l2, xs = l1 ++ a :: l2 /\ ys = l1) \/ (exists a l1 l2, xs = l1 /\ ys = l1 ++ a :: l2).
Definition list_comperasion_cons xs ys x : list_comperasion xs ys -> list_comperasion (x :: xs) (x :: ys).
Proof.
destruct 1 as [ <- | [ (a&b&l1&l2&l3&H1&H2&H3) | [ (a&l1&l2&H1&H2) | (a&l1&l2&H1&H2) ]]].
-
left.
reflexivity.
-
subst.
right; left.
exists a, b, (x::l1), l2, l3.
auto.
-
subst.
right.
right.
left.
do 3 eexists.
split.
2: reflexivity.
cbn.
eauto.
-
subst.
right.
right.
right.
do 3 eexists.
split.
1: reflexivity.
cbn.
eauto.
End CompareLists.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Section Compare_fun_lemmas.
Variable (X : finType) (stop : X -> bool).
Definition swap (A B : Type) : A*B->B*A := ltac:(intros [b a]; now constructor).
End Compare_fun_lemmas.

Lemma Compare_TerminatesIn : projT1 Compare ↓ Compare_T.
Proof.
eapply TerminatesIn_monotone.
{
unfold Compare.
TM_Correct.
-
eapply RealiseIn_Realise.
apply Compare_Step_Sem.
-
eapply RealiseIn_TerminatesIn.
apply Compare_Step_Sem.
}
{
apply WhileCoInduction; intros.
exists 5.
split.
reflexivity.
intros [ yout | ].
-
intros.
hnf in HT.
TMCrush.
all: rewrite <- HT.
all: apply Compare_steps_ge.
-
intros.
hnf in HT.
exists (Compare_steps (tape_move tin[@Fin0] Rmove, tape_move tin[@Fin1] Rmove)).
TMCrush.
split.
+
hnf.
TMSimp.
auto.
+
rewrite Compare_steps_equation in HT.
cbn in HT.
rewrite E, E0, E1, E2 in HT.
rewrite E3 in *.
lia.
}
