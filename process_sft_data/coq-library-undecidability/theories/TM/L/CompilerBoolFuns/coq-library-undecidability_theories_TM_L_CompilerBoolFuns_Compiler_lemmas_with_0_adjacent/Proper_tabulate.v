From Undecidability.Shared.Libs.PSL Require Import FinTypes Vectors.
From Undecidability.L Require Import L_facts LM_heap_def.
From Coq Require Import List.
Import Vector.VectorNotations ListNotations.
From Undecidability.TM Require Import TM_facts ProgrammingTools WriteValue CaseList Copy ListTM Hoare.
From Undecidability.TM.L Require Import Alphabets Eval.
From Undecidability.TM.L.CompilerBoolFuns Require Import Compiler_spec Compiler_facts ClosedLAdmissible.
Require Import Equations.Prop.DepElim.
Set Default Proof Using "Type".
Section APP_right.
Definition APP_right : pTM (sigPro)^+ unit 2 := App _;; WriteValue ( [appT]%list) @ [|Fin1|];; App _.
End APP_right.
Hint Rewrite Nat.eqb_refl tabulate_nth nth_tabulate: cleanupParamTM.
Ltac cleanupParamTM := try fold Nat.add;rewrite ?Nat.eqb_refl, ?tabulate_nth, ?nth_tabulate;cbn.
Section MK_isVoid.
Context {Σ : finType}.
Definition MK_isVoid : pTM Σ^+ unit 1 := Write (inl UNKNOWN).
Fixpoint MK_isVoid_multi m' : pTM (Σ) ^+ unit m' := match m' with 0 => Nop | S m' => MK_isVoid @ [|Fin0|];;MK_isVoid_multi m'@(tabulate (fun i => Fin.FS i)) end.
Instance Proper_tabulate X n: Proper (pointwise_relation _ eq ==> eq) (@tabulate X n).
Proof.
unfold pointwise_relation.
induction n;hnf;intros f g H;cbn.
reflexivity.
f_equal.
apply H.
now apply IHn.
End MK_isVoid.
Opaque MK_isVoid_multi.
From Undecidability Require Import TM.L.Transcode.Boollist_to_Enc.
From Undecidability Require Import EncBoolsTM_boolList.
Section mk_init_one.
Variable Σ : finType.
Variable s b : Σ^+.
Variable (H_disj : s <> b).
Variable (retr_pro : Retract sigPro Σ).
Variable (retr_list : Retract (sigList bool) Σ).
Definition M_init_one : pTM (Σ) ^+ unit 6:= encBoolsTM2boollist.M s retr_list @[|Fin0;Fin3|];; Rev _ ⇑ retr_list @ [|Fin3;Fin2;Fin4|];; BoollistToEnc.M retr_list retr_pro @[|Fin2;Fin3;Fin4;Fin5|];; APP_right ⇑ retr_pro @[|Fin1;Fin3|].
End mk_init_one.
Section mk_init.
Variable Σ : finType.
Variable s b : Σ^+.
Variable (H_disj : s <> b).
Context (retr_pro : Retract sigPro Σ) (retr_bools : Retract (sigList bool) Σ).
Variable m k : nat.
Variable sim : term.
Notation aux n := (Fin.L k (Fin.L m n)) (only parsing).
Notation auxm n := (Fin.L k (Fin.R 6 n)) (only parsing).
Notation auxk n := (Fin.R (6 + m) n) (only parsing).
Fixpoint M_init' k' : (Vector.t (Fin.t k) k') -> pTM (Σ) ^+ unit ((6 + m)+ k).
Proof using m s retr_bools sim retr_pro.
simple notypeclasses refine (match k' with 0 => fun _ => MK_isVoid_multi _ @ [|aux Fin1;aux Fin2;aux Fin3;aux Fin4; aux Fin5|];; WriteValue ( (compile sim)) ⇑ retr_pro @ [|aux Fin1|] | S k' => fun ren => _;;M_init_one s retr_pro retr_bools @ [|auxk (ren[@Fin0]);aux Fin1;aux Fin2;aux Fin3;aux Fin4;aux Fin5|] end).
all:try exact _.
2:{
apply (M_init' _ (Vector.tl ren)).
}
Defined.
Program Definition startRen := Vectors.tabulate (n:=k) (fun i => Fin.of_nat_lt (n:=k) (p:=k - 1 -proj1_sig (Fin.to_nat i)) _).
Next Obligation.
destruct Fin.to_nat;cbn.
nia.
Defined.
Import CasePair Code.CaseList.
Definition M_init : pTM (Σ) ^+ unit ((6 + m)+ k) := M_init' startRen.
End mk_init.
From Undecidability Require Import Enc_to_Boollist.
Section conv_output.
Variable Σ : finType.
Variable s b : Σ^+.
Variable (retr_pro : Retract sigPro Σ).
Variable (retr_list : Retract (sigList bool) Σ).
Definition M_out : pTM (Σ) ^+ unit 4 := EncToBoollist.M _ _ @ [|Fin0;Fin2;Fin3|];; Boollist2encBoolsTM.M s b _ @ [|Fin2;Fin1;Fin3|].
End conv_output.
Section main.
Variable k : nat.
Variable (R : Vector.t (list bool) k -> (list bool) -> Prop).
Variable s : term.
Hypothesis Hscl : closed s.
Variable Hs1 : (forall v, forall m : list bool, R v m <-> L.eval (Vector.fold_left (fun (s0 : term) (n : list bool) => L.app s0 (encBoolsL n)) s v) (encBoolsL m)).
Variable Hs2 : (forall v, forall o : term, L.eval (Vector.fold_left (n := k) (fun (s0 : term) (n : list bool) => L.app s0 (encBoolsL n)) s v) o -> exists m : list bool, o = encBoolsL m).
Definition n_main := 14.
Definition Σ : Type := sigList bool + EvalL.Σintern.
Definition retr_bools : Retract (sigList bool) Σ := (Retract_inl _ _).
Definition retr_intern : Retract EvalL.Σintern Σ := (Retract_inr _ _).
Definition retr_closs : Retract (sigList sigHClos) Σ := ComposeRetract retr_intern _.
Definition retr_clos : Retract sigHClos Σ := ComposeRetract retr_closs _.
Definition retr_pro : Retract sigPro Σ := ComposeRetract retr_clos _.
Definition sym_s : Σ^+ := inr (inl (sigList_X true)).
Definition sym_b : Σ^+ := inr (inl (sigList_X false)).
Notation aux n := (Fin.L k (Fin.R 1 n)).
Definition garb : Σ^+ := inl UNKNOWN.
Definition M_main : pTM (Σ ^+) unit (1 + n_main + k):= M_init sym_s retr_pro retr_bools (1 + n_main - 6) k s ;; MK_isVoid_multi _ @ [|aux Fin5;aux Fin6;aux Fin7;aux Fin8;aux Fin9;aux Fin10;aux Fin11;aux Fin12;aux Fin13 |] ;; EvalL.M retr_intern retr_pro @ [| aux Fin0 ; aux Fin1 ; aux Fin2; aux Fin5 ; aux Fin6 ; aux Fin7 ; aux Fin8 ; aux Fin9 ; aux Fin10 ; aux Fin11 ; aux Fin12 |] ;; M_out sym_s sym_b retr_pro retr_bools @ [|aux Fin0;Fin.L k Fin0;aux Fin7;aux Fin8|].
End main.

Instance Proper_tabulate X n: Proper (pointwise_relation _ eq ==> eq) (@tabulate X n).
Proof.
unfold pointwise_relation.
induction n;hnf;intros f g H;cbn.
reflexivity.
f_equal.
apply H.
now apply IHn.
