From Undecidability.H10 Require Import H10 dio_single dio_logic.
Require Import Undecidability.PCP.Util.PCP_facts.
Require Import Undecidability.Shared.Libs.PSL.FiniteTypes Undecidability.Shared.Libs.PSL.FiniteTypes.Arbitrary.
From Undecidability.Synthetic Require Export DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability.L.Datatypes Require Import LNat Lists LProd.
From Undecidability.L Require Import Tactics.LTactics Computability.MuRec Computability.Synthetic Tactics.GenEncode.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos.
Import ListAutomationNotations.
Require Import Nat Datatypes.
Inductive poly : Set := poly_cnst : nat -> poly | poly_var : nat -> poly | poly_add : poly -> poly -> poly | poly_mul : poly -> poly -> poly.
MetaCoq Run (tmGenEncode "enc_poly" poly).
Hint Resolve enc_poly_correct : Lrewrite.
Instance term_poly_cnst: computable poly_cnst.
Proof.
extract constructor.
Instance term_poly_var : computable poly_var.
Proof.
extract constructor.
Instance term_poly_add : computable poly_add.
Proof.
extract constructor.
Instance term_poly_mul : computable poly_mul.
Proof.
extract constructor.
Fixpoint eval (p : poly) (L : list nat) := match p with | poly_cnst n => n | poly_var n => nth n L 0 | poly_add p1 p2 => eval p1 L + eval p2 L | poly_mul p1 p2 => eval p1 L * eval p2 L end.
Instance term_eval : computable eval.
Proof.
extract.
Definition poly_add' '(x,y) : poly := poly_add x y.
Instance term_poly_add' : computable poly_add'.
Proof.
extract.
Definition poly_mul' '(x,y) : poly := poly_mul x y.
Instance term_poly_mul' : computable poly_mul'.
Proof.
extract.
Fixpoint L_poly n : list (poly) := match n with | 0 => [] | S n => L_poly n ++ map poly_cnst (L_nat n) ++ map poly_var (L_nat n) ++ map poly_add' (list_prod (L_poly n) (L_poly n)) ++ map poly_mul' (list_prod (L_poly n) (L_poly n)) end.
Instance term_L_poly : computable L_poly.
Proof.
extract.
Instance enum_poly : list_enumerator__T L_poly poly.
Proof.
intros p.
induction p.
+
destruct (el_T n) as [m].
exists (1 + m).
cbn.
in_app 2.
in_collect n.
exact H.
+
destruct (el_T n) as [m].
exists (1 + m).
cbn.
in_app 3.
eauto.
+
destruct IHp1 as [m1].
destruct IHp2 as [m2].
exists (1 + m1 + m2).
cbn.
in_app 4.
in_collect (p1, p2); eapply cum_ge'; eauto; lia.
+
destruct IHp1 as [m1].
destruct IHp2 as [m2].
exists (1 + m1 + m2).
cbn.
in_app 5.
in_collect (p1, p2); eapply cum_ge'; eauto; lia.
Defined.
Fixpoint conv n (p : dio_single.dio_polynomial (pos n) (pos 0)) : poly.
Proof.
destruct p as [ | p | p | ].
-
exact (poly_cnst n0).
-
exact (poly_var (pos.pos2nat p)).
-
invert pos p.
-
destruct d.
+
exact (poly_add (conv _ p1) (conv _ p2)).
+
exact (poly_mul (conv _ p1) (conv _ p2)).
Defined.
Fixpoint L_from (n : nat) : (pos n -> nat) -> list nat.
Proof.
intros phi.
destruct n.
-
exact [].
-
refine (_ :: L_from _ _)%list.
+
exact (phi pos.pos_fst).
+
intros.
eapply phi.
econstructor 2.
exact H.
Defined.
Definition test_eq := (fun '(p1,p2,L) => Nat.eqb (eval p1 L) (eval p2 L)).
Instance term_test_eq : computable test_eq.
Proof.
extract.
Definition cons' : nat * list nat -> list nat := fun '(n, L) => n :: L.
Instance term_cons' : computable cons'.
Proof.
extract.
Definition T_list_nat := @L_list nat opt_to_list.
Instance computable_cumul {X} `{registered X} : computable (@cumul X).
Proof.
extract.
Instance term_T_list : computable T_list_nat.
Proof.
unfold T_list_nat, L_list.
change (computable (fix T_list (n : nat) : list (list nat) := match n with | 0 => [[]] | S n0 => (T_list n0 ++ map cons' (L_nat n0 × T_list n0))%list end)).
extract.
Fixpoint poly_eqb p1 p2 := match p1, p2 with | poly_cnst n1, poly_cnst n2 => Nat.eqb n1 n2 | poly_var v1, poly_var v2 => Nat.eqb v1 v2 | poly_add p1 p2, poly_add p1' p2' => poly_eqb p1 p1' && poly_eqb p2 p2' | poly_mul p1 p2, poly_mul p1' p2' => poly_eqb p1 p1' && poly_eqb p2 p2' | _,_ => false end.
Instance term_poly_beq : computable poly_eqb.
Proof.
extract.

Instance term_test_eq : computable test_eq.
Proof.
extract.
