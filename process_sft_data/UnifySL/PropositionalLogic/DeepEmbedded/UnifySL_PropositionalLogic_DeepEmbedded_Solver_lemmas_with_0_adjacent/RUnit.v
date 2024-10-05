Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Logic.PropositionalLogic.DeepEmbedded.Deep.
Local Open Scope list_scope.
Ltac length_cont ls k := match ls with | nil => k O | _ :: ?ls' => length_cont ls' ltac:(fun n => k (S n)) end.
Ltac length ls := length_cont ls ltac:(fun l => l).
Definition rev (l: list nat): list nat := (fix rev (l: list nat) (cont: list nat -> list nat): list nat := match l with | nil => cont nil | a :: l0 => rev l0 (fun l => a :: cont l) end) l (fun l => l).
Ltac reverse_cont l k := match l with | @nil ?T => k (@nil T) | @cons _ ?h ?t => let k' l := let t' := k l in constr:(cons h t') in reverse_cont t k' end.
Ltac reverse l := reverse_cont l ltac:(fun l => l).
Ltac pred n := match n with | O => O | S ?m => m end.
Ltac search_expr' n i l l0 := match l with | nil => let len := length l0 in constr:((S len, n :: l0)) | n :: ?t => constr:((i, l0)) | _ :: ?t => let pi := pred i in search_expr' n pi t l0 end.
Ltac search_expr n l := let len := length l in search_expr' n len l l.
Section Temp.
Context {L : Language} {minL : MinimumLanguage L} {pL : PropositionalLanguage L}.
Fixpoint reflect (tbl : list Base.expr) (e : Deep.expr) : Base.expr := match e with | Deep.varp n => List.nth (pred n) tbl Syntax.falsep | Deep.andp e1 e2 => Syntax.andp (reflect tbl e1) (reflect tbl e2) | Deep.impp e1 e2 => Syntax.impp (reflect tbl e1) (reflect tbl e2) | Deep.orp e1 e2 => Syntax.orp (reflect tbl e1) (reflect tbl e2) | Deep.falsep => Syntax.falsep end.
End Temp.
Ltac shallowToDeep' se l0 := match se with | Syntax.andp ?sp ?sq => match shallowToDeep' sp l0 with | (?dp, ?l1) => match shallowToDeep' sq l1 with | (?dq, ?l2) => constr:((Deep.andp dp dq, l2)) end end | Syntax.impp ?sp ?sq => match shallowToDeep' sp l0 with | (?dp, ?l1) => match shallowToDeep' sq l1 with | (?dq, ?l2) => constr:((Deep.impp dp dq, l2)) end end | ?sp => match search_expr sp l0 with | (?i, ?l1) => constr:((Deep.varp i, l1)) end end.
Ltac shallowToDeep se := match shallowToDeep' se constr:(@nil Base.expr) with | (?de, ?tbl) => let tbl' := reverse tbl in assert (reflect tbl' de = se) by reflexivity end.
Section Temp.
Context (L : Base.Language) (minL : Syntax.MinimumLanguage L) (pL : Syntax.PropositionalLanguage L).
Context (P Q R : Base.expr).
Goal False.
let n := search_expr 1 (1 :: 2 :: 3 :: 4 :: nil) in pose n.
let n := search_expr 5 (1 :: 2 :: 3 :: 4 :: nil) in pose n.
shallowToDeep (Syntax.impp (Syntax.andp P Q) (Syntax.orp Q P)).
Abort.
End Temp.
Section Temp.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {GammaP: Provable L} {minAX: MinimumAxiomatization L GammaP} {ipGamma: IntuitionisticPropositionalLogic L GammaP}.
End Temp.
Module DSolver.
Local Existing Instances Deep.L Deep.minL Deep.pL Deep.GP Deep.minAX Deep.ipG.
Instance Adj : Adjointness _ _ andp impp.
Proof.
constructor.
split; intros.
-
rewrite <- impp_uncurry.
auto.
-
rewrite <- impp_curry.
auto.
Instance Comm : Commutativity _ _ andp.
Proof.
constructor.
intros.
rewrite andp_comm.
apply provable_impp_refl.
Instance Mono : Monotonicity _ _ andp.
Proof.
constructor.
intros.
apply solve_impp_andp.
-
rewrite andp_elim1.
auto.
-
rewrite andp_elim2.
auto.
Instance Assoc : Associativity _ _ andp.
Proof.
constructor; intros; rewrite andp_assoc; apply provable_impp_refl.
Instance LUnit : LeftUnit _ _ truep andp.
Proof.
constructor; intros; rewrite truep_andp; apply provable_impp_refl.
Instance RUnit : RightUnit _ _ truep andp.
Proof.
constructor; intros; rewrite andp_truep; apply provable_impp_refl.
Fixpoint flatten_imp (e : expr) : list expr * expr := match e with | Deep.impp p q => let (cxt, fq) := flatten_imp q in (p :: cxt, fq) | _ => (nil, e) end.
Definition flatten_imp_inv (p : list Deep.expr * Deep.expr) := let (ctx, r) := p in multi_imp ctx r.
Fixpoint flatten_and (e : expr) : list expr := match e with | Deep.andp p q => (flatten_and p ++ flatten_and q) | s => s :: nil end.
Definition flatten_and_inv (es : list expr) := List.fold_left andp es truep.
Definition flatten (e : expr) : list expr * list expr := let (ctx, r) := flatten_imp e in (List.flat_map flatten_and ctx, flatten_and r).
Definition AllInContext (es1 es2 : list expr) : Prop := Forall (fun e => In e es1) es2.
Definition all_in_context e := let (es, rs) := flatten e in forallb (fun r => existsb (Deep.beq r) es) rs.
End DSolver.
Module SolverSound.
Ltac ipSolver' se := match shallowToDeep' se constr:(@nil Base.expr) with | (?de, ?tbl) => let tbl' := reverse tbl in let b := eval hnf in (DSolver.all_in_context de) in assert (DSolver.all_in_context de = b) by reflexivity; assert (reflect tbl' de = se) by reflexivity; apply (reify_sound tbl' de); apply DSolver.all_in_provable; match goal with | [H : DSolver.all_in_context _ = true |- _] => apply H end end.
Ltac ipSolver := match goal with | [|- Base.provable ?e] => ipSolver' e end.
Section Temp.
Context {L: Language} {minL: MinimumLanguage L} {pL: PropositionalLanguage L} {GammaP: Provable L} {minAX: MinimumAxiomatization L GammaP} {ipGamma: IntuitionisticPropositionalLogic L GammaP}.
Parameter (P Q R : expr).
Goal (provable (impp (andp P Q) (andp Q P))).
ipSolver.
End Temp.
End SolverSound.

Instance RUnit : RightUnit _ _ truep andp.
Proof.
constructor; intros; rewrite andp_truep; apply provable_impp_refl.
