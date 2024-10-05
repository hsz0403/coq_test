Require Import Reals.
Require Import Rcomplements Hierarchy Derive RInt RInt_analysis Derive_2d Continuity ElemFct.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.seq Datatypes.
Fixpoint Rn n T := match n with | O => T | S n => R -> Rn n T end.
Inductive bop := | Eplus | Emult.
Inductive uop := | Eopp | Einv | Efct : forall (f f' : R -> R), (forall x, is_derive f x (f' x)) -> uop | Efct' : forall (f f' : R -> R) (df : R -> Prop), (forall x, df x -> is_derive f x (f' x)) -> uop.
Inductive expr := | Var : nat -> expr | AppExt : forall k, Rn k R -> seq expr -> expr | AppExtD : forall k, Rn k R -> nat -> seq expr -> expr | App : expr -> expr -> expr | Subst : expr -> expr -> expr | Cst : R -> expr | Binary : bop -> expr -> expr -> expr | Unary : uop -> expr -> expr | Int : expr -> expr -> expr -> expr.
Section ExprInduction.
Hypothesis P : expr -> Prop.
Hypothesis P_Var : forall n, P (Var n).
Hypothesis P_AppExt : forall k f le, foldr (fun e acc => P e /\ acc) True le -> P (AppExt k f le).
Hypothesis P_AppExtD : forall k f n le, foldr (fun e acc => P e /\ acc) True le -> P (AppExtD k f n le).
Hypothesis P_App : forall e1 e2, P e1 -> P e2 -> P (App e1 e2).
Hypothesis P_Subst : forall e1 e2, P e1 -> P e2 -> P (Subst e1 e2).
Hypothesis P_Cst : forall r, P (Cst r).
Hypothesis P_Binary : forall o e1 e2, P e1 -> P e2 -> P (Binary o e1 e2).
Hypothesis P_Unary : forall o e, P e -> P (Unary o e).
Hypothesis P_Int : forall f e1 e2, P f -> P e1 -> P e2 -> P (Int f e1 e2).
Fixpoint expr_ind' (e : expr) : P e := match e return P e with | Var n => P_Var n | AppExt k f le => P_AppExt k f le ((fix expr_ind'' (le : seq expr) : foldr (fun e acc => P e /\ acc) True le := match le return foldr (fun e acc => P e /\ acc) True le with | nil => I | cons h q => conj (expr_ind' h) (expr_ind'' q) end) le) | AppExtD k f n le => P_AppExtD k f n le ((fix expr_ind'' (le : seq expr) : foldr (fun e acc => P e /\ acc) True le := match le return foldr (fun e acc => P e /\ acc) True le with | nil => I | cons h q => conj (expr_ind' h) (expr_ind'' q) end) le) | App e1 e2 => P_App e1 e2 (expr_ind' e1) (expr_ind' e2) | Subst e1 e2 => P_Subst e1 e2 (expr_ind' e1) (expr_ind' e2) | Cst r => P_Cst r | Binary o e1 e2 => P_Binary o e1 e2 (expr_ind' e1) (expr_ind' e2) | Unary o e => P_Unary o e (expr_ind' e) | Int f e1 e2 => P_Int f e1 e2 (expr_ind' f) (expr_ind' e1) (expr_ind' e2) end.
End ExprInduction.
Fixpoint apply {T} p : Rn p T -> (nat -> R) -> T := match p return Rn p T -> _ -> T with | O => fun (x : T) _ => x | S p => fun (f : Rn (S p) T) g => apply p (f (g p)) g end.
Definition Derive_Rn n (f : Rn n R) p g := Derive (fun x => apply n f (fun i => if ssrnat.eqn i p then x else g i)) (g p).
Definition ex_derive_Rn n (f : Rn n R) p g := ex_derive (fun x => apply n f (fun i => if ssrnat.eqn i p then x else g i)) (g p).
Fixpoint interp (l : seq R) (e : expr) : R := match e with | Var n => nth R0 l n | AppExt k f le => apply k f (nth 0 (map (interp l) le)) | AppExtD k f n le => Derive_Rn k f n (nth 0 (map (interp l) le)) | App e1 e2 => interp ((interp l e2) :: l) e1 | Subst e1 e2 => interp (set_nth R0 l 0 (interp l e2)) e1 | Cst c => c | Binary o e1 e2 => match o with Eplus => Rplus | Emult => Rmult end (interp l e1) (interp l e2) | Unary o e => match o with Eopp => Ropp | Einv => Rinv | Efct f f' H => f | Efct' f f' df H => f end (interp l e) | Int e1 e2 e3 => RInt (fun x => interp (x :: l) e1) (interp l e2) (interp l e3) end.
Inductive domain := | Never : domain | Always : domain | Partial : (R -> Prop) -> expr -> domain | Derivable : nat -> forall k, Rn k R -> seq expr -> domain | Derivable2 : nat -> nat -> forall k, Rn k R -> seq expr -> domain | Continuous : nat -> expr -> domain | Continuous2 : nat -> nat -> expr -> domain | Integrable : expr -> expr -> expr -> domain | ParamIntegrable : nat -> expr -> expr -> expr -> domain | LocallyParamIntegrable : nat -> expr -> expr -> domain | And : seq domain -> domain | Forall : expr -> expr -> domain -> domain | Forone : expr -> domain -> domain | Locally : nat -> domain -> domain | Locally2 : nat -> nat -> domain -> domain | ForallWide : nat -> expr -> expr -> domain -> domain.
Section DomainInduction.
Hypothesis P : domain -> Prop.
Hypothesis P_Never : P Never.
Hypothesis P_Always : P Always.
Hypothesis P_Partial : forall p e, P (Partial p e).
Hypothesis P_Derivable : forall n k f le, P (Derivable n k f le).
Hypothesis P_Derivable2 : forall m n k f le, P (Derivable2 m n k f le).
Hypothesis P_Continuous : forall n e, P (Continuous n e).
Hypothesis P_Continuous2 : forall m n e, P (Continuous2 m n e).
Hypothesis P_Integrable : forall f e1 e2, P (Integrable f e1 e2).
Hypothesis P_ParamIntegrable : forall n f e1 e2, P (ParamIntegrable n f e1 e2).
Hypothesis P_LocallyParamIntegrable : forall n f e, P (LocallyParamIntegrable n f e).
Hypothesis P_And : forall ld, foldr (fun d acc => P d /\ acc) True ld -> P (And ld).
Hypothesis P_Forall : forall e1 e2 d, P d -> P (Forall e1 e2 d).
Hypothesis P_Forone : forall e d, P d -> P (Forone e d).
Hypothesis P_Locally : forall n d, P d -> P (Locally n d).
Hypothesis P_Locally2 : forall m n d, P d -> P (Locally2 m n d).
Hypothesis P_ForallWide : forall n e1 e2 d, P d -> P (ForallWide n e1 e2 d).
Fixpoint domain_ind' (d : domain) : P d := match d return P d with | Never => P_Never | Always => P_Always | Partial d e => P_Partial d e | Derivable n k f le => P_Derivable n k f le | Derivable2 m n k f le => P_Derivable2 m n k f le | Continuous n e => P_Continuous n e | Continuous2 m n e => P_Continuous2 m n e | Integrable f e1 e2 => P_Integrable f e1 e2 | ParamIntegrable n f e1 e2 => P_ParamIntegrable n f e1 e2 | LocallyParamIntegrable n f e => P_LocallyParamIntegrable n f e | And ld => P_And ld ((fix domain_ind'' (ld : seq domain) : foldr (fun d acc => P d /\ acc) True ld := match ld return foldr (fun d acc => P d /\ acc) True ld with | nil => I | cons h q => conj (domain_ind' h) (domain_ind'' q) end) ld) | Forall e1 e2 d => P_Forall e1 e2 d (domain_ind' d) | Forone e d => P_Forone e d (domain_ind' d) | Locally n d => P_Locally n d (domain_ind' d) | Locally2 m n d => P_Locally2 m n d (domain_ind' d) | ForallWide n e1 e2 d => P_ForallWide n e1 e2 d (domain_ind' d) end.
End DomainInduction.
Fixpoint interp_domain (l : seq R) (d : domain) : Prop := match d with | Never => False | Always => True | Partial p e => p (interp l e) | Derivable n k f le => ex_derive_Rn k f n (nth 0 (map (interp l) le)) | Derivable2 m n k f le => let le' := map (interp l) le in locally_2d (fun u v => ex_derive_Rn k f m (fun i => if ssrnat.eqn i m then u else if ssrnat.eqn i n then v else nth 0 le' i)) (nth 0 le' m) (nth 0 le' n) /\ continuity_2d_pt (fun u v => Derive_Rn k f m (fun i => if ssrnat.eqn i m then u else if ssrnat.eqn i n then v else nth 0 le' i)) (nth 0 le' m) (nth 0 le' n) | Continuous n f => continuity_pt (fun x => interp (set_nth R0 l n x) f) (nth R0 l n) | Continuous2 m n f => continuity_2d_pt (fun x y => interp (set_nth R0 (set_nth R0 l n y) m x) f) (nth R0 l m) (nth R0 l n) | Integrable f e1 e2 => ex_RInt (fun x => interp (x :: l) f) (interp l e1) (interp l e2) | ParamIntegrable n f e1 e2 => locally (nth R0 l n) (fun y => ex_RInt (fun t => interp (t :: set_nth R0 l n y) f) (interp l e1) (interp l e2)) | LocallyParamIntegrable n f e => let a := interp l e in exists eps : posreal, locally (nth R0 l n) (fun y => ex_RInt (fun t => interp (t :: set_nth R0 l n y) f) (a - eps) (a + eps)) | And ld => foldr (fun d acc => interp_domain l d /\ acc) True ld | Forall e1 e2 s => let a1 := interp l e1 in let a2 := interp l e2 in forall t, Rmin a1 a2 <= t <= Rmax a1 a2 -> interp_domain (t :: l) s | Forone e s => interp_domain (interp l e :: l) s | Locally n s => locally (nth R0 l n) (fun x => interp_domain (set_nth R0 l n x) s) | Locally2 m n s => locally_2d (fun x y => interp_domain (set_nth R0 (set_nth R0 l n y) m x) s) (nth R0 l m) (nth R0 l n) | ForallWide n e1 e2 s => let a1 := interp l e1 in let a2 := interp l e2 in exists d : posreal, forall t u, Rmin a1 a2 - d < t < Rmax a1 a2 + d -> Rabs (u - nth R0 l n) < d -> interp_domain (t :: set_nth R0 l n u) s end.
Fixpoint is_const (e : expr) n : bool := match e with | Var v => negb (ssrnat.eqn v n) | AppExt k f le => foldr (fun v acc => andb (is_const v n) acc) true le | AppExtD k f p le => false | App f e => andb (is_const f (S n)) (is_const e n) | Subst f e => andb (orb (ssrnat.eqn n 0) (is_const f n)) (is_const e n) | Cst _ => true | Binary b e1 e2 => andb (is_const e1 n) (is_const e2 n) | Unary u e => is_const e n | Int f e1 e2 => andb (is_const f (S n)) (andb (is_const e1 n) (is_const e2 n)) end.
Definition index_not_const l n := filter (fun v => ~~ is_const (nth (Cst 0) l v) n) (iota 0 (size l)).
Canonical ssrnat.nat_eqType.
Fixpoint D (e : expr) n {struct e} : expr * domain := match e with | Var v => (if ssrnat.eqn v n then Cst 1 else Cst 0, Always) | Cst _ => (Cst 0, Always) | AppExt k f le => let lnc := index_not_const le n in let ld := map (fun e => D e n) le in match lnc with | nil => (Cst 0, Always) | v :: nil => let '(d1,d2) := nth (Cst 0,Never) ld v in (Binary Emult d1 (AppExtD k f v le), And (Derivable v k f le :: d2 :: nil)) | v1 :: v2 :: nil => let '(d1,d2) := nth (Cst 0,Never) ld v1 in let '(d3,d4) := nth (Cst 0,Never) ld v2 in (Binary Eplus (Binary Emult d1 (AppExtD k f v1 le)) (Binary Emult d3 (AppExtD k f v2 le)), And (Derivable2 v1 v2 k f le :: d2 :: Derivable v2 k f le :: d4 :: nil)) | _ => (Cst 0, Never) end | AppExtD k f v le => (Cst 0, Never) | App f e => (Cst 0, Never) | Subst f e => (Cst 0, Never) | Binary b e1 e2 => let '(a1,b1) := D e1 n in let '(a2,b2) := D e2 n in match b, is_const e1 n, is_const e2 n with | Eplus, true, _ => (a2, b2) | Eplus, _, true => (a1, b1) | Eplus, _, _ => (Binary Eplus a1 a2, And (b1::b2::nil)) | Emult, true, _ => (Binary Emult e1 a2, b2) | Emult, _, true => (Binary Emult a1 e2, b1) | Emult, _, _ => (Binary Eplus (Binary Emult a1 e2) (Binary Emult e1 a2), And (b1::b2::nil)) end | Unary u e => let '(a,b) := D e n in match u with | Eopp => (Unary Eopp a, b) | Einv => (Binary Emult (Unary Eopp a) (Unary Einv (Binary Emult e e)), And (b:: (Partial (fun x => x <> 0) e) :: nil)) | Efct f f' H => (Binary Emult a (AppExt 1 f' [:: e]), b) | Efct' f f' df H => (Binary Emult a (AppExt 1 f' [:: e]), And (b :: (Partial df e) :: nil)) end | Int f e1 e2 => let '(a1,b1) := D e1 n in let '(a2,b2) := D e2 n in let '(a3,b3) := D f (S n) in match is_const f (S n), is_const e1 n, is_const e2 n with | true, true, _ => (Binary Emult a2 (App f e2), And (b2::(Integrable f e1 e2)::(Forone e2 (Locally 0 (Continuous 0 f)))::nil)) | true, false, true => (Unary Eopp (Binary Emult a1 (App f e1)), And (b1::(Integrable f e1 e2)::(Forone e1 (Locally 0 (Continuous 0 f)))::nil)) | true, false, false => (Binary Eplus (Binary Emult a2 (App f e2)) (Unary Eopp (Binary Emult a1 (App f e1))), And (b1::b2::(Integrable f e1 e2)::(Forone e1 (Locally 0 (Continuous 0 f)))::(Forone e2 (Locally 0 (Continuous 0 f)))::nil)) | false, true, true => (Int a3 e1 e2, And ((ForallWide n e1 e2 b3)::(Locally n (Integrable f e1 e2)):: (Forall e1 e2 (Continuous2 (S n) 0 a3))::nil)) | false, false, true => (Binary Eplus (Unary Eopp (Binary Emult a1 (App f e1))) (Int a3 e1 e2), And ((Forone e1 (Locally2 (S n) 0 (Continuous2 (S n) 0 a3))):: (Forall e1 e2 (Continuous2 (S n) 0 a3)):: b1::(Forone e1 (Locally 0 (Continuous 0 f))):: ParamIntegrable n f e1 e2::LocallyParamIntegrable n f e1:: ForallWide n e1 e2 b3::nil)) | false, true, false => (Binary Eplus (Binary Emult a2 (App f e2)) (Int a3 e1 e2), And ((Forone e2 (Locally2 (S n) 0 (Continuous2 (S n) 0 a3))):: (Forall e1 e2 (Continuous2 (S n) 0 a3)):: b2::(Forone e2 (Locally 0 (Continuous 0 f))):: ParamIntegrable n f e1 e2::LocallyParamIntegrable n f e2:: ForallWide n e1 e2 b3::nil)) | false, false, false => (Binary Eplus (Binary Eplus (Binary Emult a2 (App f e2)) (Unary Eopp (Binary Emult a1 (App f e1)))) (Int a3 e1 e2), And ((Forone e1 (Locally2 (S n) 0 (Continuous2 (S n) 0 a3))):: (Forone e2 (Locally2 (S n) 0 (Continuous2 (S n) 0 a3))):: (Forall e1 e2 (Continuous2 (S n) 0 a3)):: b1::(Forone e1 (Locally 0 (Continuous 0 f))):: b2::(Forone e2 (Locally 0 (Continuous 0 f))):: ParamIntegrable n f e1 e2::LocallyParamIntegrable n f e1::LocallyParamIntegrable n f e2:: ForallWide n e1 e2 b3::nil)) end end.
Fixpoint simplify_domain (d : domain) : domain := match d with | And ld => let l := foldr (fun d acc => let d' := simplify_domain d in match d' with | Always => acc | And l => cat l acc | Never => Never :: nil | _ => d' :: acc end) nil ld in match l with | nil => Always | d :: nil => d | _ => And l end | Forall e1 e2 d => let d' := simplify_domain d in match d' with | Always => Always | Never => Never | _ => Forall e1 e2 d' end | Forone e d => let d' := simplify_domain d in match d' with | Always => Always | Never => Never | _ => Forone e d' end | Locally n d => let d' := simplify_domain d in match d' with | Always => Always | Never => Never | _ => Locally n d' end | Locally2 m n d => let d' := simplify_domain d in match d' with | Always => Always | Never => Never | _ => Locally2 m n d' end | ForallWide n e1 e2 d => let d' := simplify_domain d in match d' with | Always => Always | Never => Never | _ => ForallWide n e1 e2 d' end | _ => d end.
Class UnaryDiff f := {UnaryDiff_f' : R -> R ; UnaryDiff_H : forall x, is_derive f x (UnaryDiff_f' x)}.
Class UnaryDiff' f := {UnaryDiff'_f' : R -> R ; UnaryDiff'_df : R -> Prop ; UnaryDiff'_H : forall x, UnaryDiff'_df x -> is_derive f x (UnaryDiff'_f' x)}.
Global Instance UnaryDiff_exp : UnaryDiff exp.
Proof.
exists exp.
move => x ; by apply is_derive_Reals, derivable_pt_lim_exp.
Defined.
Global Instance UnaryDiff_pow : forall n : nat, UnaryDiff (fun x => pow x n).
Proof.
intro n.
exists (fun x => INR n * x ^ (Peano.pred n)).
move => x ; by apply is_derive_Reals, derivable_pt_lim_pow.
Defined.
Global Instance UnaryDiff_Rabs : UnaryDiff' Rabs.
Proof.
exists (fun x => sign x) (fun x => x <> 0).
move => x Hx0 ; by apply filterdiff_Rabs.
Defined.
Global Instance UnaryDiff_Rsqr : UnaryDiff Rsqr.
Proof.
exists (fun x => 2 * x).
move => x ; by apply is_derive_Reals, derivable_pt_lim_Rsqr.
Defined.
Global Instance UnaryDiff_cosh : UnaryDiff cosh.
Proof.
exists sinh.
move => x ; by apply is_derive_Reals, derivable_pt_lim_cosh.
Defined.
Global Instance UnaryDiff_sinh : UnaryDiff sinh.
Proof.
exists (fun x => cosh x).
move => x ; by apply is_derive_Reals, derivable_pt_lim_sinh.
Defined.
Global Instance UnaryDiff_ps_atan : UnaryDiff' ps_atan.
Proof.
exists (fun x => /(1+x^2)) (fun x => -1 < x < 1).
move => x Hx ; by apply is_derive_Reals, derivable_pt_lim_ps_atan.
Defined.
Global Instance UnaryDiff_atan : UnaryDiff atan.
Proof.
exists (fun x => /(1+x^2)).
move => x ; by apply is_derive_Reals, derivable_pt_lim_atan.
Defined.
Global Instance UnaryDiff_ln : UnaryDiff' ln.
Proof.
exists (fun x => /x) (fun x => 0 < x).
move => x Hx ; by apply is_derive_Reals, derivable_pt_lim_ln.
Defined.
Global Instance UnaryDiff_cos : UnaryDiff cos.
Proof.
exists (fun x => - sin x ).
move => x ; by apply is_derive_Reals, derivable_pt_lim_cos.
Defined.
Global Instance UnaryDiff_sin : UnaryDiff sin.
Proof.
exists cos.
move => x ; by apply is_derive_Reals, derivable_pt_lim_sin.
Defined.
Global Instance UnaryDiff_sqrt : UnaryDiff' sqrt.
Proof.
exists (fun x => / (2 * sqrt x)) (fun x => 0 < x).
move => x Hx ; by apply is_derive_Reals, derivable_pt_lim_sqrt.
Defined.
Definition var : nat -> R.
exact (fun _ => R0).
Ltac reify_helper a b z d := match a with | Cst _ => match b with | Cst _ => constr:(Cst d) | _ => z end | _ => z end.
Ltac reify fct nb := let rec reify_aux fct l i := match fct with | ?f ?a => let e := reify a nb in reify_aux f (e :: l) (S i) | _ => constr:((fct, rev l, i)) end in match fct with | var ?i => eval vm_compute in (Var (nb - i)) | Rplus ?a ?b => let a' := reify a nb in let b' := reify b nb in reify_helper a' b' (Binary Eplus a' b') fct | Ropp ?a => let a' := reify a nb in match a' with | Cst _ => constr:(Cst fct) | _ => constr:(Unary Eopp a') end | Rminus ?a ?b => let a' := reify a nb in let b' := reify b nb in reify_helper a' b' (Binary Eplus a' (Unary Eopp b')) fct | Rmult ?a ?b => let a' := reify a nb in let b' := reify b nb in reify_helper a' b' (Binary Emult a' b') fct | Rinv ?a => let a' := reify a nb in match a' with | Cst _ => constr:(Cst fct) | _ => constr:(Unary Einv a') end | Rdiv ?a ?b => let a' := reify a nb in let b' := reify b nb in reify_helper a' b' (Binary Emult a' (Unary Einv b')) fct | RInt ?f ?a ?b => let f := eval cbv beta in (f (var (S nb))) in let f' := reify f (S nb) in let a' := reify a nb in let b' := reify b nb in constr:(Int f' a' b') | pow ?f ?n => reify ((fun x => pow x n) f) nb | context [var ?i] => match fct with | ?f ?a => let e := reify a nb in let ud := constr:(_ : UnaryDiff f) in constr:(Unary (Efct f (@UnaryDiff_f' f ud) (@UnaryDiff_H f ud)) e) | ?f ?a => let e := reify a nb in let ud := constr:(_ : UnaryDiff' f) in constr:(Unary (Efct' f (@UnaryDiff'_f' f ud) (@UnaryDiff'_df f ud) (@UnaryDiff'_H f ud)) e) | _ => match reify_aux fct (Nil expr) O with | (?f,?le,?k) => constr:(AppExt k f le) end end | _ => constr:(Cst fct) end.
Ltac auto_derive_fun f := let f := eval cbv beta in (f (var O)) in let e := reify f O in let H := fresh "H" in assert (H := fun x => auto_derive_helper e (x :: nil) 0) ; simpl in H ; unfold Derive_Rn, ex_derive_Rn in H ; simpl in H ; revert H.
Ltac auto_derive := match goal with | |- is_derive ?f ?v ?l => auto_derive_fun f ; let H := fresh "H" in intro H ; refine (@eq_ind R _ (is_derive f v) (H v _) l _) ; clear H | |- ex_derive ?f ?v => eexists ; auto_derive_fun f ; let H := fresh "H" in intro H ; apply (H v) ; clear H | |- derivable_pt_lim ?f ?v ?l => apply is_derive_Reals ; auto_derive | |- derivable_pt ?f ?v => apply ex_derive_Reals_0 ; auto_derive end.

Lemma interp_set_nth : forall n l e, interp (set_nth 0 l n (nth 0 l n)) e = interp l e.
Proof.
intros n l e.
apply interp_ext.
intros k.
rewrite nth_set_nth /=.
case ssrnat.eqnP.
intros H.
now apply f_equal.
easy.
