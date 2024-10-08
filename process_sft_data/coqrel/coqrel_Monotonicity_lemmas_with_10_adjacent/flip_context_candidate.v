Require Export RelDefinitions.
Require Export RelOperators.
Require Export Relators.
Require Import Delay.
Class QueryParams {A B} (m1: A) (m2: B) (n: nat).
Ltac count_unapplied_params m := let rec count t := lazymatch t with | forall x, ?t' => let n := count t' in constr:(S n) | _ => constr:(O) end in let t := type of m in let t := eval cbv in t in count t.
Ltac query_params m1 m2 := let rec head t := lazymatch t with ?t' _ => head t' | _ => t end in let h1 := head m1 in let p1 := count_unapplied_params m1 in let h2 := head m2 in let p2 := count_unapplied_params m2 in first [ not_evar h1; not_evar h2; eapply (query_params_both h1 h2 p1 p2) | not_evar h1; is_evar h2; eapply (query_params_one h1 p1) | is_evar h1; not_evar h2; eapply (query_params_one h2 p2) ].
Hint Extern 10 (QueryParams ?m1 ?m2 _) => query_params m1 m2 : typeclass_instances.
Ltac pass_evar_to k := let Av := fresh "A" in evar (Av : Type); let A := eval red in Av in clear Av; let av := fresh "a" in evar (av : A); let a := eval red in av in clear av; k a.
Class RemoveParams {A B C D} (n: nat) (m1: A) (m2: B) (f: C) (g: D).
Ltac remove_params_from n m k := lazymatch n with | O => k m | S ?n' => lazymatch m with | ?m' _ => remove_params_from n' m' k | _ => is_evar m; pass_evar_to k end end.
Ltac remove_params n m1 m2 f g := remove_params_from n m1 ltac:(fun m1' => unify f m1'; remove_params_from n m2 ltac:(fun m2' => unify g m2')).
Hint Extern 1 (RemoveParams ?n ?m1 ?m2 ?f ?g) => remove_params n m1 m2 f g; constructor : typeclass_instances.
Class RemoveAllParams {A B C D} (m1: A) (m2: B) (f: C) (g: D).
Ltac remove_all_params_from m k := lazymatch m with | ?m' _ => remove_all_params_from m' k | _ => not_evar m; k m end.
Ltac remove_all_params m1 m2 f g := first [ is_evar m2; remove_all_params_from m1 ltac:(fun m1' => unify f m1'; pass_evar_to ltac:(fun m2' => unify g m2')) | is_evar m1; remove_all_params_from m2 ltac:(fun m2' => unify g m2'; pass_evar_to ltac:(fun m1' => unify f m1')) | lazymatch m1 with ?m1' _ => lazymatch m2 with ?m2' _ => remove_all_params m1' m2' f g end end | not_evar m1; unify f m1; not_evar m2; unify g m2 ].
Hint Extern 1 (RemoveAllParams ?m1 ?m2 ?f ?g) => remove_all_params m1 m2 f g; constructor : typeclass_instances.
Class CandidateProperty {A B} (R': rel A B) f g (Q: Prop) := candidate_related: R' f g.
Instance as_is_candidate {A B} (R R': rel A B) m1 m2: Related m1 m2 R' -> CandidateProperty R' m1 m2 (R m1 m2) | 10.
Proof.
firstorder.
Instance remove_params_candidate {A B C D} R (m1: A) (m2: B) R' (f: C) (g: D) n: QueryParams m1 m2 n -> RemoveParams n m1 m2 f g -> Related f g R' -> CandidateProperty R' f g (R m1 m2) | 20.
Proof.
firstorder.
Instance remove_all_params_candidate {A B C D} R (m1:A) (m2:B) R' (f:C) (g:D): RemoveAllParams m1 m2 f g -> Related f g R' -> CandidateProperty R' f g (R m1 m2) | 30.
Proof.
firstorder.
Ltac context_candidate := let rec is_prefix f m := first [ unify f m | lazymatch m with ?n _ => is_prefix f n end ] in let rec is_prefixable f m := first [ is_evar f | is_evar m | unify f m | lazymatch m with ?n _ => is_prefixable f n end ] in multimatch goal with | H: _ ?f ?g |- @CandidateProperty ?A ?B ?R ?x ?y (_ ?m ?n) => red; once first [ is_prefix f m; is_prefixable g n | is_prefix g n; is_prefixable f m | is_prefix g m; is_prefixable f n; apply flip_context_candidate | is_prefix f n; is_prefixable g m; apply flip_context_candidate ]; eexact H end.
Hint Extern 1 (CandidateProperty _ _ _ _) => context_candidate : typeclass_instances.
Class RImpl (P Q: Prop): Prop := rimpl: P -> Q.
Global Instance rimpl_refl {A B} (R : rel A B) m n: RImpl (R m n) (R m n).
Proof.
firstorder.
Global Instance rimpl_subrel {A B} (R R': rel A B) m n: NonDelayed (RAuto (subrel R R')) -> RImpl (R m n) (R' m n).
Proof.
firstorder.
Global Instance rimpl_flip_subrel {A B} R R' (x: A) (y: B): NonDelayed (RAuto (subrel R (flip R'))) -> RImpl (R x y) (R' y x) | 2.
Proof.
firstorder.
Class Monotonicity (P Q: Prop): Prop := monotonicity: P -> Q.
Global Instance apply_candidate {A B} (R: rel A B) m n P Q Q': CandidateProperty R m n Q -> RElim R m n P Q' -> RImpl Q' Q -> Monotonicity P Q.
Proof.
firstorder.
Ltac monotonicity := lazymatch goal with |- ?Q => apply (monotonicity (Q:=Q)) end; Delay.split_conjunction.
Global Instance monotonicity_rstep {A B} (P: Prop) (R: rel A B) m n: PolarityResolved R -> Monotonicity P (R m n) -> RStep P (R m n) | 50.
Proof.
firstorder.
Class SubrelMonotonicity (P Q: Prop): Prop := subrel_monotonicity: P -> Q.
Global Instance apply_candidate_subrel {A B C D} (R: rel A B) m n P Rc Rg x y: CandidateProperty R m n (Rg x y) -> RElim R m n P (Rc x y) -> SubrelMonotonicity (@subrel C D Rc Rg /\ P) (Rg x y).
Proof.
firstorder.
Ltac subrel_monotonicity := lazymatch goal with |- ?Q => apply (subrel_monotonicity (Q:=Q)) end; Delay.split_conjunction.
Class CommonPrefix {A B C} (m1: A) (m2: B) (f: C).
Ltac common_prefix m1 m2 f := first [ not_evar m1; not_evar m2; unify m1 m2; unify f m1 | lazymatch m1 with ?m1' _ => lazymatch m2 with ?m2' _ => common_prefix m1' m2' f end end | unify m1 m2; unify f m1 ].
Hint Extern 1 (CommonPrefix ?m1 ?m2 ?f) => common_prefix m1 m2 f; constructor : typeclass_instances.
Global Instance eq_candidate {A B C} R (m1: A) (m2: B) (f: C): CommonPrefix m1 m2 f -> CandidateProperty eq f f (R m1 m2) | 100.
Proof.
firstorder.

Lemma query_params_one {A B C} (h: A) p (m1: B) (m2: C) n: Params h (p + n) -> QueryParams m1 m2 n.
Proof.
Admitted.

Lemma query_params_both {A B C D} (h1: A) (h2: B) p1 p2 (m1: C) (m2: D) n: Params h1 (p1 + n) -> Params h2 (p2 + n) -> QueryParams m1 m2 n.
Proof.
Admitted.

Instance as_is_candidate {A B} (R R': rel A B) m1 m2: Related m1 m2 R' -> CandidateProperty R' m1 m2 (R m1 m2) | 10.
Proof.
Admitted.

Instance remove_params_candidate {A B C D} R (m1: A) (m2: B) R' (f: C) (g: D) n: QueryParams m1 m2 n -> RemoveParams n m1 m2 f g -> Related f g R' -> CandidateProperty R' f g (R m1 m2) | 20.
Proof.
Admitted.

Instance remove_all_params_candidate {A B C D} R (m1:A) (m2:B) R' (f:C) (g:D): RemoveAllParams m1 m2 f g -> Related f g R' -> CandidateProperty R' f g (R m1 m2) | 30.
Proof.
Admitted.

Lemma f_equal_relim {A B} f g m n P Q: RElim eq (f m) (g n) P Q -> RElim (@eq (A -> B)) f g (m = n /\ P) Q.
Proof.
intros Helim Hf [Hmn HP].
apply Helim; eauto.
Admitted.

Lemma flip_context_candidate {A B} (R: rel A B) x y : R y x -> flip R x y.
Proof.
firstorder.
