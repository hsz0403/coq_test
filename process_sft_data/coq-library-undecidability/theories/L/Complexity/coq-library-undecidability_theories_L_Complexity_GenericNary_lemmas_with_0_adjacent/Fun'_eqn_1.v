Require Import Coq.Lists.List.
Import List.ListNotations.
From smpl Require Import Smpl.
Local Set Universe Polymorphism.
Fixpoint Rarrow (domain : list Type) (range : Type) : Type := match domain with | nil => range | d :: ds => Rarrow ds (d -> range) end.
Fixpoint Rtuple (domain : list Type) : Type := match domain with | nil => unit | d :: nil => d | d :: ds => prod (Rtuple ds) d end.
Fixpoint Const {A : Type} (domain : list Type) (c : A) : Rarrow domain A := match domain with | nil => c | d :: ds => Const ds (fun _ => c) end.
Hint Rewrite Const_eqn_1 : Const.
Hint Rewrite Const_eqn_2 : Const.
Opaque Const.
Fixpoint Fun' {domain : list Type} {range : Type} {struct domain} : (Rtuple domain -> range) -> (Rtuple domain) -> range := match domain with | nil => fun body t => body tt | d :: ds => let f := @Fun' ds range in match ds return ((Rtuple ds -> range) -> Rtuple ds -> range) -> ((Rtuple (d :: ds) -> range) -> Rtuple (d :: ds) -> range) with | [] => fun _ body t => body t | _ => fun f body t => let '(t', x) := t in f (fun p' => body (p', x)) t' end f end.
Hint Rewrite Fun'_eqn_1 : Fun'.
Hint Rewrite Fun'_eqn_2 : Fun'.
Hint Rewrite Fun'_eqn_3 : Fun'.
Opaque Fun'.
Fixpoint App {domain : list Type} {range : Type} {struct domain} : (Rarrow domain range) -> Rtuple domain -> range := match domain with | nil => fun f x => f | d :: ds => let Apprec := @App ds (d -> range) in match ds return ((Rarrow ds (d -> range)) -> Rtuple ds -> d -> range) -> (Rarrow (d :: ds) range) -> Rtuple (d :: ds) -> range with | [] => fun _ f x => f x | _ => fun Apprec f t => Apprec f (fst t) (snd t) end Apprec end.
Hint Rewrite App_eqn_1 : App.
Hint Rewrite App_eqn_2 : App.
Hint Rewrite App_eqn_3 : App.
Opaque App.
Set Printing Universes.
Tactic Notation "_rewrite_anywhere" uconstr(L):= match goal with | H : _ |- _ => setoid_rewrite L in H | _ => setoid_rewrite L end.
Smpl Create generic.
Smpl Add 2 _rewrite_anywhere Fun'_simpl : generic.
Smpl Add 2 _rewrite_anywhere App_Const_simpl : generic.
Definition Const' (domain : list Type) {range : Type} (cst : range) : Rtuple domain -> range := Fun' (App (Const domain cst)).
Hint Unfold Const' : generic.
Definition Uncurry {domain : list Type} {range : Type} (f : Rarrow domain range) : Rtuple domain -> range := Fun' (App f).
Hint Unfold Uncurry : generic.
Smpl Create nary_prepare.
Ltac rew_generic_in_all := autounfold with generic in *;repeat smpl nary_prepare;repeat smpl generic.
Tactic Notation "prove_nary" uconstr(L) := intros; rew_generic_in_all; eapply L; eauto.
Inductive Domain_goal_hint (G : Type) := Mk_domain_goal_hint : Domain_goal_hint G.
Record Domain_of_goal := Mk_domain_of_goal { Domain_of_goal_domain_ty : Type ; Domain_of_goal_domain : Domain_of_goal_domain_ty ; }.
Arguments Mk_domain_of_goal [Domain_of_goal_domain_ty].
Ltac mk_domain_getter tac := match goal with | H : Domain_goal_hint ?G |- Domain_of_goal => tac G end.
Ltac get_domain := match goal with |- ?G => let packed_dom := constr:(ltac:( pose proof (Mk_domain_goal_hint G); typeclasses eauto with domain_of_goal ) : Domain_of_goal) in let dom := constr:(Domain_of_goal_domain packed_dom) in let dom := eval cbv in dom in dom end.
Ltac simpl_apply app t := let H := fresh in pose proof t as H; autounfold with generic in H; cbn in H; app H; clear H.
Ltac _nary_apply t L := let D := get_domain in simpl_apply t (L D).
Tactic Notation "nary" "apply" uconstr(L) := _nary_apply ltac:(fun t => apply t) L.
Tactic Notation "nary" "simple" "apply" uconstr(L) := _nary_apply ltac:(fun t => simple apply t) L.
Ltac list_of_tuple ty := lazymatch ty with | prod ?A ?B => let l := list_of_tuple A in constr:(cons (B:Set) l) | _ => constr:(cons (ty:Set) nil) end.

Lemma Fun'_eqn_1 : forall range body, @Fun' [] range body = (fun _ => body tt).
Proof.
intros.
reflexivity.
