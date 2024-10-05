From Undecidability.Shared.Libs.DLW.Utils Require Import utils.
Set Implicit Arguments.
Set Default Proof Using "Type".
Reserved Notation " e '⇢' x " (at level 58).
Reserved Notation " e [ v / x ] " (at level 57, v at level 0, x at level 0, left associativity, format "e [ v / x ]").
Reserved Notation " e ⦃ x '⇠' v ⦄ " (at level 57, v at level 0, x at level 0, left associativity).
Section env.
Variable (X Y : Type) (X_eq_dec : eqdec X) (Y_default : Y).
Definition env := X -> Y.
Implicit Type e : env.
Definition get_env e x := e x.
Definition set_env e x v : env := fun y => if X_eq_dec x y then v else e y.
Definition nil_env : env := fun _ => Y_default.
Fact get_set_env_eq e v p q : p = q -> get_env (set_env e p v) q = v.
Proof.
intros []; unfold set_env, get_env; destruct (X_eq_dec p p) as [ | [] ]; auto.
Fact get_set_env_neq e v p q : p <> q -> get_env (set_env e p v) q = get_env e q.
Proof.
simpl; intros H; unfold set_env, get_env; destruct (X_eq_dec p q); auto; destruct H; auto.
End env.
Arguments nil_env {X}.
Opaque get_env.
Opaque set_env.
Local Notation " e ⇢ x " := (@get_env _ _ e x).
Local Notation " e ⦃ x ⇠ v ⦄ " := (@set_env _ _ _ e x v).
Ltac find_val x t := match t with | ?s⦃x⇠?v⦄ => v | ?s⦃_⇠_⦄ => find_val x s end.
Tactic Notation "rew" "env" := repeat once lazymatch goal with | |- context[ _⦃ ?x⇠_⦄⇢?x ] => rewrite get_set_env_eq with (1 := eq_refl x) | _ : ?x = ?y |- context[ _⦃ ?x⇠_⦄⇢?y ] => rewrite get_set_env_eq with (p := x) (q := y) | _ : ?y = ?x |- context[ _⦃ ?x⇠_⦄⇢?y ] => rewrite get_set_env_eq with (p := x) (q := y) | _ : ?x <> ?y |- context[ _⦃ ?x⇠_⦄⇢?y ] => rewrite get_set_env_neq with (p := x) (q := y) | _ : ?y <> ?x |- context[ _⦃ ?x⇠_⦄⇢?y ] => rewrite get_set_env_neq with (p := x) (q := y) | |- context[ _⦃ ?x⇠_⦄⇢?y ] => rewrite get_set_env_neq with (p := x) (q := y); [ | discriminate ] end; auto.
Tactic Notation "rew" "env" "in" hyp(H) := revert H; rew env; intros H.

Fact get_set_env_eq e v p q : p = q -> get_env (set_env e p v) q = v.
Proof.
Admitted.

Fact get_set_env_neq e v p q : p <> q -> get_env (set_env e p v) q = get_env e q.
Proof.
simpl; intros H; unfold set_env, get_env; destruct (X_eq_dec p q); auto; destruct H; auto.
