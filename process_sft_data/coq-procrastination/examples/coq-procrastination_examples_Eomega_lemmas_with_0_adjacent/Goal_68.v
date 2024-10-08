Require Import Omega.
Require Import Arith.
Ltac For n t := match n with 0 => idtac | S ?n' => (For n' t || t n') end.
Ltac For_inf n t := t n || let n' := (eval compute in (1 + n)) in For_inf n' t.
Ltac forcenat n := match type of n with nat => n | N => eval compute in (N.to_nat n) | Z => eval compute in (Z.to_nat n) end.
Ltac explus n := let z := eval compute in (Z.of_nat n) in exists z.
Ltac exminus n := let z := eval compute in (Z.opp (Z.of_nat n)) in exists z.
Ltac match_exists_on_type ty t := lazymatch goal with | |- @ex ty ?P => t P | |- @sig ty ?P => t P | |- @sigT ty ?P => t P (* the following are commented out because they give out a collision warning *) (* | |- @ex2 ty (fun x => ?P) (fun x => ?Q) => let PQ := constr:(fun x : ty => P /\ Q) in t PQ | |- @sig2 ty (fun x => ?P) (fun x => ?Q) => let PQ := constr:(fun x : ty => P /\ Q) in t PQ | |- @sigT2 ty (fun x => ?P) (fun x => ?Q) => let PQ := constr:(fun x : ty => P /\ Q) in t PQ *) | |- @ex2 ty ?P ?Q => let PQ := constr:(fun x => P x /\ Q x) in t PQ | |- @sig2 ty ?P ?Q => let PQ := constr:(fun x => P x /\ Q x) in t PQ | |- @sigT2 ty ?P ?Q => let PQ := constr:(fun x => P x /\ Q x) in t PQ end.
Ltac if_exists_on_type ty t := match_exists_on_type ty ltac:(fun _ => t).
Ltac iter_cube_new t n := let n := forcenat n in (* if existential is nat *) (if_exists_on_type nat ltac:(For n ltac:(fun i => exists i; iter_cube_new t n))) || (* if existential is Z *) (if_exists_on_type Z ltac:(For n ltac:(fun i => (explus i; iter_cube_new t n) || (exminus i; iter_cube_new t n)))) (* otherwise *) || t.
Ltac iter_cube t n := let n := forcenat n in lazymatch goal with | |- @ex nat _ => For n ltac:(fun i => exists i; iter_cube t n) | |- @sig nat _ => For n ltac:(fun i => exists i; iter_cube t n) | |- @sigT nat _ => For n ltac:(fun i => exists i; iter_cube t n) | |- @ex2 nat _ _ => For n ltac:(fun i => exists i; iter_cube t n) | |- @sig2 nat _ _ => For n ltac:(fun i => exists i; iter_cube t n) | |- @sigT2 nat _ _ => For n ltac:(fun i => exists i; iter_cube t n) | |- @ex Z _ => For n ltac:(fun i => (explus i; iter_cube t n) || (exminus i; iter_cube t n)) | |- @sig Z _ => For n ltac:(fun i => (explus i; iter_cube t n) || (exminus i; iter_cube t n)) | |- @sigT Z _ => For n ltac:(fun i => (explus i; iter_cube t n) || (exminus i; iter_cube t n)) | |- @ex2 Z _ _ => For n ltac:(fun i => (explus i; iter_cube t n) || (exminus i; iter_cube t n)) | |- @sig2 Z _ _ => For n ltac:(fun i => (explus i; iter_cube t n) || (exminus i; iter_cube t n)) | |- @sigT2 Z _ _ => For n ltac:(fun i => (explus i; iter_cube t n) || (exminus i; iter_cube t n)) | |- _ => t end.
Ltac iter_cone t n := lazymatch goal with | |- @ex nat _ => For n ltac:(fun i => exists i; let n' := eval compute in (n - i) in iter_cone t n') | |- @sig nat _ => For n ltac:(fun i => exists i; let n' := eval compute in (n - i) in iter_cone t n') | |- @sigT nat _ => For n ltac:(fun i => exists i; let n' := eval compute in (n - i) in iter_cone t n') | |- @ex Z _ => fail "Bounded sum exploration not yet implemented for Z" | |- @sig Z _ => fail "Bounded sum exploration not yet implemented for Z" | |- @sigT Z _ => fail "Bounded sum exploration not yet implemented for Z" | |- _ => t end.
Ltac iter_plane t n := let Sn := (eval compute in (1 + n)) in lazymatch goal with | |- @ex nat _ => For Sn ltac:(fun i => exists i; let n' := eval compute in (n - i) in iter_plane t n') | |- @sig nat _ => For Sn ltac:(fun i => exists i; let n' := eval compute in (n - i) in iter_plane t n') | |- @sigT nat _ => For Sn ltac:(fun i => exists i; let n' := eval compute in (n - i) in iter_plane t n') | |- @ex Z _ => fail "Constant-sum exploration not yet implemented for Z" | |- @sig Z _ => fail "Constant-sum exploration not yet implemented for Z" | |- @sigT Z _ => fail "Constant-sum exploration not yet implemented for Z" | |- _ => match n with 0 => t | _ => fail end end.
Tactic Notation "iter_planes" tactic(t) := For_inf 0 ltac:(iter_plane t).
Tactic Notation "iter_planes" tactic(t) constr(n) := For n ltac:(iter_plane t).
Tactic Notation "iter_cubes" tactic(t) constr(n) := For n ltac:(iter_cube t).
Tactic Notation "iter_cubes" tactic(t) := For_inf 1 ltac:(iter_cube t).
Tactic Notation "eomega" := iter_cubes omega.
Tactic Notation "eomega" constr(n) := let n := forcenat n in let n' := (eval compute in (1 + n)) in iter_cube omega n'.
Tactic Notation "eomega" "sum" := iter_planes omega.
Tactic Notation "eomega" "sum" constr(n) := let n := forcenat n in let n' := (eval compute in (1 + n)) in iter_cone omega n'.
Section Tests.
Goal exists a b, a = 5 /\ b = 5.
Proof.
Fail Fail eomega.
Fail eomega 4.
Fail Fail eomega 5.
Fail Fail eomega sum.
Fail eomega sum 9.
Fail Fail eomega sum 10.
eomega.
Goal 15 = 15.
Proof.
eomega.
Goal exists n, n = 0.
Proof.
Fail Fail iter_plane omega 0.
Fail iter_plane omega 1.
Fail iter_plane omega 2.
Fail Fail iter_planes omega.
eomega.
Goal exists n, n = 15.
Proof.
eomega.
Goal { n | n = 15 }.
Proof.
eomega.
Goal { n : nat & n = 15 }.
Proof.
eomega.
Goal exists2 x, x * x + 2 = 3 * x & x <> 1.
Proof.
eomega.
Goal { x | x * x + 2 = 3 * x & x <> 1 }.
Proof.
eomega.
Goal { x : nat & x * x + 2 = 3 * x & x <> 1 }.
Proof.
eomega.
Goal exists a b c, a = 5 /\ b = 6 /\ c = 4 /\ a + c + b = b + a + c.
Proof.
eomega.
Goal exists x y, 3 * x * y = 12.
Proof.
eomega.
Goal exists x2 x3 x4 : nat, 0 <= x2 /\ 1 <= x4 /\ x4 <= x3 /\ S (S x4) <= x3 /\ 2 <= x2.
Proof.
eomega.
Goal forall x2 x3 x4 : nat, (0 <= x2 /\ 1 <= x4 /\ x4 <= x3 /\ S (S x4) <= x3 /\ 2 <= x2) -> x2 <= 2 -> x3 <= 2 -> x4 <= 2 -> False.
Proof.
intros.
omega.
Goal exists a b, forall x, 6 * x + x + x = a * x + b.
Time iter_planes ltac:(intros; ring).
Open Scope Z_scope.
Goal exists x1 x2 : Z, x1 = - 5 /\ x2 = 5.
Proof.
eomega.
Goal exists x1 x2 : Z, x1 * x2 = 15 /\ x1 < 0 /\ x2 < 0.
Proof.
eomega.
Goal exists x1 x2 : Z, 0 <= x1 /\ 0 <= x1 + x2 /\ 1 <= x1 + x2 /\ x2 + 1 <= 0.
Proof.
eomega.
Goal exists x1 x2 x3 x4 : Z, x1 * x2 * x3 * x4 = 16 /\ x1 * x2 < 0 /\ x3 * x4 < 0.
Proof.
eomega.
Goal exists x1 x2 : Z, x1 * x2 = - 16 /\ 0 < x1 < 5 /\ -5 < x2 < 0.
Proof.
eomega 5.
Goal exists x1 x2 : Z, x1 * x2 = - 16 /\ 0 < x1 < 5 /\ -5 < x2 < 0.
Proof.
Fail eomega sum 8.
Fail eomega 3.
eomega 4.
Goal exists x, x * x * x = - 27.
Proof.
eomega.
Goal exists n : nat, exists z : Z, Z.pow z (Z.of_nat n) = - 27.
Proof.
Fail eomega 4.
iter_cubes reflexivity.
Definition fifth_root : { x | x * x * x * x * x = 69343957 }.
Proof.
Time Fail Fail iter_cubes reflexivity.
eomega.
Defined.
Print fifth_root.
Goal { x | x * x * x * x = 81 }%nat.
Proof.
Fail eomega 2.
eomega 3.
Goal { x | x * x * x = 81 }%nat.
Proof.
Fail eomega 100.
Abort.
End Tests.

Goal exists a b c, a = 5 /\ b = 6 /\ c = 4 /\ a + c + b = b + a + c.
Proof.
eomega.
