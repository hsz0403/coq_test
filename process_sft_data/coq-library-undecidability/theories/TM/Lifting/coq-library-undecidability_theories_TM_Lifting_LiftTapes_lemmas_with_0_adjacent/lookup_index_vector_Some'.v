From Undecidability Require Import TM.Util.Prelim TM.Util.Relations TM.Util.TM_facts.
Definition select (m n: nat) (X: Type) (I : Vector.t (Fin.t n) m) (V : Vector.t X n) : Vector.t X m := Vector.map (Vector.nth V) I.
Section LiftTapes_Rel.
Variable (sig : finType) (F : Type).
Variable m n : nat.
Variable I : Vector.t (Fin.t n) m.
Definition not_index (i : Fin.t n) : Prop := ~ Vector.In i I.
Variable (R : pRel sig F m).
Definition LiftTapes_select_Rel : pRel sig F n := fun t '(y, t') => R (select I t) (y, select I t').
Definition LiftTapes_eq_Rel : pRel sig F n := ignoreParam (fun t t' => forall i : Fin.t n, not_index i -> t'[@i] = t[@i]).
Definition LiftTapes_Rel := LiftTapes_select_Rel ∩ LiftTapes_eq_Rel.
Variable T : tRel sig m.
Definition LiftTapes_T : tRel sig n := fun t k => T (select I t) k.
End LiftTapes_Rel.
Arguments not_index : simpl never.
Arguments LiftTapes_select_Rel {sig F m n} I R x y /.
Arguments LiftTapes_eq_Rel {sig F m n} I x y /.
Arguments LiftTapes_Rel {sig F m n } I R x y /.
Arguments LiftTapes_T {sig m n} I T x y /.
Section Fill.
Fixpoint lookup_index_vector {m n : nat} (I : Vector.t (Fin.t n) m) : Fin.t n -> option (Fin.t m) := match I with | Vector.nil _ => fun (i : Fin.t n) => None | Vector.cons _ i' m' I' => fun (i : Fin.t n) => if Fin.eqb i i' then Some Fin0 else match lookup_index_vector I' i with | Some j => Some (Fin.FS j) | None => None end end.
Variable X : Type.
Definition fill {m n : nat} (I : Vector.t (Fin.t n) m) (init : Vector.t X n) (V : Vector.t X m) : Vector.t X n := tabulate (fun i => match lookup_index_vector I i with | Some j => V[@j] | None => init[@i] end).
Section Test.
Variable (a b x y z : X).
Goal fill [|Fin0; Fin1|] [|x;y;z|] [|a;b|] = [|a;b;z|].
Proof.
cbn.
reflexivity.
Goal fill [|Fin2; Fin1|] [|x;y;z|] [|a;b|] = [|x;b;a|].
Proof.
cbn.
reflexivity.
Goal fill [|Fin1; Fin0|] [|x;y;z|] [|a;b|] = [|b;a;z|].
Proof.
cbn.
reflexivity.
Goal forall (ss : Vector.t X 3), fill [|Fin0; Fin1|] ss [|a;b|] = [|a;b; ss[@Fin2]|].
Proof.
intros.
cbn.
reflexivity.
End Test.
Variable m n : nat.
Implicit Types (i : Fin.t n) (j : Fin.t m).
Implicit Types (I : Vector.t (Fin.t n) m) (init : Vector.t X n) (V : Vector.t X m).
Definition fill_default I (def : X) V := fill I (Vector.const def n) V.
End Fill.
Section loop_map.
Variable A B : Type.
Variable (f : A -> A) (h : A -> bool) (g : A -> B).
Hypothesis step_map_comp : forall a, g (f a) = g a.
End loop_map.
Section LiftNM.
Variable sig : finType.
Variable m n : nat.
Variable F : finType.
Variable pM : pTM sig F m.
Variable I : Vector.t ((Fin.t n)) m.
Variable I_dupfree : dupfree I.
Definition LiftTapes_trans := fun '(q, sym ) => let (q', act) := trans (m := projT1 pM) (q, select I sym) in (q', fill_default I (None, Nmove) act).
Definition LiftTapes_TM : TM sig n := {| trans := LiftTapes_trans; start := start (projT1 pM); halt := halt (m := projT1 pM); |}.
Definition LiftTapes : pTM sig F n := (LiftTapes_TM; projT2 pM).
Definition selectConf : mconfig sig (state LiftTapes_TM) n -> mconfig sig (state (projT1 pM)) m := fun c => mk_mconfig (cstate c) (select I (ctapes c)).
End LiftNM.
Arguments LiftTapes : simpl never.
Notation "pM @ ts" := (LiftTapes pM ts) (at level 41, only parsing).
Ltac smpl_dupfree := once lazymatch goal with | [ |- dupfree [|Fin.F1 |] ] => apply smpl_dupfree_helper1 | [ |- dupfree [|Fin.FS |] ] => apply smpl_dupfree_helper2 | [ |- dupfree _ ] => now vector_dupfree (* fallback tactic *) end.
Ltac smpl_TM_LiftN := once lazymatch goal with | [ |- LiftTapes _ _ ⊨ _] => apply LiftTapes_Realise; [ smpl_dupfree | ] | [ |- LiftTapes _ _ ⊨c(_) _] => apply LiftTapes_RealiseIn; [ smpl_dupfree | ] | [ |- projT1 (LiftTapes _ _) ↓ _] => apply LiftTapes_Terminates; [ smpl_dupfree | ] end.
Smpl Add smpl_TM_LiftN : TM_Correct.
Ltac is_num_const n := once lazymatch n with | O => idtac | S ?n => is_num_const n | _ => fail "Not a number" end.
Ltac do_n_times n t := match n with | O => idtac | (S ?n') => t 0; do_n_times n' ltac:(fun i => let next := constr:(S i) in t next) end.
Ltac do_n_times_fin_rect n m t := once lazymatch n with | O => idtac | S ?n' => let m' := eval hnf in (pred m) in let one := eval cbv in (@Fin.F1 _ : Fin.t m) in t one; do_n_times_fin_rect n' m' ltac:(fun i => let next := eval hnf in (Fin.FS i) in t next) end.
Ltac do_n_times_fin n t := do_n_times_fin_rect n n t.
Ltac vector_contains a vect := once lazymatch vect with | @Vector.nil ?A => fail "Vector doesn't contain" a | @Vector.cons ?A a ?n ?vect' => idtac | @Vector.cons ?A ?b ?n ?vect' => vector_contains a vect' | _ => fail "No vector" vect end.
Fixpoint not_indexb {n} (v : list (Fin.t n)) (i : Fin.t n) {struct v}: bool := match v with []%list => true | (i'::v)%list => if Fin.eqb i' i then false else not_indexb v i end.
Require Import Equations.Prop.DepElim.
Arguments not_indexb : simpl nomatch.
Local Definition _Flag_DisableWarning := Lock unit.
Local Definition _flag_DisableWarning : _Flag_DisableWarning := tt.
Ltac simpl_not_in_vector_one := let moveCnstLeft := let rec loop k n := lazymatch n with S ?n => loop uconstr:(S k) n | _ => uconstr:(k + n) end in loop 0 in once lazymatch goal with | [ H : forall i : Fin.t ?n, not_index ?vect i -> _ |- _ ] => specialize (not_index_reflect_helper H);clear H;intros H; let n' := moveCnstLeft n in change n with n' in H at 1; let tmp := fresh "tmp" in apply splitAllFin in H as [tmp H]; cbn [not_indexb Vector.to_list Fin.R Vector.caseS Fin.eqb Vector.nth] in H; let helper i := let H' := fresh H "_0" in assert (H':= tmp i); cbn in H'; once lazymatch type of H' with | if (if Nat.eqb ?k ?k then false else true) then _ else True => fail 1000 "arguments for not_indexb should have been set to [simpl nomatch]";clear H' | if not_indexb (?i::_)%list ?i then _ else True => clear H' | ?i = ?j => idtac | True => clear H' | ?G => idtac "simpl_not_in_vector_one is not intended for this kind of non-ground tape index" G end in once lazymatch type of tmp with forall i : Fin.t ?n, _ => do_n_times_fin n helper;clear tmp end; match type of H with | forall i : Fin.t 0, _ => clear H | forall u, if _ then _ else _ => specialize (not_index_reflect_helper2 H);clear H;intros H;cbn [Vector.of_list] in H | forall i : Fin.t _, _[@ _] = _[@ _] => idtac | ?t => match goal with | H : _Flag_DisableWarning |- _ => idtac | |- _ => idtac "unexpected case in simpl_not_in_vector_one" t end end end.
Ltac simpl_not_in_vector := repeat simpl_not_in_vector_one.
Ltac simpl_not_in := repeat simpl_not_in_vector.

Lemma lookup_index_vector_Some' (m n : nat) (I : Vector.t (Fin.t n) m) (i : Fin.t n) (j : Fin.t m) : lookup_index_vector I i = Some j -> I[@j] = i.
Proof.
revert i j.
induction I as [ | i' n' I' IH ]; intros i j Hj.
-
destruct_fin j.
-
pose proof (fin_destruct_S j) as [(j'&->) | ->]; cbn in *.
+
destruct (Fin.eqb i i'); inv Hj.
destruct (lookup_index_vector I' i) as [ j'' | ] eqn:Ej''.
*
apply Some_inj in H0.
apply Fin.FS_inj in H0 as ->.
now apply IH.
*
congruence.
+
destruct (Fin.eqb i i') eqn:Ei'.
*
now apply Fin.eqb_eq in Ei'.
*
destruct (lookup_index_vector I' i) as [ j'' | ] eqn:Ej''.
--
congruence.
--
congruence.
