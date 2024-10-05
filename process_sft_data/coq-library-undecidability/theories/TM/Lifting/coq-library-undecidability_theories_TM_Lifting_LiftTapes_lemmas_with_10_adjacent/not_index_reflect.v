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

Lemma LiftTapes_lift (c1 c2 : mconfig sig (state LiftTapes_TM) n) (k : nat) : loopM (M := LiftTapes_TM) c1 k = Some c2 -> loopM (M := projT1 pM) (selectConf c1) k = Some (selectConf c2).
Proof.
intros HLoop.
eapply loop_lift with (f := step (M := LiftTapes_TM)) (h := haltConf (M := LiftTapes_TM)).
-
cbn.
auto.
-
intros ? _.
now apply LiftTapes_comp_step.
-
Admitted.

Lemma LiftTapes_comp_eq (c1 c2 : mconfig sig (state LiftTapes_TM) n) (i : Fin.t n) : not_index I i -> step (M := LiftTapes_TM) c1 = c2 -> (ctapes c2)[@i] = (ctapes c1)[@i].
Proof.
intros HI H.
unfold LiftTapes_TM in *.
destruct c1 as [state1 tapes1] eqn:E1, c2 as [state2 tapes2] eqn:E2.
unfold step, select in *.
cbn in *.
destruct (trans (state1, select I (current_chars tapes1))) as (q, act) eqn:E3.
inv H.
erewrite Vector.nth_map2; eauto.
Admitted.

Lemma LiftTapes_eq (c1 c2 : mconfig sig (state LiftTapes_TM) n) (k : nat) (i : Fin.t n) : not_index I i -> loopM (M := LiftTapes_TM) c1 k = Some c2 -> (ctapes c2)[@i] = (ctapes c1)[@i].
Proof.
intros Hi HLoop.
unfold loopM in HLoop.
eapply loop_map with (g := fun c => (ctapes c)[@i]); eauto.
intros.
Admitted.

Lemma LiftTapes_Realise (R : Rel (tapes sig m) (F * tapes sig m)) : pM ⊨ R -> LiftTapes ⊨ LiftTapes_Rel I R.
Proof.
intros H.
split.
-
apply (H (select I t) k (selectConf outc)).
now apply (@LiftTapes_lift (initc LiftTapes_TM t) outc k).
-
hnf.
intros i HI.
Admitted.

Lemma LiftTapes_unlift (k : nat) (c1 : mconfig sig (state (LiftTapes_TM)) n) (c2 : mconfig sig (state (LiftTapes_TM)) m) : loopM (M := projT1 pM) (selectConf c1) k = Some c2 -> exists c2' : mconfig sig (state (LiftTapes_TM)) n, loopM (M := LiftTapes_TM) c1 k = Some c2' /\ c2 = selectConf c2'.
Proof.
intros HLoop.
unfold loopM in *.
cbn in *.
apply loop_unlift with (lift:=selectConf) (f:=step (M:=LiftTapes_TM)) (h:=haltConf (M:=LiftTapes_TM)) in HLoop as (c'&HLoop&->).
-
exists c'.
split; auto.
-
auto.
-
intros ? _.
Admitted.

Lemma LiftTapes_Terminates T : projT1 pM ↓ T -> projT1 LiftTapes ↓ LiftTapes_T I T.
Proof.
intros H initTapes k Term.
hnf in *.
specialize (H (select I initTapes) k Term) as (outc&H).
pose proof (@LiftTapes_unlift k (initc LiftTapes_TM initTapes) outc H) as (X&X'&->).
Admitted.

Lemma LiftTapes_RealiseIn R k : pM ⊨c(k) R -> LiftTapes ⊨c(k) LiftTapes_Rel I R.
Proof.
intros (H1&H2) % Realise_total.
apply Realise_total.
split.
-
now apply LiftTapes_Realise.
-
eapply TerminatesIn_monotone.
+
apply LiftTapes_Terminates; eauto.
+
Admitted.

Lemma smpl_dupfree_helper1 (n : nat) : dupfree [|Fin.F1 (n := n)|].
Proof.
Admitted.

Lemma smpl_dupfree_helper2 (n : nat) : dupfree [|Fin.FS (Fin.F1 (n := n))|].
Proof.
Admitted.

Lemma splitAllFin k' n (P : Fin.t (k'+n) -> Prop): (forall i, P i) -> (forall (i : Fin.t k'), P (Fin.L n i)) /\ (forall (i : Fin.t n), P (Fin.R k' i)).
Proof.
Admitted.

Lemma not_index_reflect_helper n m (v : Vector.t _ m) (P : Fin.t n -> Prop): (forall i : Fin.t n, not_index v i -> P i) -> (forall i : Fin.t n, if not_indexb (Vector.to_list v) i then P i else True).
Proof.
intros H i.
specialize (H i).
setoid_rewrite not_index_reflect in H.
Admitted.

Lemma not_index_reflect_helper2 n' (l : list _) (P : Fin.t n' -> Prop): (forall i : Fin.t n', if not_indexb l i then P i else True) -> (forall i : Fin.t n', not_index (Vector.of_list l) i -> P i).
Proof.
intros H i.
specialize (H i).
setoid_rewrite not_index_reflect.
rewrite VectorSpec.to_list_of_list_opp.
Admitted.

Lemma not_index_reflect n m (v : Vector.t _ m) (i : Fin.t n): not_index v i <-> not_indexb (Vector.to_list v) i = true.
Proof.
unfold Vector.to_list.
depind v;cbn.
easy.
specialize (Fin.eqb_eq _ h i) as H'.
destruct Fin.eqb.
{
destruct H' as [->].
2:easy.
split.
2:easy.
destruct 1.
constructor.
}
rewrite <- IHv.
cbv;intuition.
apply H1.
now constructor.
apply H1.
inversion H2;subst.
now specialize (H0 eq_refl).
apply Eqdep_dec.inj_pair2_eq_dec in H6;subst.
easy.
decide equality.
