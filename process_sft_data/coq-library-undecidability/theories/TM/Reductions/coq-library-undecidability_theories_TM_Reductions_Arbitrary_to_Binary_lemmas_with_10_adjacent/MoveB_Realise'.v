From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import ArithPrelim.
Require Import Undecidability.Shared.FinTypeEquiv Undecidability.Shared.FinTypeForallExists.
Set Default Proof Using "Type".
Section fix_Sigma.
Variable n : nat.
Definition encode_sym (s : Fin.t n) : list bool := let i := proj1_sig (Fin.to_nat s) in repeat false i ++ repeat true (n - i).
Fixpoint encode_string (s : list (Fin.t n)) := match s with | [] => [] | i :: l => false :: encode_sym i ++ true :: encode_string l end.
Definition encode_tape (t : tape (Fin.t n)) := match t with | niltape => niltape | midtape ls c_i rs => midtape (rev (encode_string (rev ls))) false (encode_sym c_i ++ true :: encode_string rs) | leftof c_i rs => leftof false (encode_sym c_i ++ true :: encode_string rs) | rightof c_i ls => rightof true (rev (encode_sym c_i) ++ false :: rev(encode_string (rev (ls)))) end.
End fix_Sigma.
Fixpoint ReadB (n : nat) : pTM (FinType (EqType bool)) (option (Fin.t n)) 1.
Proof.
destruct n as [ | n ].
-
exact (Return Nop None).
-
refine (Switch ReadChar (fun o : option bool => match o with None => Return Nop None | Some _ => Move Rmove ;; Switch ReadChar (fun o : option bool => match o with | None => Return (Move Lmove) None | Some true => Return (Move Lmove) (Some Fin.F1) | Some false => Switch (ReadB n) (fun o => Return (Move Lmove) (match o with | None => None | Some i => Some (Fin.R 1 i) end)) end) end)).
Defined.
Definition ReadB_rel' d n : Vector.t (tape bool) 1 -> option (Fin.t (d + n)) * Vector.t (tape bool) 1 -> Prop := fun t '(l, t') => forall t_sig : tape (Fin.t n), t = [| encode_tape t_sig |] -> t' = t /\ forall s, current t_sig = Some s -> l = Some (Fin.R d s).
Smpl Add eassumption : TM_Correct.
Fixpoint ReadB_canonical n : {Rel | ReadB n ⊨ Rel}.
Proof.
destruct n; cbn.
-
eexists.
TM_Correct.
-
eexists.
eapply Switch_Realise.
TM_Correct.
cbn in *.
intros [ | ].
instantiate (1 := fun o => match o with None => _ | Some _ => _ end).
eapply Seq_Realise.
TM_Correct.
eapply Switch_Realise.
TM_Correct.
cbn in *.
intros [[] | ].
instantiate (1 := fun o => match o with None => _ | Some true => _ | Some false => _ end).
cbn in *.
TM_Correct.
eapply Switch_Realise.
eapply (proj2_sig (ReadB_canonical n)).
instantiate (1 := fun o => match o with None => _ | Some _ => _ end).
intros []; TM_Correct.
TM_Correct.
cbn.
TM_Correct.
Defined.
Definition isTotal {Σ} {L} {n} (M : pTM Σ L n) := exists c, projT1 M ↓ fun t k => c <= k.
Ltac help := intros;TMSimp; destruct_tapes; TMSimp; try lia; try match goal with [ |- ?L <= ?R ] => tryif (is_evar R) then (eapply le_plus_l) else (ring_simplify; shelve) | _ => idtac end.
Require Import Undecidability.TM.Compound.WriteString.
Fixpoint MoveM {Σ : finType} (D : move) (n : nat) : pTM Σ unit 1 := match n with | 0 => Nop | S n => MoveM D n ;; Move D end.
Definition TestLeftof {Σ : finType} : pTM Σ bool 1 := Switch ReadChar (fun s1 => match s1 with Some _ => Return Nop false | None => Move Rmove ;; Switch ReadChar (fun s2 => match s2 with None => Return Nop false | Some _ => Return (Move Lmove) true end) end).
Definition MoveL_rel {Σ : finType} D (n : nat) : Vector.t (tape Σ) 1 -> unit * Vector.t (tape Σ) 1 -> Prop := fun t '(_, t') => t' = Vector.map (Nat.iter n (fun t => @tape_move Σ t D)) t.
Definition WriteB (n : nat) (c : option (Fin.t n)) : pTM (FinType (EqType bool)) unit 1 := match c with | None => Nop | Some c => Switch TestLeftof (fun b => if b then WriteString Lmove (rev (false :: encode_sym c ++ [true])) else WriteString Rmove (false :: encode_sym c ++ [true]) ;; MoveM Lmove (S n)) end.
Definition MoveB (m : move) n : pTM (finType_CS bool) unit 1 := Switch TestLeftof (fun b => match b, m with | true, Rmove => Move Rmove | _, _ => MoveM m (2 + n) end).
Arguments Nat.iter : simpl never.
Opaque Nat.iter.
Section FixM.
Variable Σ : finType.
Let n := (projT1 (finite_n Σ)).
Let f := (projT1 (projT2 (finite_n Σ))).
Let g := (proj1_sig (projT2 (projT2 (finite_n Σ)))).
Let Hf := (proj1 (proj2_sig (projT2 (projT2 (finite_n Σ))))).
Let Hg := (proj2 (proj2_sig (projT2 (projT2 (finite_n Σ))))).
Instance R : Retract (Fin.t n) Σ.
Proof.
eapply (@Build_Retract _ _ g (fun x => Some (f x ))).
econstructor.
-
intros [= <-]; now rewrite Hg.
-
intros ->; now rewrite Hf.
Definition encode_tape' (t : tape Σ) : tape bool := encode_tape (mapTape f t).
Variable M : TM Σ 1.
Definition Step (q : state M) : pTM (finType_CS bool) (state M + state M) 1 := Switch (ReadB n) (fun c_i => if halt q then Return Nop (inr q) else let '(q', e) := trans M (q, [| map_opt g c_i |]) in let '(existT _ (c', m) _) := destruct_vector_cons e in WriteB (map_opt f c') ;; MoveB m n ;; Return Nop (inl q')).
Smpl Add (eapply ReadB_Realise') : TM_Correct.
Smpl Add (eapply WriteB_Realise') : TM_Correct.
Smpl Add (eapply MoveB_Realise') : TM_Correct.
End FixM.
Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts Undecidability.TM.Util.TM_facts.
From Equations Require Import Equations.

Lemma WriteB_TerminatesIn (n : nat) (c : option (Fin.t n)) : isTotal (WriteB c).
Proof.
destruct (@MoveM_isTotal (finType_CS bool) Lmove n) as [MoveM_c H_MoveM].
red.
eexists.
eapply TerminatesIn_monotone.
unfold WriteB.
destruct c; cbn.
-
instantiate (1 := ltac:(destruct c; refine _ )).
cbn.
TM_Correct.
eapply TestLeftof_Realise.
unfold TestLeftof.
TM_Correct.
eapply RealiseIn_TerminatesIn, WriteString_Sem.
eapply RealiseIn_Realise, WriteString_Sem.
eapply RealiseIn_TerminatesIn, WriteString_Sem.
eapply MoveM_Realise.
-
cbn.
TM_Correct.
-
cbn.
intros ? ? ?.
destruct c; cbn.
+
repeat eexists.
help.
eapply le_plus_l.
intros.
TMSimp.
destruct_tapes.
cbn.
destruct (current _).
*
destruct b; help.
*
repeat eexists.
help.
help.
help.
eapply le_plus_l.
intros.
TMSimp.
destruct_tapes.
TMSimp.
destruct current.
destruct b; help.
lia.
*
eapply H.
*
intros.
TMSimp.
destruct_tapes.
rename tout_0 into h.
destruct h; help.
--
TMSimp.
repeat eexists.
rewrite !app_length, length_encode_sym.
cbn.
eapply le_plus_l.
cbn.
instantiate (1 := ltac:(destruct c; refine _ )).
cbn in *.
eapply le_plus_l.
eapply le_plus_l.
eapply le_plus_l.
intros.
eapply le_plus_l.
--
TMSimp.
rewrite !app_length, rev_length, !app_length, length_encode_sym.
cbn.
lia.
--
TMSimp.
repeat eexists.
rewrite !app_length, length_encode_sym.
cbn.
eapply le_plus_l.
2: eapply le_plus_l.
2:eapply le_plus_l.
2: intros; eapply le_plus_l.
ring_simplify.
shelve.
--
TMSimp.
repeat eexists.
rewrite !app_length, length_encode_sym.
cbn.
eapply le_plus_l.
cbn.
shelve.
eapply le_plus_l.
eapply le_plus_l.
intros.
eapply le_plus_l.
+
lia.
Unshelve.
all: try exact 0.
lia.
lia.
Admitted.

Lemma midtape_left_midtape {Σ : finType} (l1 l2 : list Σ) m m' r n : n = S (length l1) -> Nat.iter n (@tape_move_left Σ) (midtape (rev l1 ++ [m'] ++ l2) m r) = midtape l2 m' (l1 ++ m :: r).
Proof.
intros ->.
induction l1 in m, m', l2 |- *.
-
cbn.
reflexivity.
-
cbn.
rewrite <- app_assoc.
rewrite Nat_iter_S'.
Admitted.

Lemma midtape_right_midtape {Σ : finType} l m r1 c r2 n : n = S (length r1) -> Nat.iter n (@tape_move_right Σ) (midtape l m (r1 ++ c :: r2)) = midtape (rev r1 ++ m :: l) c r2.
Proof.
intros ->.
induction r1 in m, c, r2 |- * using rev_ind; cbn.
-
reflexivity.
-
rewrite app_length.
cbn.
rewrite plus_comm.
cbn.
rewrite <- app_assoc, Nat_iter_S'.
cbn.
rewrite (IHr1 m x (c :: r2)).
cbn.
Admitted.

Lemma midtape_right_rightof {Σ : finType} l m rs c n : n = 2 + (length rs) -> Nat.iter n (@tape_move_right Σ) (midtape l m (rs ++ [c])) = rightof c (rev rs ++ m :: l).
Proof.
intros ->.
cbn.
rewrite Nat_iter_S'.
rewrite midtape_right_midtape.
2:reflexivity.
cbn.
Admitted.

Lemma MoveB_Realise (n : nat) m : MoveB m n ⊨ fun t '(l, t') => forall t_sig, t = [| encode_tape t_sig |] -> t' = [| @encode_tape n (mv m t_sig) |].
Proof.
epose (R := _).
eapply Realise_monotone.
{
unfold MoveB.
eapply Switch_Realise.
eapply TestLeftof_Realise.
instantiate (1 := R m).
subst R.
instantiate (1 := fun m b => if b then _ else _).
cbn.
intros [].
cbn.
instantiate (1 := match m0 with Rmove => _ | _ => _ end).
cbn.
destruct m.
TM_Correct.
eapply MoveM_Realise.
TM_Correct.
TM_Correct.
eapply MoveM_Realise.
TM_Correct.
eapply MoveM_Realise.
}
subst R.
assert (forall n c rs, Nat.iter n (fun t : tape bool => tape_move_left t) (leftof c rs) = leftof c rs) as Eleft.
{
clear.
intros.
clear.
induction n; cbn.
reflexivity.
rewrite Nat_iter_S', IHn.
reflexivity.
}
intros t ([], t') ? t_sig ->.
TMSimp.
destruct_tapes.
f_equal.
destruct t_sig.
-
TMSimp.
destruct_tapes.
TMSimp.
assert (Nat.iter n (fun t : tape bool => tape_move t m) niltape = niltape) as ->.
{
induction n; cbn.
reflexivity.
rewrite Nat_iter_S', IHn.
now destruct m.
}
now destruct m.
-
cbn in *.
TMSimp.
destruct m.
+
TMSimp.
destruct_tapes.
TMSimp.
now rewrite Eleft.
+
TMSimp.
reflexivity.
+
TMSimp.
destruct_tapes.
TMSimp.
now rewrite Nat_iter_id.
-
TMSimp.
destruct_tapes.
TMSimp.
destruct m.
+
cbn.
rewrite <- !Nat_iter_S' with (f := fun t0 => tape_move_left t0).
rewrite Nat_iter_S.
cbn.
pose proof (@midtape_left_midtape (finType_CS bool)).
cbn in H.
erewrite <- H.
2: reflexivity.
rewrite Nat_iter_S'.
rewrite length_encode_sym.
reflexivity.
+
enough (forall c rs, Nat.iter n (fun t : tape bool => tape_move_right t) (rightof c rs) = rightof c rs) as -> by reflexivity.
intros.
clear.
induction n; cbn.
reflexivity.
rewrite Nat_iter_S', IHn.
reflexivity.
+
now rewrite Nat_iter_id.
-
TMSimp.
destruct_tapes.
TMSimp.
rename l into rs, l0 into ls.
rewrite <- !Nat_iter_S' with (f := fun t0 => tape_move t0 m).
destruct m.
+
cbn.
destruct rs.
*
cbn.
rewrite Nat_iter_S.
cbn.
now rewrite Eleft.
*
cbn.
pose proof (@midtape_left_midtape (finType_CS bool)).
cbn in H.
rewrite encode_string_app, rev_app_distr.
cbn.
rewrite rev_app_distr.
cbn.
rewrite Nat_iter_S.
cbn.
rewrite <- app_assoc.
erewrite <- H.
2:reflexivity.
rewrite length_encode_sym.
reflexivity.
+
cbn.
destruct ls.
*
cbn.
pose proof (@midtape_right_rightof (finType_CS bool)).
cbn in H.
rewrite H.
2:now rewrite length_encode_sym.
reflexivity.
*
cbn.
rewrite Nat_iter_S'.
pose proof (@midtape_right_midtape (finType_CS bool)).
cbn in H.
rewrite H.
cbn.
rewrite encode_string_app.
cbn.
rewrite !rev_app_distr.
cbn.
rewrite rev_app_distr.
cbn.
rewrite <- app_assoc.
cbn.
reflexivity.
now rewrite length_encode_sym.
+
cbn.
rewrite Nat_iter_id.
Admitted.

Lemma TestLeftof_total {Σ} : isTotal (@TestLeftof Σ).
Proof.
unfold TestLeftof.
eexists.
eapply TerminatesIn_monotone.
TM_Correct.
intros ? ? ?.
repeat eexists; help.
destruct current; help.
repeat eexists.
help.
help.
help.
instantiate (1 := ltac:(destruct x; refine _)).
cbn.
eapply le_plus_l.
help.
destruct current.
help.
help.
Unshelve.
all: try destruct x; cbn.
4:{
eapply H.
}
Admitted.

Lemma MoveB_total (n : nat) : exists c, forall m, projT1 (MoveB m n) ↓ fun t k => c <= k.
Proof.
destruct (@TestLeftof_total (finType_CS bool)) as [c Hlo].
destruct (@MoveM_isTotal (finType_CS bool) Lmove n) as [c1 H1].
destruct (@MoveM_isTotal (finType_CS bool) Nmove n) as [c2 H2].
destruct (@MoveM_isTotal (finType_CS bool) Rmove n) as [c3 H3].
eexists.
intros m.
eapply TerminatesIn_monotone.
unfold MoveB.
eapply Switch_TerminatesIn.
TM_Correct.
eapply TestLeftof_Realise.
eapply Hlo.
intros f.
instantiate (1 := fun f => if f then _ else _).
cbn.
destruct f.
-
destruct m.
instantiate (1 := ltac:(destruct m, f; refine _)).
all: cbn.
eapply Seq_TerminatesIn.
TM_Correct.
eapply MoveM_Realise.
TM_Correct.
eapply MoveM_Realise.
TM_Correct.
TM_Correct.
TM_Correct.
eapply MoveM_Realise.
eapply MoveM_Realise.
-
instantiate (1 := ltac:(destruct f; refine _)); cbn.
TM_Correct.
eapply MoveM_Realise.
eapply MoveM_Realise.
destruct m.
instantiate (1 := ltac:(destruct m; refine _)); cbn.
all: cbn.
all:eassumption.
-
cbn.
intros ? ? ?.
repeat eexists; help.
TMSimp.
destruct_tapes.
TMSimp.
rename tout_0 into h.
destruct h; TMSimp.
repeat eexists; help.
destruct m.
instantiate (1:= ltac:(destruct m; refine _)); cbn.
all:cbn.
all:help.
destruct m.
instantiate (1:= ltac:(destruct m; refine _)); cbn.
all:cbn.
repeat eexists; help.
lia.
repeat eexists; help.
repeat eexists.
destruct m.
instantiate (1:= ltac:(destruct m; refine _)); cbn.
all:cbn.
all:help.
repeat eexists.
destruct m.
instantiate (1:= ltac:(destruct m; refine _)); cbn.
all:cbn.
all:help.
Unshelve.
all: try destruct x; cbn in *.
all: try destruct x; cbn in *.
all:try destruct m; cbn in *.
17:{
eapply H.
}
16:{
instantiate (6 := c1).
instantiate (6 := c3) in H.
ring_simplify in H.
ring_simplify.
replace (c + c1 + c3) with (c + c3 + c1) by lia.
eapply H.
}
14:{
ring_simplify.
ring_simplify in H.
instantiate (6 := c3).
instantiate (5 := c1).
instantiate (5 := c2) in H.
replace (c + c3 + c2 + c1) with (c + c3 + c1 + c2) by lia.
eapply H.
}
all:try exact 0.
all: try lia.
Admitted.

Instance R : Retract (Fin.t n) Σ.
Proof.
eapply (@Build_Retract _ _ g (fun x => Some (f x ))).
econstructor.
-
intros [= <-]; now rewrite Hg.
-
Admitted.

Lemma ReadB_Realise' : ReadB n ⊨ fun t '(l, t') => forall t_sig : tape Σ, t = [| encode_tape' t_sig |] -> t' = t /\ l = map_opt f (current t_sig).
Proof.
eapply Realise_monotone.
eapply ReadB_Realise.
intros t (?, t') ? t_sig ->.
destruct_tapes.
cbn in *.
specialize (H (mapTape f t_sig) eq_refl) as [[= ->] ->].
split.
eauto.
Admitted.

Lemma WriteB_Realise' (c : option Σ) : WriteB (map_opt f c) ⊨ fun t '(_, t') => forall t_sig, t = [| encode_tape' t_sig |] -> t' = [| encode_tape' (wr c t_sig) |].
Proof.
eapply Realise_monotone.
eapply WriteB_Realise.
intros t (?, t') ? t_sig ->.
destruct_tapes.
cbn in *.
specialize (H (mapTape f t_sig) eq_refl) as [= ->].
unfold tape_write.
destruct c.
-
cbn.
destruct t_sig; reflexivity.
-
Admitted.

Lemma Step_Realise q : Step q ⊨ fun t '(q_, t') => forall t_sig, t = [| encode_tape' t_sig |] -> if halt q then q_ = inr q /\ t' = t else let '(q', a) := trans M (q, [| current t_sig |]) in let '(existT _ (c', m) _) := destruct_vector_cons a in q_ = inl q' /\ t' = [| encode_tape' (mv m (wr c' t_sig)) |].
Proof.
eapply Realise_monotone.
{
unfold Step.
eapply Switch_Realise.
TM_Correct.
cbn.
intros c_i.
instantiate (1 := fun c_i => _).
cbn.
instantiate (1 := ltac:(destruct (halt q); refine _)).
destruct (halt q).
cbn.
TM_Correct.
instantiate (1 := ltac:(destruct (trans (q, [|map_opt g c_i|])); refine _)).
cbn.
destruct (trans (q, [|map_opt g c_i|])).
instantiate (1 := ltac:(destruct (destruct_vector_cons t); refine _)).
cbn.
destruct (destruct_vector_cons t).
cbn.
instantiate (1 := ltac:(destruct x; refine _)).
cbn.
destruct x.
TM_Correct.
}
intros t (q_, t') ? t_sig ->.
TMSimp.
rename t'_0 into t'.
destruct (halt q) eqn:Eq.
-
TMSimp.
split.
reflexivity.
eapply H.
reflexivity.
-
specialize (H _ eq_refl) as [[= ->] ->].
cbn in *.
assert (Efg : forall o, map_opt g (map_opt f o) = o).
{
intros [s | ]; cbn; now rewrite ?Hg.
}
rewrite Efg in H0.
clear Efg.
destruct trans as [q' T] eqn:Eqt.
destruct destruct_vector_cons as [[m c'] [nl ->]].
TMSimp.
destruct_vector.
split.
reflexivity.
Admitted.

Lemma WriteB_total' : exists C, forall (c : option (Fin.t n)), projT1 (WriteB c) ↓ fun t k => k >= C.
Proof.
eapply fintype_forall_exists; cbn.
-
intros.
eapply TerminatesIn_monotone.
eassumption.
intros ? ? ?.
lia.
-
Admitted.

Lemma Step_total q : isTotal (Step q).
Proof.
destruct (MoveB_total n).
destruct (ReadB_total n).
destruct (WriteB_total').
eexists.
eapply TerminatesIn_monotone.
-
unfold Step.
eapply Switch_TerminatesIn.
TM_Correct.
cbn in *.
eapply H0.
cbn.
intros c_i.
instantiate (1 := ltac:(intros c_i; refine _)); cbn.
instantiate (1 := ltac:(destruct (halt q); refine _)); cbn.
destruct halt.
TM_Correct.
instantiate (1 := ltac:(destruct (trans (q, [| map_opt g c_i |])), (destruct_vector_cons t), x2 ; refine _)); cbn.
destruct (trans (q, [| map_opt g c_i |])); cbn.
destruct (destruct_vector_cons t); cbn.
destruct x2.
TM_Correct.
eapply H1.
eapply H.
-
cbn.
intros ? ? ?.
repeat eexists; help.
instantiate (1 := ltac:(destruct (halt q); refine _)); cbn.
destruct halt.
lia.
rename yout into c_i.
destruct (trans (q, [| map_opt g c_i |])); cbn.
destruct (destruct_vector_cons t); cbn.
instantiate (1 := ltac:(destruct x2; refine _)).
destruct x2.
TM_Correct.
repeat eexists.
eapply le_plus_l.
eapply le_plus_l.
eapply le_plus_l.
eapply le_plus_l.
intros.
eapply le_plus_l.
Unshelve.
all:cbn.
all: try destruct x2; cbn in *.
3:{
destruct halt.
cbn.
eapply H2.
eapply H2.
}
all:exact 0.
Unshelve.
Admitted.

Lemma Step_total' : exists C, forall q, projT1 (Step q) ↓ fun t k => C <= k.
Proof.
eapply fintype_forall_exists.
-
intros.
eapply TerminatesIn_monotone.
eassumption.
intros ? ?.
lia.
-
intros q.
Admitted.

Theorem WhileStep_Realise : StateWhile Step (start M) ⊨ fun t '(q', t') => forall t_sig, t = [| encode_tape' t_sig |] -> exists t_sig', eval M (start M) [| t_sig |] q' [| t_sig' |] /\ t' = [| encode_tape' t_sig'|].
Proof.
generalize (start M).
intros q.
eapply Realise_monotone.
{
TM_Correct.
eapply Step_Realise.
}
intros t (l, t') ? t_sig E.
TMSimp.
destruct_tapes.
rename t'_0 into t'.
remember ([|encode_tape' t_sig|]) as tin.
remember (l, [|t'|]) as cout.
induction H in t_sig, l, t', Heqtin, Heqcout |- *.
-
TMSimp.
destruct_tapes.
specialize (H _ eq_refl).
rename l0 into q.
destruct (halt q) eqn:Eq.
+
inv Heqcout.
destruct H as [[= ->] [= ->]].
+
inv Heqcout.
destruct trans as [q' T] eqn:Eqt.
destruct destruct_vector_cons as [[m c'] [nl ->]].
destruct_vector.
destruct H as [[= ->] [= ->]].
specialize (IHStateWhile_Rel _ _ _ eq_refl eq_refl) as [t_sig' [H1 [= ->]]].
exists t_sig'.
split; try reflexivity.
econstructor.
eassumption.
eassumption.
cbn.
eassumption.
-
inv Heqcout.
specialize (H _ eq_refl).
rename l0 into q.
destruct (halt q) eqn:Eq.
+
destruct H as [[= ->] [= ->]].
eexists; split; try reflexivity.
now econstructor.
+
destruct trans as [q' T] eqn:Eqt.
destruct destruct_vector_cons as [[m c'] [nl ->]].
destruct_vector.
Admitted.

Theorem WhileStep_Terminates : exists C1 C2, projT1 (StateWhile Step (start M)) ↓ fun t k => exists t_sig, t = [| encode_tape' t_sig |] /\ exists k' t_sig' q', loopM (initc M [| t_sig |]) k' = Some (mk_mconfig q' [| t_sig' |] ) /\ k >= C1 * k' + C2.
Proof.
unfold initc.
generalize (start M).
intros q.
destruct (Step_total') as [C HC].
eexists.
eexists.
eapply TerminatesIn_monotone.
{
eapply StateWhile_TerminatesIn.
intros.
eapply Step_Realise.
intros.
eapply HC.
}
revert q.
eapply StateWhileCoInduction.
intros q tin k H.
TMSimp.
rename ymid0 into steps, ymid into t_sig, ymid1 into t_sig', ymid2 into q'.
remember [|t_sig|] as tin.
remember [|t_sig'|] as tout.
rename H0 into H.
rename H1 into H0.
induction steps in tin, t_sig, Heqtin, q, H0, H |- *.
-
cbn in H.
unfold haltConf in H.
cbn in *.
destruct (halt q) eqn:Eq; cbn.
+
inv H.
eexists.
split.
eapply le_plus_l.
intros.
destruct_tapes.
specialize (H _ eq_refl) as [[= ->] [= ->]].
ring_simplify in H0.
shelve.
+
inv H.
-
cbn in H.
unfold haltConf in H.
cbn in *.
destruct (halt q) eqn:Eq; cbn.
+
inv H.
eexists.
split.
eapply le_plus_l.
intros.
destruct_tapes.
specialize (H _ eq_refl) as [[= ->] [= ->]].
ring_simplify in H0.
shelve.
+
subst.
unfold step in H.
cbn in *.
unfold current_chars in *.
cbn in *.
destruct trans as (qnxt, A) eqn:Et.
cbn in *.
destruct (destruct_vector_cons A) eqn:E2.
destruct x as (c', m) eqn:E3.
destruct s as [? ->].
destruct_vector.
cbn in *.
pose proof (Hrem := H).
eapply IHsteps in H.
eexists.
split.
eapply le_plus_l.
intros.
specialize (H1 _ eq_refl).
rewrite Et in H1.
rewrite E2 in H1.
destruct H1.
subst.
repeat eexists.
rewrite <- Hrem.
repeat f_equal.
now destruct t_sig, m, c'.
shelve.
shelve.
reflexivity.
shelve.
Unshelve.
exact (1 + C).
exact (2 + 2 * C).
exact 0.
2: exact 0.
3: exact 0.
3: (exact ((2 + steps) * S C)).
Admitted.

Lemma Sim_Realise {Σ} (L : finType) (M : pTM Σ L 1) R : M ⊨ R -> Relabel (StateWhile (@Step Σ (projT1 M)) (start (projT1 M))) (projT2 M) ⊨ fun t '(l, t') => forall t_sig, t = [| encode_tape' t_sig |] -> exists t_sig', R [| t_sig |] (l, [| t_sig' |]) /\ t' = [| encode_tape' t_sig' |].
Proof.
intros HM.
eapply Realise_monotone.
{
eapply Relabel_Realise, WhileStep_Realise.
}
intros ? ? ?.
TMSimp.
specialize (H0 _ eq_refl).
TMSimp.
repeat eexists.
unfold Realise in HM.
eapply TM_eval_iff in H as [k H].
Admitted.

Lemma Sim_Terminates {Σ} (L : finType) (M : pTM Σ L 1) T : projT1 M ↓ T -> exists C1 C2, projT1 (Relabel (StateWhile (@Step Σ (projT1 M)) (start (projT1 M))) (projT2 M)) ↓ fun t k => exists t_sig k', t = [| encode_tape' t_sig |] /\ T [| t_sig |] k' /\ k >= C1 * k' + C2.
Proof.
intros HM.
destruct (WhileStep_Terminates (projT1 M)) as (C1 & C2 & HC).
exists C1, C2.
eapply TerminatesIn_monotone.
{
eapply Relabel_Terminates, HC.
}
intros ? ? ?.
TMSimp.
eapply HM in H0.
TMSimp.
destruct ymid1.
destruct_tapes.
Admitted.

Theorem reduction : HaltTM 1 ⪯ fun '(M,t) => @HaltsTM (finType_CS bool) 1 M t.
Proof.
unshelve eexists.
-
intros [Σ M t].
split.
exact (projT1 (StateWhile (@Step Σ M) (start M))).
exact (Vector.map (fun t => encode_tape' t) t).
-
intros [Σ M t].
cbn.
split.
+
intros (q' & t' & [n H] % TM_eval_iff).
edestruct @Sim_Terminates with (M := (existT _ M (fun _ : state M => tt))) (T := fun tin k => tin = t /\ k >= n).
*
intros tin k [-> Hk].
cbn.
exists (mk_mconfig q' t').
eapply @loop_monotone.
exact H.
eapply Hk.
*
destruct H0 as [k H0].
cbn in H0.
edestruct H0 as [[] H1].
--
exists (Vector.hd t), n.
split.
reflexivity.
split.
2: now unfold ge.
split.
2:lia.
dependent elimination t.
dependent elimination t.
reflexivity.
--
exists cstate.
eexists ctapes.
eapply TM_eval_iff.
exists (x * n + k).
unfold Relabel, initc in H1.
cbn in H1.
repeat dependent elimination t.
exact H1.
+
intros (q' & t' & [n H] % TM_eval_iff).
eapply (Sim_Realise (M := (existT _ M (fun _ : state M => tt))) (R := fun tin '(_,tout) => exists q', eval M (start M) tin q' tout)) in H.
*
repeat dependent elimination t.
rename h into t.
specialize (H t eq_refl) as [t'_sig [[q'_ H1] H2]].
cbn in H1.
cbn in H2.
subst.
exists q'_, [|t'_sig|].
eassumption.
*
intros tin k [q'_ tout] Hter.
cbn in *.
exists q'_.
eapply TM_eval_iff.
exists k.
Admitted.

Lemma MoveB_Realise' m : MoveB m n ⊨ fun t '(l, t') => forall t_sig, t = [| encode_tape' t_sig |] -> t' = [| encode_tape' (mv m t_sig) |].
Proof.
eapply Realise_monotone.
eapply MoveB_Realise.
intros t (?, t') ? t_sig ->.
destruct_tapes.
cbn in *.
specialize (H (mapTape f t_sig) eq_refl) as [= ->].
f_equal.
destruct t_sig, m; try reflexivity.
cbn.
destruct l; cbn; reflexivity.
cbn.
destruct l0; cbn; reflexivity.
