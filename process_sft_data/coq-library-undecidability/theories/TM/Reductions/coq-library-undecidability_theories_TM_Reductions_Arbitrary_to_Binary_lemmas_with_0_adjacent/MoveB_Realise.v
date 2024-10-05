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
reflexivity.
