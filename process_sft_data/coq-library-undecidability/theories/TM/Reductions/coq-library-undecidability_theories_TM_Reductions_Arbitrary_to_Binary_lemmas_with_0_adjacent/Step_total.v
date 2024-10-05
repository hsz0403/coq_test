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
all:exact 0.
