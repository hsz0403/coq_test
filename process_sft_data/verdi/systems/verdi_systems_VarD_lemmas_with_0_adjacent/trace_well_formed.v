Require Import Verdi.Verdi.
Require Import FMapList.
Require Import String.
Require Import Verdi.FMapVeryWeak.
Require Import Verdi.StateMachineHandlerMonad.
Definition key := string.
Definition value := string.
Inductive input : Set := | Put : key -> value -> input | Get : key -> input | Del : key -> input | CAS : key -> option value -> value -> input | CAD : key -> value -> input.
Inductive output : Set := | Response : key -> option value -> option value -> output.
Module VarDFunctor (Map : VWS with Definition E.t := string with Definition E.eq := @eq string).
Definition key_eq_dec := string_dec.
Definition value_eq_dec := string_dec.
Definition val_eq_dec : forall v v' : option value, {v = v'} + {v <> v'}.
decide equality.
auto using value_eq_dec.
Defined.
Definition trace_state_correct (trace : list (input * output)) (st : data) (st' : data) := forall k, fst (interpret k (rev (inputs_with_key trace k)) (Map.find k st)) = Map.find k st'.
Ltac vard_unfold := unfold runHandler, getk, setk, delk, resp in *; monad_unfold.
Open Scope string_scope.
Example trace_correct_eg0 : trace_correct [(Put "james" "awesome", Response "james" (Some "awesome") None)].
Proof.
rewrite <- app_nil_l.
constructor.
-
constructor.
-
simpl.
auto.
End VarDFunctor.
Module LogTimeVarD := VarDFunctor(LogTimeStringMap).
Module LinearTimeVarD := VarDFunctor(LinearTimeStringMap).
Module VarD := LogTimeVarD.
Export VarD.

Lemma trace_well_formed : forall st st' trace, step_1_star st st' trace -> (trace = [] \/ exists t i o, trace = t ++ [(i, o)]).
Proof.
intros.
find_apply_lem_hyp refl_trans_1n_n1_trace.
invcs H; intuition.
right.
exists cs.
invcs H1.
unfold VarDHandler, VarDHandler' in *.
vard_unfold.
repeat break_match; simpl in *; repeat find_inversion; repeat eexists; eauto.
