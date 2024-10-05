Require Import Undecidability.Shared.Libs.PSL.Base.
Require Import FunInd.
From Undecidability.L Require Export Prelim.ARS Prelim.MoreBase AbstractMachines.FlatPro.Programs.
Definition HAdd : Type := nat.
Definition HClos : Type := HAdd * Pro.
Definition HEntr : Type := option (HClos * HAdd).
Definition Heap : Type := list HEntr.
Section Semantics.
Implicit Types H : Heap.
Implicit Types T V : list HClos.
Implicit Types n m : nat.
Implicit Types a b c : HAdd.
Implicit Types g : HClos.
Implicit Types P Q : Pro.
Definition put H e : HAdd * Heap := (|H|, H++[e]).
Definition tailRecursion : HClos -> list HClos -> list HClos := fun '(a, P) T => match P with | [] => T | _ => (a, P) :: T end.
Definition state : Type := list HClos * list HClos * Heap.
Fixpoint jumpTarget (k:nat) (Q:Pro) (P:Pro) : option (Pro*Pro) := match P with | retT :: P' => match k with | 0 => Some (Q,P') | S k' => jumpTarget k' (Q++[retT]) P' end | lamT :: P' => jumpTarget (S k) (Q++[lamT]) P' | t :: P' => jumpTarget k (Q++[t]) P' (* either [varT n] or [appT] *) | [] => None end.
Fixpoint lookup H a n : option HClos := match nth_error H a with | Some (Some (g, b)) => match n with | 0 => Some g | S n' => lookup H b n' end | _ => None end.
Inductive step : state -> state -> Prop := | step_pushVal P P' Q a T V H : jumpTarget O [] P = Some (Q, P') -> step ((a, (lamT :: P)) :: T, V, H) (tailRecursion (a, P') T, (a, Q) :: V, H) | step_beta a b g P Q H H' c T V : put H (Some (g, b)) = (c, H') -> step ((a, (appT :: P)) :: T, g :: (b, Q) :: V, H) ((c, Q) :: tailRecursion (a, P) T, V, H') | step_load P a n g T V H : lookup H a n = Some g -> step ((a, (varT n :: P)) :: T, V, H) (tailRecursion (a, P) T, g :: V, H) .
Definition halt_state (s : state) : Prop := forall s', ~ step s s'.
Definition steps : state -> state -> Prop := star step.
Definition steps_k : nat -> state -> state -> Prop := pow step.
Definition halts (s : state) : Prop := exists s', steps s s' /\ halt_state s'.
Definition halts_k (s : state) (k : nat) : Prop := exists s', steps_k k s s' /\ halt_state s'.
Definition step_fun : state -> option state := fun '(T, V, H) => match T with | (a, (lamT :: P)) :: T => match jumpTarget O [] P with | Some (Q, P') => Some (tailRecursion (a, P') T, (a, Q) :: V, H) | _ => None end | (a, (appT :: P)) :: T => match V with | g :: (b, Q) :: V => let (c, H') := put H (Some (g, b)) in Some ((c, Q) :: tailRecursion (a, P) T, V, H') | _ => None end | (a, (varT x :: P)) :: T => match lookup H a x with | Some g => Some (tailRecursion (a, P) T, g :: V, H) | _ => None end | _ => None end.
Functional Scheme step_fun_ind := Induction for step_fun Sort Prop.
Definition is_halt_state (s : state) : bool := match step_fun s with | Some s' => false | None => true end.
Global Instance halt_state_dec : forall s, dec (halt_state s).
Proof.
intros s.
eapply dec_transfer.
apply is_halt_state_correct.
auto.
Defined.
End Semantics.
Definition largestVarC : HClos -> nat := (fun '(_,P) => largestVarP P).
Definition largestVarCs (T:list HClos) := maxl (map largestVarC T).
Definition largestVarHE (h:HEntr) := match h with None => 0 | Some (c,_) => largestVarC c end.
Definition largestVarH (H:list HEntr) := maxl (map largestVarHE H).

Lemma is_halt_state_correct (s : state) : is_halt_state s = true <-> halt_state s.
Proof.
intros.
split; auto using is_halt_state_halt, halt_state_is_halt_state.
