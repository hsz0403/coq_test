Require Import Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes.
Require Import Vector List.
Unset Implicit Arguments.
Section Fix_Sigma.
Variable Σ : Type.
Inductive tape : Type := | niltape : tape | leftof : Σ -> list Σ -> tape | rightof : Σ -> list Σ -> tape | midtape : list Σ -> Σ -> list Σ -> tape.
Definition current (t : tape) : option Σ := match t with | midtape _ a _ => Some a | _ => None end.
Inductive move : Type := Lmove : move | Rmove : move | Nmove : move.
Definition mv (m : move) (t : tape) := match m, t with | Lmove, rightof l ls => midtape ls l nil | Lmove, midtape nil m rs => leftof m rs | Lmove, midtape (l :: ls) m rs => midtape ls l (m :: rs) | Rmove, leftof r rs => midtape nil r rs | Rmove, midtape ls m nil => rightof m ls | Rmove, midtape ls m (r :: rs) => midtape (m :: ls) r rs | _, _ => t end.
Definition wr (s : option Σ) (t : tape) : tape := match s, t with | None, t => t | Some a, niltape => midtape nil a nil | Some a, leftof r rs => midtape nil a (r :: rs) | Some a, midtape ls b rs => midtape ls a rs | Some a, rightof l ls => midtape (l :: ls) a nil end.
End Fix_Sigma.
Arguments niltape _, {_}.
Arguments leftof _ _ _, {_} _ _.
Arguments rightof _ _ _, {_} _ _.
Arguments midtape _ _ _ _, {_} _ _ _.
Arguments current {_} _.
Arguments wr {_} _ _.
Arguments mv {_} _.
Section Fix_Alphabet.
Variable Σ : finType.
Variable n : nat.
Record TM : Type := { (* type of states of the TM: *) state : finType; (* transition function: *) trans : state * (Vector.t (option Σ) n) -> state * (Vector.t ((option Σ) * move) n); (* start state: *) start: state; (* decidable subset of halting states: *) halt : state -> bool }.
Inductive eval (M : TM) (q : state M) (t : Vector.t (tape Σ) n) : state M -> Vector.t (tape Σ) n -> Prop := | eval_halt : halt M q = true -> eval M q t q t | eval_step q' a q'' t' : halt M q = false -> trans M (q, Vector.map current t) = (q', a) -> eval M q' (Vector.map2 (fun tp '(c,m) => mv m (wr c tp)) t a) q'' t' -> eval M q t q'' t'.
End Fix_Alphabet.
Arguments state {_ _} m : rename.
Arguments trans {_ _} m _, {_ _ m} _ : rename.
Arguments start {_ _} m : rename.
Arguments halt {_ _} m _, {_ _ m} _ : rename.
Arguments eval {_ _} _ _ _ _ _.
Arguments Build_TM {_ _ _} _ _ _.
Definition HaltsTM {Σ: finType} {n: nat} (M : TM Σ n) (t : Vector.t (tape Σ) n) := exists q' t', eval M (start M) t q' t'.
Arguments HaltsTM _ _ _ _, {_ _} _ _.
Definition HaltTM (n : nat) : {Σ : finType & TM Σ n & Vector.t (tape Σ) n} -> Prop := fun '(existT2 _ _ Σ M t) => HaltsTM M t.
Definition HaltMTM : {'(n,Σ) : nat * finType & TM Σ n & Vector.t (tape Σ) n} -> Prop := fun '(existT2 _ _ (n, Σ) M t) => HaltsTM M t.