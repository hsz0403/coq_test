Require Import List.
Set Implicit Arguments.
Section Non_deterministic_Minsky_Machines.
Variables loc : Set.
Inductive ndmm2_instr : Set := | ndmm2_stop : loc -> ndmm2_instr | ndmm2_inc : bool -> loc -> loc -> ndmm2_instr | ndmm2_dec : bool -> loc -> loc -> ndmm2_instr | ndmm2_zero : bool -> loc -> loc -> ndmm2_instr.
Notation α := true.
Notation β := false.
Notation STOPₙ := ndmm2_stop.
Notation INCₙ := ndmm2_inc.
Notation DECₙ := ndmm2_dec.
Notation ZEROₙ := ndmm2_zero.
Infix "∊" := In (at level 70).
Reserved Notation "Σ //ₙ a ⊕ b ⊦ u" (at level 70, no associativity).
Inductive ndmm2_accept (Σ : list ndmm2_instr) : nat -> nat -> loc -> Prop := | in_ndmm2a_stop : forall p, STOPₙ p ∊ Σ -> Σ //ₙ 0 ⊕ 0 ⊦ p | in_ndmm2a_inc_a : forall a b p q, INCₙ α p q ∊ Σ -> Σ //ₙ 1+a ⊕ b ⊦ q -> Σ //ₙ a ⊕ b ⊦ p | in_ndmm2a_inc_b : forall a b p q, INCₙ β p q ∊ Σ -> Σ //ₙ a ⊕ 1+b ⊦ q -> Σ //ₙ a ⊕ b ⊦ p | in_ndmm2a_dec_a : forall a b p q, DECₙ α p q ∊ Σ -> Σ //ₙ a ⊕ b ⊦ q -> Σ //ₙ 1+a ⊕ b ⊦ p | in_ndmm2a_dec_b : forall a b p q, DECₙ β p q ∊ Σ -> Σ //ₙ a ⊕ b ⊦ q -> Σ //ₙ a ⊕ 1+b ⊦ p | in_ndmm2a_zero_a : forall b p q, ZEROₙ α p q ∊ Σ -> Σ //ₙ 0 ⊕ b ⊦ q -> Σ //ₙ 0 ⊕ b ⊦ p | in_ndmm2a_zero_b : forall a p q, ZEROₙ β p q ∊ Σ -> Σ //ₙ a ⊕ 0 ⊦ q -> Σ //ₙ a ⊕ 0 ⊦ p where "Σ //ₙ a ⊕ b ⊦ u" := (ndmm2_accept Σ a b u).
Definition ndMM2_problem := { Σ : list ndmm2_instr & loc * (nat * nat) }%type.
Definition ndMM2_ACCEPT (i : ndMM2_problem) : Prop := match i with existT _ Σ (u,(a,b)) => Σ //ₙ a ⊕ b ⊦ u end.
End Non_deterministic_Minsky_Machines.