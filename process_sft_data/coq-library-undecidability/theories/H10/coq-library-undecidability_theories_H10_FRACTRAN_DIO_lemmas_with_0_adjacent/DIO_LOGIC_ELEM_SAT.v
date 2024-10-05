Require Import List.
From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.Shared.Libs.DLW Require Import utils_tac pos vec.
From Undecidability.FRACTRAN Require Import FRACTRAN MM_FRACTRAN.
From Undecidability.H10.Fractran Require Import fractran_dio.
From Undecidability.H10.Dio Require Import dio_elem dio_single dio_logic.
Set Implicit Arguments.
Definition DIO_LOGIC_PROBLEM := (dio_formula * (nat -> nat))%type.
Definition DIO_LOGIC_SAT (p : DIO_LOGIC_PROBLEM) := let (f,ν) := p in df_pred f ν.
Definition DIO_ELEM_PROBLEM := (list dio_constraint * (nat -> nat))%type.
Definition DIO_ELEM_SAT (p : DIO_ELEM_PROBLEM) := let (l,v) := p in exists φ, Forall (dc_eval φ v) l.
Definition DIO_SINGLE_PROBLEM := (dio_single nat nat * (nat -> nat))%type.
Definition DIO_SINGLE_SAT (p : DIO_SINGLE_PROBLEM) := let (E,φ) := p in dio_single_pred E φ.

Theorem DIO_LOGIC_ELEM_SAT : DIO_LOGIC_SAT ⪯ DIO_ELEM_SAT.
Proof.
apply reduces_dependent; exists.
intros (A,v).
destruct (dio_formula_elem A) as (l & _ & _ & Hl).
exists (l,v); apply Hl.
