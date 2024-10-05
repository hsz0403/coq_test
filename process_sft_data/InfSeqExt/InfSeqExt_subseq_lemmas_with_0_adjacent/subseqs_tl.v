Require Import InfSeqExt.infseq.
Require Import InfSeqExt.exteq.
Section sec_subseq.
Variable T: Type.
Inductive suff (s : infseq T) : infseq T -> Prop := | sp_eq : suff s s | sp_next : forall x s0, suff s s0 -> suff s (Cons x s0).
CoInductive subseq : infseq T -> infseq T -> Prop := | Subseq : forall s s0 s1, suff s1 s0 -> subseq s (tl s1) -> subseq (Cons (hd s1) s) s0.
CoInductive subseqs' : infseq (infseq T) -> infseq T -> Prop := | Subseqs' : forall si s0 s1, suff s1 s0 -> subseqs' si (tl s1) -> subseqs' (Cons s1 si) s0.
CoInductive subseqs : infseq (infseq T) -> infseq T -> Prop := | Subseqs : forall si s, suff (hd si) s -> subseqs (tl si) (tl (hd si)) -> subseqs si s.
Inductive ex_suff (P: infseq T -> Prop) (s' : infseq T) : Prop := Esp : forall s, suff s s' -> P s -> ex_suff P s'.
Inductive suff_exteq (s : infseq T) : infseq T -> Prop := | sb_eq : forall s', exteq s s' -> suff_exteq s s' | sb_next : forall x s', suff_exteq s s' -> suff_exteq s (Cons x s').
Inductive suffb (x : T) (s : infseq T) : infseq T -> Prop := | sp_eqb : forall s', exteq (Cons x s) s' -> suffb x s s' | sp_nextb : forall y s', suffb x s s' -> suffb x s (Cons y s').
CoInductive subseqb : infseq T -> infseq T -> Prop := | Subseqb : forall x s s', suffb x s s' -> subseqb s s' -> subseqb (Cons x s) s'.
Inductive mem (x : T) : infseq T -> Prop := | mem0 : forall s, mem x (Cons x s) | mem_next : forall y s, mem x s -> mem x (Cons y s).
End sec_subseq.

Lemma subseqs_tl : forall si s, subseqs si (tl s) -> subseqs si s.
Proof using.
intros si (x, s) su.
simpl in su.
case su.
clear su si s; intros si s sf su.
constructor.
-
constructor 2.
exact sf.
-
exact su.
