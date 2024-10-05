Require Import List.
Import ListNotations.
Definition string X := list X.
Definition card X : Type := list X * list X.
Definition stack X := list (card X).
Fixpoint tau1 {X : Type} (A : stack X) : string X := match A with | [] => [] | (x, y) :: A => x ++ tau1 A end.
Fixpoint tau2 {X : Type} (A : stack X) : string X := match A with | [] => [] | (x, y) :: A => y ++ tau2 A end.
Definition PCPX {X : Type}: stack X -> Prop := fun P => exists A, incl A P /\ A <> [] /\ tau1 A = tau2 A.
Definition PCP : stack nat -> Prop := @PCPX nat.
Definition PCPb : stack bool -> Prop := @PCPX bool.
Fixpoint itau1 {X : Type} (P : stack X) (A : list nat) : string X := match A with | [] => [] | i :: A => fst (nth i P ([], [])) ++ itau1 P A end.
Fixpoint itau2 {X : Type} (P : stack X) (A : list nat) : string X := match A with | [] => [] | i :: A => snd (nth i P ([], [])) ++ itau2 P A end.
Definition iPCPb : stack bool -> Prop := fun P => exists (A : list nat), (forall a, In a A -> a < length P) /\ A <> [] /\ itau1 P A = itau2 P A.
Inductive derivable {X : Type} (P : stack X) : string X -> string X -> Prop := | der_sing x y : In (x, y) P -> derivable P x y | der_cons x y u v : In (x, y) P -> derivable P u v -> derivable P (x ++ u) (y ++ v).
Definition dPCP {X : Type} : stack X -> Prop := fun P => exists u, @derivable X P u u.
Definition dPCPb : stack bool -> Prop := @dPCP bool.
Inductive BPCP (P : stack bool) : Prop := | cBPCP : forall u, derivable P u u -> BPCP P.
Hint Constructors BPCP : core.
Definition MPCP : card nat * stack nat -> Prop := fun '((x, y), P) => exists (A : stack nat), incl A ((x, y) :: P) /\ x ++ tau1 A = y ++ tau2 A.
Definition MPCPb : card bool * stack bool -> Prop := fun '((x, y), P) => exists (A : stack bool), incl A ((x, y) :: P) /\ x ++ tau1 A = y ++ tau2 A.