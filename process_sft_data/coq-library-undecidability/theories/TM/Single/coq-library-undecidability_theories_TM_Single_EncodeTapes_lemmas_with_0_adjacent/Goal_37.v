From Undecidability.TM Require Import ProgrammingTools.
From Undecidability.TM.PrettyBounds Require Export SizeBounds.
From Undecidability Require Import TM.Util.VectorPrelim.
Inductive sigTape (sig : Type) : Type := | LeftBlank (marked : bool) | RightBlank (marked : bool) | NilBlank (* always marked *) | MarkedSymbol (s : sig) | UnmarkedSymbol (s : sig).
Instance sigTape_eq (sig : Type) : eq_dec sig -> eq_dec (sigTape sig).
Proof.
intros.
hnf.
decide equality; now apply Dec; auto.
Defined.
Arguments LeftBlank {sig} marked.
Arguments RightBlank {sig} marked.
Arguments NilBlank {sig}.
Arguments MarkedSymbol {sig}.
Arguments UnmarkedSymbol {sig}.
Instance sigTape_fin (sig : finType) : finTypeC (EqType (sigTape sig)).
Proof.
split with (enum := LeftBlank true :: LeftBlank false :: RightBlank true :: RightBlank false :: NilBlank :: map MarkedSymbol enum ++ map UnmarkedSymbol enum).
intros [ [ | ] | [ | ] | | | ]; cbn; auto.
1-5: f_equal.
1-5: now rewrite <- countSplit, !countMap_zero.
-
rewrite <- countSplit.
rewrite countMap_injective, countMap_zero by congruence.
now rewrite enum_ok.
-
rewrite <- countSplit.
rewrite countMap_injective, countMap_zero by congruence.
now rewrite enum_ok.
Definition isMarked (sig : Type) (s : sigTape sig) : bool := match s with | LeftBlank marked => marked | RightBlank marked => marked | NilBlank => true | MarkedSymbol _ => true | UnmarkedSymbol _ => false end.
Definition isNilBlank {sig : Type} (s : sigTape sig) : bool := match s with NilBlank => true | _ => false end.
Definition isLeftBlank {sig : Type} (s : sigTape sig) : bool := match s with | LeftBlank _ => true | _ => false end.
Definition isVoidBlank {sig : Type} (s : sigTape sig) : bool := match s with | RightBlank _ => true | _ => false end.
Definition isSymbol {sig : Type} (s : sigTape sig) : bool := match s with | UnmarkedSymbol _ | MarkedSymbol _ => true | _ => false end.
Definition encode_tape (sig : Type) (t : tape sig) : list (sigTape sig) := match t with | niltape _ => [NilBlank] | leftof r rs => LeftBlank true :: UnmarkedSymbol r :: map UnmarkedSymbol rs ++ [RightBlank false] | midtape ls m rs => LeftBlank false :: map UnmarkedSymbol (rev ls) ++ MarkedSymbol m :: map UnmarkedSymbol rs ++ [RightBlank false] | rightof l ls => LeftBlank false :: map UnmarkedSymbol (rev ls) ++ [UnmarkedSymbol l; RightBlank true] end.
Instance Encode_tape (sig : Type) : codable (sigTape sig) (tape sig) := {| encode := @encode_tape sig; |}.
Goal forall (sig : Type) (m : move) (t : tape sig), length (encode_tape (tape_move t m)) = length (encode_tape t).
Proof.
intros.
destruct m eqn:E1, t eqn:E2; cbn; auto.
-
now rewrite !app_length.
-
destruct l; cbn; auto.
rewrite !app_length.
f_equal.
rewrite !map_length.
cbn.
rewrite !app_length.
cbn.
lia.
-
destruct l0; cbn; auto.
rewrite !app_length.
f_equal.
rewrite !app_length.
cbn.
rewrite !map_length.
cbn.
rewrite !app_length.
cbn.
lia.
Definition encode_tapes (sig : Type) (n : nat) (t : tapes sig n) := encode_list (@Encode_tape sig) (vector_to_list t).
Arguments encode_tapes {sig n}.
Instance Encode_tapes (sig : Type) (n : nat) : codable (sigList (sigTape sig)) (tapes sig n) := {| encode := @encode_tapes sig n; |}.
Fixpoint split_vector {X : Type} {n : nat} (v : Vector.t X n) (k : nat) : Vector.t X (min k n) * Vector.t X (n-k).
Proof.
destruct k as [ | k']; cbn.
-
split.
apply Vector.nil.
eapply Vector.cast.
apply v.
abstract lia.
-
destruct v as [ | x n' v']; cbn.
+
split.
apply Vector.nil.
apply Vector.nil.
+
specialize (split_vector X n' v' k') as (rec1&rec2).
split.
apply Vector.cons.
apply x.
apply rec1.
apply rec2.
Defined.

Goal forall (sig : Type) (m : move) (t : tape sig), length (encode_tape (tape_move t m)) = length (encode_tape t).
Proof.
intros.
destruct m eqn:E1, t eqn:E2; cbn; auto.
-
now rewrite !app_length.
-
destruct l; cbn; auto.
rewrite !app_length.
f_equal.
rewrite !map_length.
cbn.
rewrite !app_length.
cbn.
lia.
-
destruct l0; cbn; auto.
rewrite !app_length.
f_equal.
rewrite !app_length.
cbn.
rewrite !map_length.
cbn.
rewrite !app_length.
cbn.
lia.
