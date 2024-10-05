Require Import List Lia.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Require Import Undecidability.HilbertCalculi.HSC.
Require Import Undecidability.HilbertCalculi.Util.HSCFacts.
Require Import Undecidability.PCP.PCP.
Set Default Goal Selector "!".
Module Argument.
Local Arguments incl_cons_inv {A a l m}.
Local Arguments incl_cons {A a l m}.
Definition bullet := var 0.
Definition b2 := (arr bullet bullet).
Definition b3 := arr bullet (arr bullet bullet).
Fixpoint append_word (s: formula) (v: list bool) := match v with | [] => s | a :: v => if a then append_word (arr b2 s) v else append_word (arr b3 s) v end.
Definition encode_word (v: list bool) := append_word bullet v.
Definition encode_pair (s t: formula) := arr b3 (arr s (arr t b3)).
Local Notation "⟨ s , t ⟩" := (encode_pair s t).
Local Notation "⟦ v ⟧" := (encode_word v).
Local Notation "s → t" := (arr s t) (at level 50).
Definition Γ v w P := (encode_pair (var 1) (var 1)) :: (arr (encode_pair (encode_word v) (encode_word w)) a_b_a) :: map (fun '(v, w) => arr (encode_pair (append_word (var 2) v) (append_word (var 3) w)) (encode_pair (var 2) (var 3))) ((v, w) :: P).
Definition ΓPCP := [ (* ((Q, P), (x, x)) *) encode_pair (var 1) (encode_pair (var 2) (var 2)); (* ((P, P), ((x, v'), (y, w'))) → ((((v', w'), Q), P), ((x, •), (y, •))) *) arr (encode_pair (encode_pair (var 4) (var 4)) (encode_pair (encode_pair (var 5) (var 1)) (encode_pair (var 6) (var 2)))) (encode_pair (encode_pair (encode_pair (encode_pair (var 1) (var 2)) (var 3)) (var 4)) (encode_pair (encode_pair (var 5) bullet) (encode_pair (var 6) bullet))); (* ((Q, P), (x, y)) → ((((v', w'), Q), P), (x, y)) *) arr (encode_pair (encode_pair (var 2) (var 3)) (var 4)) (encode_pair (encode_pair (encode_pair (var 1) (var 2)) (var 3)) (var 4)); (* ((Q, P), ((x, a), v'), y) → ((Q, P), ((x, (a, v')), y) *) arr (encode_pair (var 1) (encode_pair (encode_pair (encode_pair (var 2) (var 3)) (var 4)) (var 5))) (encode_pair (var 1) (encode_pair (encode_pair (var 2) (encode_pair (var 3) (var 4))) (var 5))); (* ((Q, P), (x, ((y, a), w')) → ((Q, P), (x, (y, (a, w'))) *) arr (encode_pair (var 1) (encode_pair (var 5) (encode_pair (encode_pair (var 2) (var 3)) (var 4)))) (encode_pair (var 1) (encode_pair (var 5) (encode_pair (var 2) (encode_pair (var 3) (var 4))))) ].
Definition encode_bool b := if b then b2 else b3.
Fixpoint encode_list {X: Type} (encode_X: X -> formula) (A: list X) : formula := match A with | [] => bullet | a :: A => encode_pair (encode_X a) (encode_list encode_X A) end.
Fixpoint encode_word' (s: formula) (v: list bool) := match v with | [] => s | a :: v => encode_word' (encode_pair s (if a then b2 else b3)) v end.
Definition encode_word_pair '(x, y) := encode_pair (encode_list encode_bool x) (encode_list encode_bool y).
Definition PCPf P x y := encode_pair (encode_pair (encode_list encode_word_pair P) (encode_list encode_word_pair P)) (encode_pair (encode_pair (encode_word' bullet x) bullet) (encode_pair (encode_word' bullet y) bullet)).
Definition PCPf' Q P s t := encode_pair (encode_pair (encode_list encode_word_pair Q) (encode_list encode_word_pair P)) (encode_pair s t).
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma hscI {Gamma ζ s t} : In s Gamma -> t = substitute ζ s -> hsc Gamma t.
Proof.
by move=> /hsc_var + ->.
