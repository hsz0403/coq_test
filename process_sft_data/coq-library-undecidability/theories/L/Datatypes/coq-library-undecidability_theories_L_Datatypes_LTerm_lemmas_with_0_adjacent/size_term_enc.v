From Undecidability.L.Datatypes Require Export LNat.
From Undecidability.L Require Export Util.L_facts.
From Undecidability.L.Tactics Require Import LTactics GenEncode.
MetaCoq Run (tmGenEncode "term_enc" term).
Hint Resolve term_enc_correct : Lrewrite.
Instance term_var : computableTime' var (fun n _ => (1, tt)).
Proof.
extract constructor.
solverec.
Instance term_app : computableTime' L.app (fun s1 _ => (1, (fun s2 _ => (1, tt)))).
Proof.
extract constructor.
solverec.
Instance term_lam : computableTime' lam (fun s _ => (1, tt)).
Proof.
extract constructor.
solverec.
Definition c__termsize := c__natsizeS + 7.

Lemma size_term_enc (s:term) : size (enc s) <= size s *c__termsize.
Proof.
induction s;cbv [enc registered_term_enc] in *.
all:cbn [size term_enc] in *.
rewrite size_nat_enc.
all: unfold c__termsize, c__natsizeS, c__natsizeO in *; solverec.
