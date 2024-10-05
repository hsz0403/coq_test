Require Export Pminus.
Require Export DivTerm.
Section Pspminus.
Load hCoefStructure.
Load hOrderStructure.
Load hMinus.
Hint Resolve divP_is_not_order : core.
Definition spminusf (a b : Term A n) (nZb : ~ zeroP (A:=A) A0 eqA (n:=n) b) (p q : list (Term A n)) := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec p (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) a (b:=b) nZb) q).
Hint Resolve canonical_spminusf : core.
Hint Resolve canonical_spminusf_full : core.
Hint Resolve canonical_spminusf_full_t : core.
Hint Resolve spminusf_pluspf : core.
Hint Resolve eqTerm_spminusf_com eqp_spminusf_com eqp_spminusf_com : core.
Hint Resolve spminusf_plusTerm spminusf_multTerm : core.
Hint Resolve spminusf_minusTerm_r : core.
Hint Resolve spminusf_plusTerm_r : core.
Hint Resolve divP_minusTerm_comp : core.
Hint Resolve spminusf_minusTerm : core.
Hint Resolve spminusf_minusTerm : core.
End Pspminus.

Theorem spminusf_multTerm : forall (a b c : Term A n) (nZc : ~ zeroP (A:=A) A0 eqA (n:=n) c) (p q : list (Term A n)), canonical A0 eqA ltM p -> canonical A0 eqA ltM q -> divP A A0 eqA multA divA n b c -> ~ zeroP (A:=A) A0 eqA (n:=n) a -> eqP A eqA n (spminusf (multTerm (A:=A) multA (n:=n) a b) c nZc (mults (A:=A) multA (n:=n) a p) q) (mults (A:=A) multA (n:=n) a (spminusf b c nZc p q)).
intros a b c nZc p q H' H'0 H'1 H'2; unfold spminusf in |- *.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) (multTerm (A:=A) multA (n:=n) a (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=c) nZc)) q)); [ auto | idtac ].
apply minuspf_comp with (1 := cs); auto.
apply canonical_mults with (1 := cs); auto.
apply nzeroP_comp_eqTerm with (1 := cs) (a := multTerm (A:=A) multA (n:=n) a (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=c) nZc)); auto.
apply (eqTerm_sym _ _ _ _ _ _ _ _ _ cs n); apply divTerm_multTerm_l with (1 := cs).
inversion H'1; auto.
apply (eqp_trans _ _ _ _ _ _ _ _ _ cs n) with (y := minuspf A A0 A1 eqA invA minusA multA eqA_dec n ltM ltM_dec (mults (A:=A) multA (n:=n) a p) (mults (A:=A) multA (n:=n) a (mults (A:=A) multA (n:=n) (divTerm (A:=A) (A0:=A0) (eqA:=eqA) divA (n:=n) b (b:=c) nZc) q))); [ auto | idtac ].
apply (eqp_sym _ _ _ _ _ _ _ _ _ cs n); apply mults_dist_minuspf with (1 := cs); auto.
