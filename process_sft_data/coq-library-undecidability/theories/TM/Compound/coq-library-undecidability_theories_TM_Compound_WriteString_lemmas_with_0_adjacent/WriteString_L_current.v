From Undecidability Require Import TM.Util.TM_facts TM.Basic.Mono TM.Combinators.Combinators TM.Compound.Multi.
Require Import List.
From Undecidability Require Import TMTac.
From Coq Require Import List.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Section Write_String.
Variable sig : finType.
Variable D : move.
Fixpoint WriteString (l : list sig) : pTM sig unit 1 := match l with | [] => Nop | [x] => Write x | x :: xs => WriteMove x D;; WriteString xs end.
Fixpoint WriteString_Fun (sig' : Type) (t : tape sig') (str : list sig') := match str with | nil => t | [x] => tape_write t (Some x) | x :: str' => WriteString_Fun (doAct t (Some x, D)) str' end.
Fixpoint WriteString_sem_fix (str : list sig) : pRel sig unit 1 := match str with | nil => Nop_Rel | [x] => Write_Rel x | x :: str' => WriteMove_Rel x D |_tt ∘ WriteString_sem_fix str' end.
Definition WriteString_steps l := 2 * l - 1.
Definition WriteString_Rel str : Rel (tapes sig 1) (unit * tapes sig 1) := Mono.Mk_R_p (ignoreParam (fun tin tout => tout = WriteString_Fun tin str)).
End Write_String.
Arguments WriteString : simpl never.
Arguments WriteString_Rel {sig} (D) (str) x y/.

Lemma WriteString_L_current (sig : Type) (str : list sig) t : current (WriteString_Fun Lmove t str) = hd None (map Some (rev str ++ tape_local t)).
Proof.
revert t.
induction str as [ | s [ | s' str'] IH]; intros; cbn in *.
-
now destruct t.
-
reflexivity.
-
rewrite IH.
autorewrite with list.
setoid_rewrite app_assoc at 1 2.
rewrite !hd_app with (xs:=(map Some (rev str') ++ map Some [s'])).
easy.
all:intros (?&[=])%app_eq_nil.
