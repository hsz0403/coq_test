From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import TM.Code.CaseNat TM.Code.CaseSum TM.Code.CaseFin LM_heap_def .
From Undecidability.TM.L Require Import Alphabets.
Definition CaseCom : pTM sigCom^+ (option ACom) 1 := If (CaseSum _ _) (Return Nop None) (Relabel (ChangeAlphabet (CaseFin (FinType(EqType(ACom))) ) _) Some).
Definition CaseCom_size (t : Tok) : nat -> nat := match t with | varT n => S | _ => S >> S >> S end.
Definition CaseCom_Rel : pRel sigCom^+ (FinType (EqType (option ACom))) 1 := fun tin '(yout, tout) => forall (t : Tok) (s : nat), tin[@Fin0] ≃(;s) t -> match yout with | Some c => isVoid_size tout[@Fin0] (CaseCom_size t s) /\ ACom2Com c = t | None => exists n, t = varT n /\ tout[@Fin0] ≃(;CaseCom_size t s) n end.
Definition CaseCom_steps := 11.
Definition Constr_ACom (t : ACom) : pTM sigCom^+ unit 1 := WriteValue (ACom2Com t).
Definition Constr_ACom_Rel (t : ACom) : pRel sigCom^+ unit 1 := Mk_R_p (ignoreParam (fun tin tout => isVoid tin -> tout ≃ ACom2Com t)).
Definition Constr_ACom_steps := 7.
Definition Constr_varT : pTM sigCom^+ unit 1 := Constr_inl _ _.
Definition Constr_varT_Rel : pRel sigCom^+ (FinType (EqType unit)) 1 := Mk_R_p (ignoreParam (fun tin tout => forall (x : nat) (s : nat), tin ≃(;s) x -> tout ≃(;pred s) varT x)).
Definition Constr_varT_steps := 3.
Arguments CaseCom : simpl never.
Arguments Constr_ACom : simpl never.
Arguments Constr_varT : simpl never.
From Undecidability Require Import Hoare.
Ltac hstep_Com := lazymatch goal with | [ |- TripleT ?P ?k CaseCom ?Q ] => eapply CaseCom_SpecT_size | [ |- TripleT ?P ?k Constr_varT ?Q ] => eapply Constr_varT_SpecT_size end.
Smpl Add hstep_Com : hstep_Spec.

Lemma Constr_varT_Sem : Constr_varT ⊨c(Constr_varT_steps) Constr_varT_Rel.
Proof.
unfold Constr_varT_steps.
eapply RealiseIn_monotone.
-
unfold Constr_varT.
apply Constr_inl_Sem.
-
reflexivity.
-
intros tin ((), tout) H.
intros n s HEncN.
TMSimp.
modpon H.
auto.
