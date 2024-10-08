Set Implicit Arguments.
Module Type ExprLang.
Parameter Var: Type -> Type.
Parameter Expr: Type -> Type.
Parameter Env: Type.
Parameter upd: forall (A:Type), (Var A) -> A -> Env -> Env.
Parameter eval: forall (A:Type), (Expr A) -> Env -> A.
End ExprLang.
Module Type HoareLogicDefs.
Declare Module E: ExprLang.
Inductive ImpProg: Type := | Iskip: ImpProg | Iset (A:Type) (x:E.Var A) (expr:E.Expr A): ImpProg | Iif (cond:E.Expr bool) (p1 p2:ImpProg): ImpProg | Iseq (p1 p2:ImpProg): ImpProg | Iwhile (cond:E.Expr bool) (p:ImpProg): ImpProg.
Inductive exec: E.Env -> ImpProg -> E.Env -> Prop := | exec_Iskip: forall e, (exec e Iskip e) | exec_Iset: forall (A:Type) e x (expr: E.Expr A), (exec e (Iset x expr) (E.upd x (E.eval expr e) e)) | exec_Iif: forall e (cond: E.Expr bool) p1 p2 e', (exec e (if (E.eval cond e) then p1 else p2) e') -> (exec e (Iif cond p1 p2) e') | exec_Iseq: forall e p1 p2 e' e'', (exec e p1 e') -> (exec e' p2 e'') -> (exec e (Iseq p1 p2) e'') | exec_Iwhile: forall e cond p e', (exec e (Iif cond (Iseq p (Iwhile cond p)) Iskip) e') -> (exec e (Iwhile cond p) e').
Definition Pred := E.Env -> Prop.
Notation "p |= q" := (forall e, (p e) -> (q e)) (at level 80, no associativity).
Definition wlp: ImpProg -> Pred -> Pred := fun prog post e => (forall e', (exec e prog e') -> (post e')).
Notation "p {= post =}" := (wlp p post) (at level 70).
Definition wp: ImpProg -> Pred -> Pred := fun prog post e => exists e', (exec e prog e') /\ (post e').
Notation "p [= post =]" := (wp p post) (at level 70).
Hint Resolve exec_Iskip exec_Iset exec_Iif exec_Iseq exec_Iwhile: hoare.
Parameter exec_Iif_true: forall e cond p1 p2 e', (E.eval cond e)=true -> (exec e p1 e') -> (exec e (Iif cond p1 p2) e').
Parameter exec_Iif_false: forall e cond p1 p2 e', (E.eval cond e)=false -> (exec e p2 e') -> (exec e (Iif cond p1 p2) e').
Hint Resolve exec_Iif_true exec_Iif_false: hoare.
End HoareLogicDefs.
Module Type HoareProofSystem.
Declare Module HLD: HoareLogicDefs.
Import HLD.
Parameter sem_wp: ImpProg -> Pred -> Pred.
Parameter synt_wp: ImpProg -> Pred -> Pred.
Parameter soundness: forall pre p post, pre |= (synt_wp p post) -> pre |= (sem_wp p post).
Parameter completeness: forall pre p post, pre |= (sem_wp p post) -> pre |= (synt_wp p post).
End HoareProofSystem.
Module Type HoareLogicSem.
Declare Module E: ExprLang.
Declare Module HLD: HoareLogicDefs with Module E:=E.
Import HLD.
Declare Module PHL: HoareProofSystem with Module HLD:=HLD with Definition sem_wp:=wlp.
Declare Module THL: HoareProofSystem with Module HLD:=HLD with Definition sem_wp:=wp.
Parameter wp_entails_wlp: forall prog post, prog [= post =] |= prog {= post =}.
End HoareLogicSem.