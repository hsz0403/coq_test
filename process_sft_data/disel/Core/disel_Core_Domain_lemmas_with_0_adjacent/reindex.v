From mathcomp.ssreflect Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From fcsl Require Import axioms pred prelude.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Poset.
Section RawMixin.
Record mixin_of (T : Type) := Mixin { mx_leq : T -> T -> Prop; _ : forall x, mx_leq x x; _ : forall x y, mx_leq x y -> mx_leq y x -> x = y; _ : forall x y z, mx_leq x y -> mx_leq y z -> mx_leq x z}.
End RawMixin.
Section ClassDef.
Record class_of T := Class {mixin : mixin_of T}.
Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Definition pack (m0 : mixin_of T) := fun m & phant_id m0 m => Pack (@Class T m) T.
Definition leq := mx_leq (mixin class).
End ClassDef.
Module Exports.
Coercion sort : type >-> Sortclass.
Notation poset := Poset.type.
Notation PosetMixin := Poset.Mixin.
Notation Poset T m := (@pack T _ m id).
Notation "[ 'poset' 'of' T 'for' cT ]" := (@clone T cT _ id) (at level 0, format "[ 'poset' 'of' T 'for' cT ]") : form_scope.
Notation "[ 'poset' 'of' T ]" := (@clone T _ _ id) (at level 0, format "[ 'poset' 'of' T ]") : form_scope.
Notation "x <== y" := (Poset.leq x y) (at level 70).
Section Laws.
Variable T : poset.
End Laws.
Hint Resolve poset_refl : core.
Add Parametric Relation (T : poset) : T (@Poset.leq T) reflexivity proved by (@poset_refl _) transitivity proved by (fun x y => @poset_trans _ y x) as poset_rel.
End Exports.
End Poset.
Export Poset.Exports.
Definition monotone (T1 T2 : poset) (f : T1 -> T2) := forall x y, x <== y -> f x <== f y.
Section IdealDef.
Variable T : poset.
Structure ideal (P : T) := Ideal {id_val : T; id_pf : id_val <== P}.
Definition relax (P1 P2 : T) (x : ideal P1) (pf : P1 <== P2) := Ideal (relaxP pf (id_pf x)).
End IdealDef.
Section SubPoset.
Variables (T : poset) (s : Pred T).
Local Notation tp := {x : T | x \In s}.
Definition sub_leq (p1 p2 : tp) := sval p1 <== sval p2.
Definition subPosetMixin := PosetMixin sub_refl sub_asym sub_trans.
Definition subPoset := Eval hnf in Poset tp subPosetMixin.
End SubPoset.
Section PairPoset.
Variable (A B : poset).
Local Notation tp := (A * B)%type.
Definition pair_leq (p1 p2 : tp) := p1.1 <== p2.1 /\ p1.2 <== p2.2.
Definition pairPosetMixin := PosetMixin pair_refl pair_asym pair_trans.
Canonical pairPoset := Eval hnf in Poset tp pairPosetMixin.
End PairPoset.
Section FunPoset.
Variable (A : Type) (B : poset).
Local Notation tp := (A -> B).
Definition fun_leq (p1 p2 : tp) := forall x, p1 x <== p2 x.
Definition funPosetMixin := PosetMixin fun_refl fun_asym fun_trans.
Canonical funPoset := Eval hnf in Poset tp funPosetMixin.
End FunPoset.
Section DFunPoset.
Variables (A : Type) (B : A -> poset).
Local Notation tp := (forall x, B x).
Definition dfun_leq (p1 p2 : tp) := forall x, p1 x <== p2 x.
Definition dfunPosetMixin := PosetMixin dfun_refl dfun_asym dfun_trans.
Definition dfunPoset := Eval hnf in Poset tp dfunPosetMixin.
End DFunPoset.
Section IdealPoset.
Variable (T : poset) (P : T).
Definition ideal_leq (p1 p2 : ideal P) := id_val p1 <== id_val p2.
Definition idealPosetMixin := PosetMixin ideal_refl ideal_asym ideal_trans.
Canonical idealPoset := Eval hnf in Poset (ideal P) idealPosetMixin.
End IdealPoset.
Section PropPoset.
Definition prop_leq (p1 p2 : Prop) := p1 -> p2.
Definition propPosetMixin := PosetMixin prop_refl prop_asym prop_trans.
Canonical propPoset := Eval hnf in Poset Prop propPosetMixin.
End PropPoset.
Module Lattice.
Section RawMixin.
Variable T : poset.
Record mixin_of := Mixin { mx_sup : Pred T -> T; _ : forall (s : Pred T) x, x \In s -> x <== mx_sup s; _ : forall (s : Pred T) x, (forall y, y \In s -> y <== x) -> mx_sup s <== x}.
End RawMixin.
Section ClassDef.
Record class_of (T : Type) := Class { base : Poset.class_of T; mixin : mixin_of (Poset.Pack base T)}.
Local Coercion base : class_of >-> Poset.class_of.
Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Definition pack b0 (m0 : mixin_of (Poset.Pack b0 T)) := fun m & phant_id m0 m => Pack (@Class T b0 m) T.
Definition sup (s : Pred cT) : cT := mx_sup (mixin class) s.
Definition poset := Poset.Pack class cT.
End ClassDef.
Module Exports.
Coercion base : class_of >-> Poset.class_of.
Coercion sort : type >-> Sortclass.
Coercion poset : type >-> Poset.type.
Canonical Structure poset.
Notation lattice := Lattice.type.
Notation LatticeMixin := Lattice.Mixin.
Notation Lattice T m := (@pack T _ _ m id).
Notation "[ 'lattice' 'of' T 'for' cT ]" := (@clone T cT _ id) (at level 0, format "[ 'lattice' 'of' T 'for' cT ]") : form_scope.
Notation "[ 'lattice' 'of' T ]" := (@clone T _ _ id) (at level 0, format "[ 'lattice' 'of' T ]") : form_scope.
Arguments Lattice.sup [cT].
Prenex Implicits Lattice.sup.
Notation sup := Lattice.sup.
Section Laws.
Variable T : lattice.
End Laws.
End Exports.
End Lattice.
Export Lattice.Exports.
Section Infimum.
Variable T : lattice.
Definition inf (s : Pred T) := sup [Pred x : T | forall y, y \In s -> x <== y].
End Infimum.
Section Lat.
Variable T : lattice.
Definition lbot : T := sup Pred0.
Definition tarski_lfp (f : T -> T) := inf [Pred x : T | f x <== x].
Definition tarski_gfp (f : T -> T) := sup [Pred x : T | x <== f x].
Definition sup_closed (T : lattice) := [Pred s : Pred T | forall d, d <=p s -> sup d \In s].
Definition sup_closure (T : lattice) (s : Pred T) := [Pred p : T | forall t : Pred T, s <=p t -> t \In sup_closed T -> p \In t].
End Lat.
Arguments lbot {T}.
Arguments sup_closed {T}.
Arguments sup_closure [T].
Prenex Implicits sup_closed sup_closure.
Section BasicProperties.
Variable T : lattice.
End BasicProperties.
Section SubLattice.
Variables (T : lattice) (s : Pred T) (C : sup_closed s).
Local Notation tp := (subPoset s).
Definition sub_sup' (u : Pred tp) : T := sup [Pred x : T | exists y, y \In u /\ x = sval y].
Definition sub_sup (u : Pred tp) : tp := exist _ (sub_sup' u) (sub_supX u).
Definition subLatticeMixin := LatticeMixin sub_supP sub_supM.
Definition subLattice := Eval hnf in Lattice {x : T | x \In s} subLatticeMixin.
End SubLattice.
Section PairLattice.
Variables (A B : lattice).
Local Notation tp := (A * B)%type.
Definition pair_sup (s : Pred tp) : tp := (sup [Pred p | exists f, p = f.1 /\ f \In s], sup [Pred p | exists f, p = f.2 /\ f \In s]).
Definition pairLatticeMixin := LatticeMixin pair_supP pair_supM.
Canonical pairLattice := Eval hnf in Lattice tp pairLatticeMixin.
End PairLattice.
Section FunLattice.
Variables (A : Type) (B : lattice).
Local Notation tp := (A -> B).
Definition fun_sup (s : Pred tp) : tp := fun x => sup [Pred p | exists f, f \In s /\ p = f x].
Definition funLatticeMixin := LatticeMixin fun_supP fun_supM.
Canonical funLattice := Eval hnf in Lattice tp funLatticeMixin.
End FunLattice.
Section DFunLattice.
Variables (A : Type) (B : A -> lattice).
Local Notation tp := (dfunPoset B).
Definition dfun_sup (s : Pred tp) : tp := fun x => sup [Pred p | exists f, f \In s /\ p = f x].
Definition dfunLatticeMixin := LatticeMixin dfun_supP dfun_supM.
Definition dfunLattice := Eval hnf in Lattice (forall x, B x) dfunLatticeMixin.
End DFunLattice.
Section IdealLattice.
Variables (T : lattice) (P : T).
Definition ideal_sup' (s : Pred (ideal P)) := sup [Pred x | exists p, p \In s /\ id_val p = x].
Definition ideal_sup (s : Pred (ideal P)) := Ideal (ideal_supP' s).
Definition idealLatticeMixin := LatticeMixin ideal_supP ideal_supM.
Canonical idealLattice := Eval hnf in Lattice (ideal P) idealLatticeMixin.
End IdealLattice.
Section PropLattice.
Definition prop_sup (s : Pred Prop) : Prop := exists p, p \In s /\ p.
Definition propLatticeMixin := LatticeMixin prop_supP prop_supM.
Canonical propLattice := Eval hnf in Lattice Prop propLatticeMixin.
End PropLattice.
Arguments id_mono [T].
Prenex Implicits id_mono.
Arguments const_mono [T1 T2 y].
Prenex Implicits const_mono.
Arguments comp_mono [T1 T2 T3 f1 f2].
Prenex Implicits comp_mono.
Arguments proj1_mono [T1 T2].
Arguments proj2_mono [T1 T2].
Prenex Implicits proj1_mono proj2_mono.
Arguments diag_mono [T].
Prenex Implicits diag_mono.
Arguments app_mono [A T].
Prenex Implicits app_mono.
Arguments dapp_mono [A T].
Prenex Implicits dapp_mono.
Arguments prod_mono [S1 S2 T1 T2 f1 f2].
Prenex Implicits prod_mono.
Section Chains.
Variable T : poset.
Definition chain_axiom (s : Pred T) := (exists d, d \In s) /\ (forall x y, x \In s -> y \In s -> x <== y \/ y <== x).
Structure chain := Chain { pred_of :> Pred T; _ : chain_axiom pred_of}.
Canonical chainPredType := @mkPredType T chain pred_of.
End Chains.
Section ImageChain.
Variables (T1 T2 : poset) (s : chain T1) (f : T1 -> T2) (M : monotone f).
Definition image_chain := Chain image_chainP.
End ImageChain.
Notation "[ f '^^' s 'by' M ]" := (@image_chain _ _ s f M) (at level 0, format "[ f '^^' s 'by' M ]") : form_scope.
Section ChainId.
Variables (T : poset) (s : chain T).
End ChainId.
Section ChainConst.
Variables (T1 T2 : poset) (y : T2).
Definition const_chain := Chain const_chainP.
End ChainConst.
Section ChainCompose.
Variables (T1 T2 T3 : poset) (f1 : T2 -> T1) (f2 : T3 -> T2).
Variables (s : chain T3) (M1 : monotone f1) (M2 : monotone f2).
End ChainCompose.
Section ProjChain.
Variables (T1 T2 : poset) (s : chain [poset of T1 * T2]).
Definition proj1_chain := [@fst _ _ ^^ s by proj1_mono].
Definition proj2_chain := [@snd _ _ ^^ s by proj2_mono].
End ProjChain.
Section DiagChain.
Variable (T : poset) (s : chain T).
Definition diag_chain := [_ ^^ s by @diag_mono T].
End DiagChain.
Section AppChain.
Variables (A : Type) (T : poset) (s : chain [poset of A -> T]).
Definition app_chain x := [_ ^^ s by app_mono x].
End AppChain.
Section DAppChain.
Variables (A : Type) (T : A -> poset) (s : chain (dfunPoset T)).
Definition dapp_chain x := [_ ^^ s by dapp_mono x].
End DAppChain.
Section ProdChain.
Variables (S1 S2 T1 T2 : poset) (f1 : S1 -> T1) (f2 : S2 -> T2).
Variables (M1 : monotone f1) (M2 : monotone f2).
Variable (s : chain [poset of S1 * S2]).
Definition prod_chain := [f1 \* f2 ^^ s by prod_mono M1 M2].
End ProdChain.
Module CPO.
Section RawMixin.
Record mixin_of (T : poset) := Mixin { mx_bot : T; mx_lim : chain T -> T; _ : forall x, mx_bot <== x; _ : forall (s : chain T) x, x \In s -> x <== mx_lim s; _ : forall (s : chain T) x, (forall y, y \In s -> y <== x) -> mx_lim s <== x}.
End RawMixin.
Section ClassDef.
Record class_of (T : Type) := Class { base : Poset.class_of T; mixin : mixin_of (Poset.Pack base T)}.
Local Coercion base : class_of >-> Poset.class_of.
Structure type : Type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Definition pack b0 (m0 : mixin_of (Poset.Pack b0 T)) := fun m & phant_id m0 m => Pack (@Class T b0 m) T.
Definition poset := Poset.Pack class cT.
Definition lim (s : chain poset) : cT := mx_lim (mixin class) s.
Definition bot : cT := mx_bot (mixin class).
End ClassDef.
Module Import Exports.
Coercion base : class_of >-> Poset.class_of.
Coercion sort : type >-> Sortclass.
Coercion poset : type >-> Poset.type.
Canonical Structure poset.
Notation cpo := type.
Notation CPOMixin := Mixin.
Notation CPO T m := (@pack T _ _ m id).
Notation "[ 'cpo' 'of' T 'for' cT ]" := (@clone T cT _ idfun) (at level 0, format "[ 'cpo' 'of' T 'for' cT ]") : form_scope.
Notation "[ 'cpo' 'of' T ]" := (@clone T _ _ id) (at level 0, format "[ 'cpo' 'of' T ]") : form_scope.
Arguments CPO.bot {cT}.
Arguments CPO.lim [cT].
Prenex Implicits CPO.lim.
Prenex Implicits CPO.bot.
Notation lim := CPO.lim.
Notation bot := CPO.bot.
Section Laws.
Variable D : cpo.
End Laws.
End Exports.
End CPO.
Export CPO.Exports.
Hint Resolve botP : core.
Section LiftChain.
Variable (D : cpo) (s : chain D).
Hint Resolve botP : core.
Definition lift_chain := Chain lift_chainP.
End LiftChain.
Section PairCPO.
Variables (A B : cpo).
Local Notation tp := [poset of A * B].
Definition pair_bot : tp := (bot, bot).
Definition pair_lim (s : chain tp) : tp := (lim (proj1_chain s), lim (proj2_chain s)).
Definition pairCPOMixin := CPOMixin pair_botP pair_limP pair_limM.
Canonical pairCPO := Eval hnf in CPO (A * B) pairCPOMixin.
End PairCPO.
Section FunCPO.
Variable (A : Type) (B : cpo).
Local Notation tp := [poset of A -> B].
Definition fun_bot : tp := fun x => bot.
Definition fun_lim (s : chain tp) : tp := fun x => lim (app_chain s x).
Definition funCPOMixin := CPOMixin fun_botP fun_limP fun_limM.
Canonical funCPO := Eval hnf in CPO (A -> B) funCPOMixin.
End FunCPO.
Section DFunCPO.
Variable (A : Type) (B : A -> cpo).
Local Notation tp := (dfunPoset B).
Definition dfun_bot : tp := fun x => bot.
Definition dfun_lim (s : chain tp) : tp := fun x => lim (dapp_chain s x).
Definition dfunCPOMixin := CPOMixin dfun_botP dfun_limP dfun_limM.
Definition dfunCPO := Eval hnf in CPO (forall x, B x) dfunCPOMixin.
End DFunCPO.
Section PropCPO.
Local Notation tp := [poset of Prop].
Definition prop_bot : tp := False.
Definition prop_lim (s : chain tp) : tp := exists p, p \In s /\ p.
Definition propCPOMixin := CPOMixin prop_botP prop_limP prop_limM.
Canonical propCPO := Eval hnf in CPO Prop propCPOMixin.
End PropCPO.
Section PredCPO.
Variable A : Type.
Definition predCPOMixin := funCPOMixin A propCPO.
Canonical predCPO := Eval hnf in CPO (Pred A) predCPOMixin.
End PredCPO.
Section LatticeCPO.
Variable A : lattice.
Local Notation tp := (Lattice.poset A).
Definition lat_bot : tp := lbot.
Definition lat_lim (s : chain tp) : tp := sup s.
Definition latCPOMixin := CPOMixin lat_botP lat_limP lat_limM.
Definition latCPO := Eval hnf in CPO tp latCPOMixin.
End LatticeCPO.
Section AdmissibleClosure.
Variable T : cpo.
Definition chain_closed := [Pred s : Pred T | bot \In s /\ forall d : chain T, d <=p s -> lim d \In s].
Definition chain_closure (s : Pred T) := [Pred p : T | forall t : Pred T, s <=p t -> chain_closed t -> p \In t].
End AdmissibleClosure.
Arguments chain_closed {T}.
Prenex Implicits chain_closed.
Section SubCPO.
Variables (D : cpo) (s : Pred D) (C : chain_closed s).
Local Notation tp := (subPoset s).
Definition sub_bot := exist _ (@bot D) (proj1 C).
Definition sub_lim (u : chain tp) : tp := exist _ (lim [sval ^^ u by sval_mono]) (sub_limX u).
Definition subCPOMixin := CPOMixin sub_botP sub_limP sub_limM.
Definition subCPO := Eval hnf in CPO {x : D | x \In s} subCPOMixin.
End SubCPO.
Section Continuity.
Variables (D1 D2 : cpo) (f : D1 -> D2).
Definition continuous := exists M : monotone f, forall s : chain D1, f (lim s) = lim [f ^^ s by M].
End Continuity.
Module Kleene.
Section NatPoset.
Definition natPosetMixin := PosetMixin nat_refl nat_asym nat_trans.
Canonical natPoset := Eval hnf in Poset nat natPosetMixin.
End NatPoset.
Section NatChain.
Definition nat_chain := Chain nat_chain_axiom.
End NatChain.
Section Kleene.
Variables (D : cpo) (f : D -> D) (C : continuous f).
Fixpoint pow m := if m is n.+1 then f (pow n) else bot.
Definition pow_chain := [pow ^^ nat_chain by pow_mono].
Definition kleene_lfp := lim pow_chain.
End Kleene.
Module Exports.
Notation kleene_lfp := kleene_lfp.
Notation kleene_lfp_fixed := kleene_lfp_fixed.
Notation kleene_lfp_least := kleene_lfp_least.
End Exports.
End Kleene.
Export Kleene.Exports.
Arguments id_cont {D}.
Prenex Implicits id_cont.
Arguments const_cont {D1 D2 y}.
Prenex Implicits const_cont.
Arguments comp_cont [D1 D2 D3 f1 f2].
Prenex Implicits comp_cont.
Arguments proj1_cont {D1 D2}.
Arguments proj2_cont {D1 D2}.
Prenex Implicits proj1_cont proj2_cont.
Arguments diag_cont {D}.
Prenex Implicits diag_cont.
Arguments app_cont [A D].
Arguments dapp_cont [A D].
Prenex Implicits app_cont dapp_cont.
Arguments prod_cont [S1 S2 T1 T2 f1 f2].
Prenex Implicits prod_cont.

Lemma reindex : pow_chain =p lift_chain [f ^^ pow_chain by cont_mono C].
Proof.
move=>x; split.
-
case; case=>[|n][->] /=; first by left.
by right; exists (pow n); split=>//; exists n.
case=>/=; first by move=>->; exists 0.
by case=>y [->][n][->]; exists n.+1.
