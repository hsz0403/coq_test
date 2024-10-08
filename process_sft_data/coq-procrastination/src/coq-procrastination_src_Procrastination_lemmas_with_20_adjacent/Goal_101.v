Module Marker.
Definition end_defer (P : Type) := P.
Definition group (P : Prop) := P.
Ltac find_group := match goal with | H : group _ |- _ => constr:(H) end.
End Marker.
Global Opaque Marker.group.
Module MkHelperLemmas.
Ltac transparent_assert name type := unshelve notypeclasses refine (let name := _ : type in _).
Inductive Boxer := | boxer : forall A : Type, A -> Boxer.
Arguments boxer : clear implicits.
Ltac ids_nb ids := lazymatch ids with | tt => constr:(O) | (fun x => _) => let ids' := eval cbv beta in (ids tt) in let n := ids_nb ids' in constr:(S n) end.
Ltac iter_idents ids tac := lazymatch ids with | tt => idtac | (fun x => _) => tac x; iter_idents ltac:(eval cbv beta in (ids tt)) tac end.
Ltac print_ids ids := lazymatch ids with | tt => idtac | (fun x => _) => let ids' := eval cbv beta in (ids tt) in idtac x; print_ids ids' end.
Ltac mk_forall varty goalty n cont := lazymatch n with | O => cont (@nil Boxer) | S ?n' => let X := fresh in refine (forall (X : varty), _ : goalty); mk_forall varty goalty n' ltac:(fun x => cont (cons (boxer varty X) x)) end.
Ltac mk_forall_tys vartys goalty cont := lazymatch vartys with | nil => cont (@nil Boxer) | cons (boxer _ ?ty) ?tys => let X := fresh in refine (forall (X : ty), _ : goalty); mk_forall_tys tys goalty ltac:(fun x => cont (cons (boxer ty X) x)) end.
Ltac mk_arrow vars goalty := lazymatch vars with | nil => idtac | cons (boxer _ ?v) ?vs => refine (v -> _ : goalty); mk_arrow vs goalty end.
Ltac mk_app f vars goalty := lazymatch vars with | nil => exact f | cons (boxer _ ?v) ?vs => refine (_ v : goalty); let x := fresh "x" in intro x; mk_app (f x) vs goalty end.
Ltac mk_sigT_sig ids goalty cont := lazymatch ids with | tt => cont (@nil Boxer) | (fun x => tt) => let X := fresh x in refine (sig (fun (X : _) => _) : goalty); let X_ty := type of X in cont (cons (@boxer X_ty X) (@nil Boxer)) | (fun x => _) => let ids' := eval cbv beta in (ids tt) in let X := fresh x in refine (sigT (fun (X : _) => _) : goalty); let X_ty := type of X in mk_sigT_sig ids' goalty ltac:(fun x => cont (cons (@boxer X_ty X) x)) end.
Ltac mk_exists ids goalty cont := lazymatch ids with | tt => cont (@nil Boxer) | (fun x => _) => let ids' := eval cbv beta in (ids tt) in let X := fresh x in refine (exists (X : _), _ : goalty); let X_ty := type of X in mk_exists ids' goalty ltac:(fun x => cont (cons (@boxer X_ty X) x)) end.
Ltac introsType := repeat ( match goal with | |- forall (_ : Type), _ => intro end ).
Ltac prove_begin_defer_helper := introsType; let H := fresh in intros ? ? ? H; unfold Marker.end_defer in *; repeat (let x := fresh "x" in destruct H as (x & H)); eauto using Marker.group_fold.
Goal forall (g : Prop) (P : Type), (Marker.group g -> P) -> Marker.end_defer g -> P.
Proof.
prove_begin_defer_helper.
Goal forall A (g : A -> Prop) (P : Prop), (forall a, Marker.group (g a) -> P) -> Marker.end_defer (exists a, g a) -> P.
Proof.
prove_begin_defer_helper.
Goal forall A B (g : A -> B -> Prop) (P : Prop), (forall a b, Marker.group (g a b) -> P) -> Marker.end_defer (exists a b, g a b) -> P.
Proof.
prove_begin_defer_helper.
Goal forall A B (g : A -> B -> Prop) (P : Type), (forall a b, Marker.group (g a b) -> P) -> Marker.end_defer {a : A & { b | g a b } } -> P.
Proof.
prove_begin_defer_helper.
Ltac mk_begin_defer_helper_aux n G Pty mk_exists := transparent_assert G Type; [ mk_forall Type Type n ltac:(fun L => let g_ty := fresh "g_ty" in transparent_assert g_ty Type; [ mk_arrow L Type; exact Prop | simpl in g_ty]; let g := fresh "g" in refine (forall (g : g_ty), _ : Type); subst g_ty; let P := fresh "P" in refine (forall (P : Pty), _ : Type); let H1 := fresh "H1" in transparent_assert H1 Type; [ mk_forall_tys L Type ltac:(fun l => let g_args := fresh in transparent_assert g_args Prop; [ mk_app g l Prop | simpl in g_args]; refine (Marker.group g_args -> P : Type) ) | simpl in H1]; let H2 := fresh "H2" in transparent_assert H2 Type; [ refine (Marker.end_defer _ : Type); mk_exists n ltac:(fun l => mk_app g l Prop) | simpl in H2]; exact (H1 -> H2 -> P) ) | simpl in G].
Ltac mk_begin_defer_helper_Type ids G := let n := ids_nb ids in mk_begin_defer_helper_aux n G Type ltac:(fun n cont => mk_sigT_sig ids Type cont).
Ltac mk_begin_defer_helper_Prop ids G := let n := ids_nb ids in mk_begin_defer_helper_aux n G Prop ltac:(fun n cont => mk_exists ids Prop cont).
Ltac mk_begin_defer_helper ids := let H := fresh in match goal with |- ?G => match type of G with | Prop => mk_begin_defer_helper_Prop ids H | _ => mk_begin_defer_helper_Type ids H end; cut H; subst H; [| now prove_begin_defer_helper] end.
Goal True.
mk_begin_defer_helper tt.
intro H; eapply H; clear H.
Abort.
Goal True.
mk_begin_defer_helper (fun a b c : unit => tt).
intro H; eapply H; clear H.
Abort.
Goal nat.
mk_begin_defer_helper (fun a b c : unit => tt).
intro H; eapply H; clear H.
Abort.
Ltac prove_end_defer_helper := introsType; let P1 := fresh in let P2 := fresh in let H1 := fresh in let H2 := fresh in intros P1 P2 H1 H2; unfold Marker.end_defer in *; repeat (let x := fresh "x" in destruct H2 as (x & H2); exists x); apply H1; auto.
Goal forall A (P1 P2 : A -> Prop), (forall a, P1 a -> P2 a) -> (exists a, P1 a) -> Marker.end_defer (exists a, P2 a).
Proof.
prove_end_defer_helper.
Goal forall A B (P1 P2 : A -> B -> Prop), (forall a b, P1 a b -> P2 a b) -> (exists a b, P1 a b) -> Marker.end_defer (exists a b, P2 a b).
Proof.
prove_end_defer_helper.
Goal forall A (P1 P2 : A -> Prop), (forall a, P1 a -> P2 a) -> { a | P1 a } -> Marker.end_defer { a | P2 a }.
Proof.
prove_end_defer_helper.
Ltac mk_end_defer_helper_aux n G mk_exists := transparent_assert G Type; [ mk_forall Type Type n ltac:(fun L => let P_ty := fresh "P_ty" in transparent_assert P_ty Type; [ mk_arrow L Type; exact Prop | simpl in P_ty ]; let P1 := fresh "P1" in let P2 := fresh "P2" in refine (forall (P1 P2 : P_ty), _ : Type); subst P_ty; let H1 := fresh "H1" in transparent_assert H1 Type; [ mk_forall_tys L Type ltac:(fun l => refine (_ -> _ : Type); [ mk_app P1 l Type | mk_app P2 l Type ] ) | simpl in H1 ]; refine (H1 -> _ -> Marker.end_defer _ : Type); [ mk_exists n ltac:(fun l => mk_app P1 l Prop) | mk_exists n ltac:(fun l => mk_app P2 l Prop) ] ) | simpl in G].
Ltac mk_end_defer_helper_Type ids G := let n := ids_nb ids in mk_end_defer_helper_aux n G ltac:(fun n cont => mk_sigT_sig ids Type cont).
Ltac mk_end_defer_helper_Prop ids G := let n := ids_nb ids in mk_end_defer_helper_aux n G ltac:(fun n cont => mk_exists ids Prop cont).
Ltac mk_end_defer_helper ids := let H := fresh in match goal with |- Marker.end_defer ?G => match type of G with | Prop => mk_end_defer_helper_Prop ids H | _ => mk_end_defer_helper_Type ids H end; cut H; subst H; [| prove_end_defer_helper ] end.
Goal Marker.end_defer nat.
mk_end_defer_helper (fun x y z : unit => tt).
intros.
Abort.
Goal Marker.end_defer True.
mk_end_defer_helper (fun x y z : unit => tt).
Abort.
End MkHelperLemmas.
Ltac specialize_helper_types H ids := MkHelperLemmas.iter_idents ids ltac:(fun _ => let e := fresh in evar (e : Type); specialize (H e); subst e ).
Ltac mkrefine_group ids := lazymatch ids with | tt => uconstr:(_) | (fun x => _) => let ids' := eval cbv beta in (ids tt) in let ret := mkrefine_group ids' in uconstr:(fun x => ret) end.
Ltac specialize_helper_group H ids := let group_uconstr := mkrefine_group ids in let g := fresh in refine (let g := group_uconstr in _); specialize (H g); subst g.
Ltac begin_defer_core g ids := MkHelperLemmas.mk_begin_defer_helper ids; let H := fresh in intro H; specialize_helper_types H ids; specialize_helper_group H ids; eapply H; clear H; [ MkHelperLemmas.iter_idents ids ltac:(fun x => intro x); intro g |].
Tactic Notation "begin" "defer" := let g := fresh "g" in begin_defer_core g tt.
Tactic Notation "begin" "defer" "in" ident(g) := begin_defer_core g tt.
Tactic Notation "begin" "defer" "assuming" ident(a) := let g := fresh "g" in begin_defer_core g (fun a : unit => tt).
Tactic Notation "begin" "defer" "assuming" ident(a) "in" ident(g) := begin_defer_core g (fun a : unit => tt).
Tactic Notation "begin" "defer" "assuming" ident(a) ident(b) := let g := fresh "g" in begin_defer_core g (fun a b : unit => tt).
Tactic Notation "begin" "defer" "assuming" ident(a) ident(b) "in" ident(g) := begin_defer_core g (fun a b : unit => tt).
Tactic Notation "begin" "defer" "assuming" ident(a) ident(b) ident(c) := let g := fresh "g" in begin_defer_core g (fun a b c : unit => tt).
Tactic Notation "begin" "defer" "assuming" ident(a) ident(b) ident(c) "in" ident(g) := begin_defer_core g (fun a b c : unit => tt).
Tactic Notation "begin" "defer" "assuming" ident(a) ident(b) ident(c) ident(d) := let g := fresh "g" in begin_defer_core g (fun a b c d : unit => tt).
Tactic Notation "begin" "defer" "assuming" ident(a) ident(b) ident(c) ident(d) "in" ident(g) := begin_defer_core g (fun a b c d : unit => tt).
Tactic Notation "begin" "defer" "assuming" ident(a) ident(b) ident(c) ident(d) ident(e) := let g := fresh "g" in begin_defer_core g (fun a b c d e : unit => tt).
Tactic Notation "begin" "defer" "assuming" ident(a) ident(b) ident(c) ident(d) ident(e) "in" ident(g) := begin_defer_core g (fun a b c d e : unit => tt).
Goal True.
begin defer assuming a b in foo.
Abort.
Goal nat.
begin defer assuming a b in foo.
Abort.
Ltac defer_aux tm ty := let ty' := (eval hnf in ty) in lazymatch ty' with | and ?x ?y => defer_aux (@proj2 x y tm) y | _ => eapply (proj1 tm) end.
Ltac defer_core group := let ty := type of group in match ty with | Marker.group ?G => defer_aux group G end.
Tactic Notation "defer" "in" ident(g) := defer_core g.
Tactic Notation "defer" := let g := Marker.find_group in defer in g.
Tactic Notation "defer" simple_intropattern(H) ":" uconstr(E) "in" ident(g) := assert E as H by defer_core g.
Tactic Notation "defer" ":" uconstr(E) "in" ident(g) := let H := fresh in defer H : E in g; revert H.
Tactic Notation "defer" simple_intropattern(H) ":" uconstr(E) := let g := Marker.find_group in defer H : E in g.
Tactic Notation "defer" ":" uconstr(E) := let g := Marker.find_group in defer: E in g.
Goal True.
begin defer in foo.
begin defer in bar.
assert (1 = 1) by defer.
defer HH: (2 = 2).
defer: (3 = 3).
intros ?.
defer _: (4 = 4) in foo.
defer [E1 E2]: (5 = 5 /\ 6 = 6) in foo.
Abort.
Ltac deferred_exploit_aux tm ty tac := lazymatch ty with | and ?x ?y => try tac (@proj1 x y tm); tryif is_evar y then idtac else deferred_exploit_aux (@proj2 x y tm) y tac end.
Ltac deferred_exploit_core g tac := let ty := type of g in match ty with | Marker.group ?G => progress (deferred_exploit_aux g G tac) end.
Tactic Notation "deferred" "exploit" tactic(tac) "in" ident(g) := deferred_exploit_core g tac.
Tactic Notation "deferred" "exploit" tactic(tac) := let g := Marker.find_group in deferred exploit tac in g.
Goal True.
begin defer in foo.
defer ?: (1 + 1 = 2).
defer L: (forall n, n + 0 = n).
clear L.
assert (3 + 0 = 3).
{
deferred exploit (fun H => rewrite H).
reflexivity.
}
Abort.
Ltac deferred_core g := deferred exploit (fun H => generalize H) in g.
Tactic Notation "deferred" "in" ident(g) := deferred_core g.
Tactic Notation "deferred" := let g := Marker.find_group in deferred in g.
Tactic Notation "deferred" simple_intropattern(H) ":" uconstr(E) "in" ident(g) := assert E as H; [ deferred in g; try now auto |].
Tactic Notation "deferred" ":" uconstr(E) "in" ident(g) := let H := fresh in assert E as H; [ deferred in g; try now auto | revert H ].
Tactic Notation "deferred" simple_intropattern(H) ":" uconstr(E) := let g := Marker.find_group in deferred H : E in g.
Tactic Notation "deferred" ":" uconstr(E) := let g := Marker.find_group in deferred : E in g.
Goal True.
begin defer.
defer _: (1 + 1 = 2).
defer _: (1 + 2 = 3).
deferred.
intros _ _.
Abort.
Goal True.
begin defer assuming n.
defer _: (1+2=3).
defer _: (n + 1 = n).
deferred ?: (n = n + 1); [].
deferred: (n + 2 = n).
{
intros.
admit.
}
intros ?.
Abort.
Ltac introv_rec := lazymatch goal with | |- (?P -> ?Q) => idtac | |- (forall _, _) => intro; introv_rec | |- _ => idtac end.
Ltac cleanup_conj_goal_aux tm ty := lazymatch ty with | and ?x ?y => tryif is_evar y then (split; [refine tm | exact I]) else (split; [refine (@proj1 x _ tm) | cleanup_conj_goal_aux uconstr:(@proj2 x _ tm) y]) end.
Ltac cleanup_conj_goal_core := let H_P_clean := fresh "H_P_clean" in intro H_P_clean; match goal with | |- ?P => cleanup_conj_goal_aux H_P_clean P end.
Ltac collect_exists_ids_loop G ids := lazymatch G with | (fun g => exists x, @?body g x) => collect_exists_ids_aux ids x body | (fun g => { x & @?body g x }) => collect_exists_ids_aux ids x body | (fun g => { x | @?body g x }) => collect_exists_ids_aux ids x body | _ => constr:(ids) end with collect_exists_ids_aux ids x body := let G' := constr:(fun (z : _ * _) => body (fst z) (snd z)) in let G' := eval cbn beta in G' in let ids' := collect_exists_ids_loop G' ids in constr:(fun (x : unit) => ids').
Ltac collect_exists_ids g := collect_exists_ids_loop (fun (_:unit) => g) tt.
Goal Marker.end_defer (exists a b c, a + b = c).
match goal with |- Marker.end_defer ?g => let ids := collect_exists_ids g in (* MkHelperLemmas.print_ids ids; *) (* prints: a b c *) idtac end.
Abort.
Goal Marker.end_defer { a & { b & { c | a + b = c } } }.
match goal with |- Marker.end_defer ?g => let ids := collect_exists_ids g in (* MkHelperLemmas.print_ids ids; *) (* prints: a b c *) idtac end.
Abort.
Ltac end_defer_core := match goal with |- Marker.end_defer ?g => let ids := collect_exists_ids g in MkHelperLemmas.mk_end_defer_helper ids; let H := fresh in intro H; eapply H; clear H; [ introv_rec; cleanup_conj_goal_core | hnf ] end.
Tactic Notation "end" "defer" := end_defer_core.
Goal True.
begin defer in g.
defer H1: (1 + 1 = 2).
defer H2: (1 + 2 = 3).
defer H3: (1 + 3 = 4) in g.
tauto.
end defer.
do 3 split.
Goal True.
begin defer assuming a b c.
assert (a + b = c).
defer.
exact I.
end defer.
Abort.
Goal nat.
begin defer assuming a b c.
assert (a + b = c).
defer.
exact 0.
end defer.
Abort.
Goal 1= 2 /\ 2=3.
begin defer.
defer.
end defer.
Abort.
Notation "'end' 'defer'" := (Marker.end_defer _) (at level 0).
Notation "'Group' P" := (Marker.group P) (at level 0).

Lemma group_fold : forall (P: Prop), P -> group P.
Proof.
Admitted.

Goal forall (g : Prop) (P : Type), (Marker.group g -> P) -> Marker.end_defer g -> P.
Proof.
Admitted.

Goal forall A (g : A -> Prop) (P : Prop), (forall a, Marker.group (g a) -> P) -> Marker.end_defer (exists a, g a) -> P.
Proof.
Admitted.

Goal forall A B (g : A -> B -> Prop) (P : Prop), (forall a b, Marker.group (g a b) -> P) -> Marker.end_defer (exists a b, g a b) -> P.
Proof.
Admitted.

Goal forall A B (g : A -> B -> Prop) (P : Type), (forall a b, Marker.group (g a b) -> P) -> Marker.end_defer {a : A & { b | g a b } } -> P.
Proof.
Admitted.

Goal True.
mk_begin_defer_helper tt.
Admitted.

Goal True.
mk_begin_defer_helper (fun a b c : unit => tt).
Admitted.

Goal nat.
mk_begin_defer_helper (fun a b c : unit => tt).
Admitted.

Goal forall A (P1 P2 : A -> Prop), (forall a, P1 a -> P2 a) -> (exists a, P1 a) -> Marker.end_defer (exists a, P2 a).
Proof.
Admitted.

Goal forall A B (P1 P2 : A -> B -> Prop), (forall a b, P1 a b -> P2 a b) -> (exists a b, P1 a b) -> Marker.end_defer (exists a b, P2 a b).
Proof.
Admitted.

Goal forall A (P1 P2 : A -> Prop), (forall a, P1 a -> P2 a) -> { a | P1 a } -> Marker.end_defer { a | P2 a }.
Proof.
Admitted.

Goal Marker.end_defer nat.
mk_end_defer_helper (fun x y z : unit => tt).
Admitted.

Goal Marker.end_defer True.
Admitted.

Goal True.
Admitted.

Goal True.
begin defer in foo.
begin defer in bar.
assert (1 = 1) by defer.
defer HH: (2 = 2).
defer: (3 = 3).
intros ?.
defer _: (4 = 4) in foo.
Admitted.

Goal True.
begin defer in foo.
defer ?: (1 + 1 = 2).
defer L: (forall n, n + 0 = n).
clear L.
assert (3 + 0 = 3).
{
deferred exploit (fun H => rewrite H).
reflexivity.
Admitted.

Goal True.
begin defer.
defer _: (1 + 1 = 2).
defer _: (1 + 2 = 3).
deferred.
Admitted.

Goal True.
begin defer assuming n.
defer _: (1+2=3).
defer _: (n + 1 = n).
deferred ?: (n = n + 1); [].
deferred: (n + 2 = n).
{
intros.
admit.
}
Admitted.

Goal Marker.end_defer (exists a b c, a + b = c).
Admitted.

Goal Marker.end_defer { a & { b & { c | a + b = c } } }.
Admitted.

Goal True.
begin defer in g.
defer H1: (1 + 1 = 2).
defer H2: (1 + 2 = 3).
defer H3: (1 + 3 = 4) in g.
tauto.
end defer.
Admitted.

Goal True.
begin defer assuming a b c.
assert (a + b = c).
defer.
exact I.
Admitted.

Goal nat.
begin defer assuming a b c.
assert (a + b = c).
defer.
exact 0.
Admitted.

Goal 1= 2 /\ 2=3.
begin defer.
defer.
Admitted.

Goal nat.
begin defer assuming a b in foo.
