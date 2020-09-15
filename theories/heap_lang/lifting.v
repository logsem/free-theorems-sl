From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl agree gmap list.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export proph_map.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From intensional Require Export lang.
From intensional Require Import tactics notation.
Set Default Proof Using "Type".

Fixpoint gmap_of_trace {A} (n: nat) (l: list A): gmap nat (agree (leibnizO A)) :=
  match l with
  | nil => ∅
  | x :: l' => <[ n := to_agree x ]> (gmap_of_trace (S n) l')
  end.

Lemma gmap_of_trace_snoc {A} n (l: list A) (a: A):
  gmap_of_trace n (l ++ [a]) =
  <[ (n + length l)%nat := to_agree a ]> (gmap_of_trace n l).
Proof.
  revert n. induction l as [| x l].
  { cbn. intros. by rewrite Nat.add_0_r. }
  { intros. cbn. rewrite IHl /= -Nat.add_succ_r insert_commute //. lia. }
Qed.

Lemma gmap_of_trace_dom {A} (n: nat) (l: list A) k :
  k ∈ dom (gset nat) (gmap_of_trace n l) ↔ (n ≤ k < n + length l)%nat.
Proof.
  revert n. induction l.
  { intros. cbn. rewrite dom_empty_L elem_of_empty. lia. }
  { intros. cbn. rewrite dom_insert_L elem_of_union elem_of_singleton IHl. lia. }
Qed.

Definition eventO := leibnizO event.
Definition traceO := leibnizO (list event).

Class traceG Σ := TraceG {
  trace_hist_inG :> inG Σ (authR (gmapUR nat (agreeR eventO)));
  trace_hist_name : gname;
  trace_inG :> inG Σ (authR (optionUR (exclR traceO)));
  trace_name : gname;
}.

Class trace_preG Σ := TracePreG {
  trace_hist_preG_inG :> inG Σ (authR (gmapUR nat (agreeR eventO)));
  trace_preG_inG :> inG Σ (authR (optionUR (exclR (leibnizO (list event)))));
}.

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_gen_heapG :> gen_heapG loc val Σ;
  heapG_proph_mapG :> proph_mapG proph_id (val * val) Σ;
  heapG_traceG :> traceG Σ;
}.

Definition trace_auth `{hT: traceG Σ} (t: list event) :=
  (own trace_name (● (Excl' (t: traceO))) ∗ own trace_hist_name (● gmap_of_trace 0 t))%I.
Definition hist `{hT: traceG Σ} (t: list event) :=
  own trace_hist_name (◯ (gmap_of_trace 0 t)).
Definition trace_is `{hT: traceG Σ} (t: list event) :=
  (own trace_name (◯ (Excl' (t: traceO))) ∗ hist t)%I.

Instance hist_persistent `{traceG Σ} (t: list event): Persistent (hist t) := _.

Lemma alloc_hist `{traceG Σ} t :
  trace_is t -∗ trace_is t ∗ hist t.
Proof.
  rewrite /trace_is /hist. iIntros "[Htt #Hth]".
  iFrame. iSplit; iAssumption.
Qed.

Lemma trace_agree `{traceG Σ} t t':
  trace_auth t -∗ trace_is t' -∗ ⌜t = t'⌝.
Proof.
  rewrite /trace_auth /trace_is.
  iIntros "[H1 _] [H2 _]".
  iDestruct (own_valid_2 with "H1 H2") as "H".
  iDestruct "H" as %[Hi%Excl_included _]%auth_both_valid.
  eapply leibniz_equiv in Hi; eauto.
Qed.

Lemma trace_is_excl `{traceG Σ} t t' :
  trace_is t -∗ trace_is t' -∗ ⌜ False ⌝.
Proof.
  iIntros "[H1 _] [H2 _]". iDestruct (own_valid_2 with "H1 H2") as %Hv.
  rewrite -auth_frag_op // in Hv.
Qed.

Lemma trace_add_event `{traceG Σ} t (e: event) :
  trace_auth t -∗ trace_is t ==∗ trace_auth (t ++ [e]) ∗ trace_is (t ++ [e]).
Proof.
  rewrite /trace_auth /trace_is /hist.
  iIntros "[H1 H1h] [H2 H2h]".
  iMod (own_update_2 _ _ _ (● Excl' (t++[e]:traceO) ⋅ ◯ Excl' (t++[e]:traceO)) with "H1 H2") as "[? ?]".
  by apply auth_update, option_local_update, exclusive_local_update.
  cbn [gmap_of_trace]. rewrite gmap_of_trace_snoc Nat.add_0_l.
  iMod (own_update_2 with "H1h H2h") as "[? ?]".
  apply auth_update.
  eapply (alloc_local_update _ _ (length t : nat) (to_agree (e:eventO))); [|done].
  { eapply not_elem_of_dom. intros ?%gmap_of_trace_dom. lia. }
  iModIntro. iFrame.
  Unshelve. all: typeclasses eauto.
Qed.

Lemma gmap_of_trace_hist_valid_prefix `{traceG Σ} {A} n (t: list A) h :
  ✓ gmap_of_trace n t →
  gmap_of_trace n h ≼ gmap_of_trace n t →
  h `prefix_of` t.
Proof.
  revert n t. induction h as [| a h].
  { cbn. intros. apply prefix_nil. }
  { intros n t Hv Hsub.
    pose proof (proj1 (lookup_included _ _) Hsub) as Hsub'.
    destruct t as [| e t].
    { exfalso. specialize (Hsub' n).
      rewrite /= lookup_insert lookup_empty in Hsub'.
      apply option_included in Hsub' as [HH|(? & ? & ? & HH & ?)]; inversion HH. }
    specialize (Hsub' n). rewrite /= !lookup_insert in Hsub'.
    eapply (proj1 (Some_included_total _ _)) in Hsub'.
    eapply (proj1 (to_agree_included (a:leibnizO A) e)) in Hsub'.
    apply leibniz_equiv in Hsub'. subst e.
    cbn in Hsub.
    apply (delete_valid _ n) in Hv. rewrite /= delete_insert in Hv.
    2: { eapply not_elem_of_dom. intros ?%gmap_of_trace_dom. lia. }
    assert (gmap_of_trace (S n) h ≼ gmap_of_trace (S n) t).
    { apply lookup_included. intros i.
      eapply (proj1 (lookup_included _ _)) with i in Hsub.
      destruct (decide (i = n)); subst.
      { rewrite (_ : gmap_of_trace (S n) h !! n = None).
        rewrite (_ : gmap_of_trace (S n) t !! n = None) //.
        all: eapply not_elem_of_dom.
        all: intros ?%gmap_of_trace_dom; lia. }
      rewrite !lookup_insert_ne // in Hsub. }
    eapply prefix_cons, IHh; eauto. }
  Unshelve. all: typeclasses eauto.
Qed.

Lemma hist_trace_auth_prefix `{traceG Σ} t h :
  trace_auth t -∗ hist h -∗ ⌜ h `prefix_of` t ⌝.
Proof.
  rewrite /trace_auth /hist. iIntros "[_ H1] H2".
  iDestruct (own_op with "[$H1 $H2]") as "H".
  iDestruct (own_valid with "H") as %[Hsub Hv]%auth_both_valid.
  iPureIntro. eapply gmap_of_trace_hist_valid_prefix; eauto.
Qed.

Instance heapG_irisG `{!heapG Σ} : irisG heap_lang Σ := {
  iris_invG := heapG_invG;
  state_interp σ κs _ :=
    (gen_heap_ctx σ.(heap)
     ∗ trace_auth σ.(trace)
     ∗ proph_map_ctx κs σ.(used_proph_id))%I;
  fork_post _ := True%I;
}.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l 1 v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (head_reducible_no_obs _ _) => eexists _, _, _; simpl : core.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Local Hint Extern 1 (head_step _ _ _ _ _ _) => econstructor : core.
Local Hint Extern 0 (head_step (CmpXchg _ _ _) _ _ _ _ _) => eapply CmpXchgS : core.
Local Hint Extern 0 (head_step (AllocN _ _) _ _ _ _ _) => apply alloc_fresh : core.
Local Hint Extern 0 (head_step NewProph _ _ _ _ _) => apply new_proph_id_fresh : core.
Local Hint Resolve to_of_val : core.

Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

Instance rec_atomic s f x e : Atomic s (Rec f x e).
Proof. solve_atomic. Qed.
Instance pair_atomic s v1 v2 : Atomic s (Pair (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance injl_atomic s v : Atomic s (InjL (Val v)).
Proof. solve_atomic. Qed.
Instance injr_atomic s v : Atomic s (InjR (Val v)).
Proof. solve_atomic. Qed.
(** The instance below is a more general version of [Skip] *)
Instance beta_atomic s f x v1 v2 : Atomic s (App (RecV f x (Val v1)) (Val v2)).
Proof. destruct f, x; solve_atomic. Qed.
Instance unop_atomic s op v : Atomic s (UnOp op (Val v)).
Proof. solve_atomic. Qed.
Instance binop_atomic s op v1 v2 : Atomic s (BinOp op (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance if_true_atomic s v1 e2 : Atomic s (If (Val $ LitV $ LitBool true) (Val v1) e2).
Proof. solve_atomic. Qed.
Instance if_false_atomic s e1 v2 : Atomic s (If (Val $ LitV $ LitBool false) e1 (Val v2)).
Proof. solve_atomic. Qed.
Instance fst_atomic s v : Atomic s (Fst (Val v)).
Proof. solve_atomic. Qed.
Instance snd_atomic s v : Atomic s (Snd (Val v)).
Proof. solve_atomic. Qed.

Instance fork_atomic s e : Atomic s (Fork e).
Proof. solve_atomic. Qed.

Instance alloc_atomic s v w : Atomic s (AllocN (Val v) (Val w)).
Proof. solve_atomic. Qed.
Instance load_atomic s v : Atomic s (Load (Val v)).
Proof. solve_atomic. Qed.
Instance store_atomic s v1 v2 : Atomic s (Store (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance cmpxchg_atomic s v0 v1 v2 : Atomic s (CmpXchg (Val v0) (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance faa_atomic s v1 v2 : Atomic s (FAA (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance emit_atomic s tag v : Atomic s (Emit tag (LitV v)).
Proof. solve_atomic. Qed.

Instance new_proph_atomic s : Atomic s NewProph.
Proof. solve_atomic. Qed.
Instance resolve_atomic s e v1 v2 :
  Atomic s e → Atomic s (Resolve e (Val v1) (Val v2)).
Proof.
  rename e into e1. intros H σ1 e2 κ σ2 efs [Ks e1' e2' Hfill -> step].
  simpl in *. induction Ks as [|K Ks _] using rev_ind; simpl in Hfill.
  - subst. inversion_clear step. by apply (H σ1 (Val v) κs σ2 efs), head_prim_step.
  - rewrite fill_app. rewrite fill_app in Hfill.
    assert (∀ v, Val v = fill Ks e1' → False) as fill_absurd.
    { intros v Hv. assert (to_val (fill Ks e1') = Some v) as Htv by by rewrite -Hv.
      apply to_val_fill_some in Htv. destruct Htv as [-> ->]. inversion step. }
    destruct K; (inversion Hfill; clear Hfill; subst; try
      match goal with | H : Val ?v = fill Ks e1' |- _ => by apply fill_absurd in H end).
    refine (_ (H σ1 (fill (Ks ++ [K]) e2') _ σ2 efs _)).
    + destruct s; intro Hs; simpl in *.
      * destruct Hs as [v Hs]. apply to_val_fill_some in Hs. by destruct Hs, Ks.
      * apply irreducible_resolve. by rewrite fill_app in Hs.
    + econstructor 1 with (K := Ks ++ [K]); try done. simpl. by rewrite fill_app.
Qed.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
Local Ltac solve_pure_exec :=
  subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)
Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Instance pure_recc f x (erec : expr) :
  PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
Proof. solve_pure_exec. Qed.
Instance pure_pairc (v1 v2 : val) :
  PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
Proof. solve_pure_exec. Qed.
Instance pure_injlc (v : val) :
  PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
Proof. solve_pure_exec. Qed.
Instance pure_injrc (v : val) :
  PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
Proof. solve_pure_exec. Qed.

Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
  PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

Instance pure_unop op v v' :
  PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
Proof. solve_pure_exec. Qed.

Instance pure_binop op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
Proof. solve_pure_exec. Qed.
(* Higher-priority instance for [EqOp]. *)
Instance pure_eqop v1 v2 :
  PureExec (vals_compare_safe v1 v2) 1
    (BinOp EqOp (Val v1) (Val v2))
    (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
Proof.
  intros Hcompare.
  cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
  { intros. revert Hcompare. solve_pure_exec. }
  rewrite /bin_op_eval /= decide_True //.
Qed.

Instance pure_if_true e1 e2 : PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
Proof. solve_pure_exec. Qed.

Instance pure_if_false e1 e2 : PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
Proof. solve_pure_exec. Qed.

Instance pure_fst v1 v2 :
  PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
Proof. solve_pure_exec. Qed.

Instance pure_snd v1 v2 :
  PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
Proof. solve_pure_exec. Qed.

Instance pure_case_inl v e1 e2 :
  PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
Proof. solve_pure_exec. Qed.

Instance pure_case_inr v e1 e2 :
  PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
Proof. solve_pure_exec. Qed.

Section lifting.
Context `{!heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

Lemma wp_emit s E tr tag lit :
  {{{ trace_is tr }}}
    Emit tag (LitV lit) @ s; E
  {{{ RET (LitV LitUnit); trace_is (tr ++ [(tag, lit)]) }}}.
Proof.
  iIntros (φ) "Ht Hφ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 κ κs n) "(? & ? & ?) !>"; iSplit; first by eauto.
  iNext. iIntros (v2 σ2 efs Hstep); inv_head_step.
  iDestruct (trace_agree with "[$] [$]") as %?; subst.
  iMod (trace_add_event with "[$] [$]") as "(?&?)".
  iModIntro. iFrame. iSplitL; last done. by iApply "Hφ".
Qed.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 κ κs n) "Hσ !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. by iFrame.
Qed.

Lemma twp_fork s E e Φ :
  WP e @ s; ⊤ [{ _, True }] -∗ Φ (LitV LitUnit) -∗ WP Fork e @ s; E [{ Φ }].
Proof.
  iIntros "He HΦ". iApply twp_lift_atomic_head_step; [done|].
  iIntros (σ1 κs n) "Hσ !>"; iSplit; first by eauto.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step. by iFrame.
Qed.

(** Heap *)
(** The usable rules for [allocN] stated in terms of the [array] proposition
are derived in te file [array]. *)
Lemma heap_array_to_seq_meta l vs (n : nat) :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof.
  iIntros (<-) "Hvs". iInduction vs as [|v vs] "IH" forall (l)=> //=.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma heap_array_to_seq_mapsto l v (n : nat) :
  ([∗ map] l' ↦ v ∈ heap_array l (replicate n v), l' ↦ v) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
Proof.
  iIntros "Hvs". iInduction n as [|n] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma twp_allocN_seq s E v n :
  0 < n →
  [[{ True }]] AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  [[{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }]].
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κs k) "[Hσ Hκs] !>"; iSplit; first by destruct n; auto with lia.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_alloc_gen _ (heap_array l (replicate (Z.to_nat n) v)) with "Hσ")
    as "(Hσ & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite replicate_length Z2Nat.id; auto with lia. }
  iModIntro; do 2 (iSplit; first done). iFrame "Hσ Hκs". iApply "HΦ".
  iApply big_sepL_sep. iSplitL "Hl".
  - by iApply heap_array_to_seq_mapsto.
  - iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
Qed.
Lemma wp_allocN_seq s E v n :
  0 < n →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_allocN_seq; [auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_alloc s E v :
  [[{ True }]] Alloc (Val v) @ s; E [[{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }]].
Proof.
  iIntros (Φ) "_ HΦ". iApply twp_allocN_seq; [auto with lia..|].
  iIntros (l) "/= (? & _)". rewrite loc_add_0. iApply "HΦ"; iFrame.
Qed.
Lemma wp_alloc s E v :
  {{{ True }}} Alloc (Val v) @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_alloc; [auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_load s E l q v :
  [[{ l ↦{q} v }]] Load (Val $ LitV $ LitLoc l) @ s; E [[{ RET v; l ↦{q} v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_load s E l q v :
  {{{ ▷ l ↦{q} v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_load with "H"); [auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_store s E l v' v :
  [[{ l ↦ v' }]] Store (Val $ LitV $ LitLoc l) (Val v) @ s; E
  [[{ RET LitV LitUnit; l ↦ v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_store s E l v' v :
  {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_store with "H"); [auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_fail s E l q v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  [[{ l ↦{q} v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool false); l ↦{q} v' }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_false //.
  iModIntro; iSplit=> //. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_cmpxchg_fail s E l q v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦{q} v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{q} v' }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_fail with "H"); [auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  [[{ l ↦ v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ v2' σ2 efs Hstep); inv_head_step.
  rewrite bool_decide_true //.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_cmpxchg_suc s E l v1 v2 v' :
  v' = v1 → vals_compare_safe v' v1 →
  {{{ ▷ l ↦ v' }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_suc with "H"); [auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_faa s E l i1 i2 :
  [[{ l ↦ LitV (LitInt i1) }]] FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  [[{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ e2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iSplit; first done. iFrame. by iApply "HΦ".
Qed.
Lemma wp_faa s E l i1 i2 :
  {{{ ▷ l ↦ LitV (LitInt i1) }}} FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_faa with "H"); [auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma wp_new_proph s E :
  {{{ True }}}
    NewProph @ s; E
  {{{ pvs p, RET (LitV (LitProphecy p)); proph p pvs }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κ κs n) "[Hσ [Ht HR]] !>". iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep). inv_head_step.
  iMod (proph_map_new_proph p with "HR") as "[HR Hp]"; first done.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

(* In the following, strong atomicity is required due to the fact that [e] must
be able to make a head step for [Resolve e _ _] not to be (head) stuck. *)

Lemma resolve_reducible e σ (p : proph_id) v :
  Atomic StronglyAtomic e → reducible e σ →
  reducible (Resolve e (Val (LitV (LitProphecy p))) (Val v)) σ.
Proof.
  intros A (κ & e' & σ' & efs & H).
  exists (κ ++ [(p, (default v (to_val e'), v))]), e', σ', efs.
  eapply Ectx_step with (K:=[]); try done.
  assert (∃w, Val w = e') as [w <-].
  { unfold Atomic in A. apply (A σ e' κ σ' efs) in H. unfold is_Some in H.
    destruct H as [w H]. exists w. simpl in H. by apply (of_to_val _ _ H). }
  simpl. constructor. by apply prim_step_to_val_is_head_step.
Qed.

Lemma step_resolve e vp vt σ1 κ e2 σ2 efs :
  Atomic StronglyAtomic e →
  prim_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs →
  head_step (Resolve e (Val vp) (Val vt)) σ1 κ e2 σ2 efs.
Proof.
  intros A [Ks e1' e2' Hfill -> step]. simpl in *.
  induction Ks as [|K Ks _] using rev_ind.
  + simpl in *. subst. inversion step. by constructor.
  + rewrite fill_app /= in Hfill. destruct K; inversion Hfill; subst; clear Hfill.
    - assert (fill_item K (fill Ks e1') = fill (Ks ++ [K]) e1') as Eq1;
        first by rewrite fill_app.
      assert (fill_item K (fill Ks e2') = fill (Ks ++ [K]) e2') as Eq2;
        first by rewrite fill_app.
      rewrite fill_app /=. rewrite Eq1 in A.
      assert (is_Some (to_val (fill (Ks ++ [K]) e2'))) as H.
      { apply (A σ1 _ κ σ2 efs). eapply Ectx_step with (K0 := Ks ++ [K]); done. }
      destruct H as [v H]. apply to_val_fill_some in H. by destruct H, Ks.
    - assert (to_val (fill Ks e1') = Some vp); first by rewrite -H1 //.
      apply to_val_fill_some in H. destruct H as [-> ->]. inversion step.
    - assert (to_val (fill Ks e1') = Some vt); first by rewrite -H2 //.
      apply to_val_fill_some in H. destruct H as [-> ->]. inversion step.
Qed.

Lemma wp_resolve s E e Φ (p : proph_id) v (pvs : list (val * val)) :
  Atomic StronglyAtomic e →
  to_val e = None →
  proph p pvs -∗
  WP e @ s; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ proph p pvs' -∗ Φ r }} -∗
  WP Resolve e (Val $ LitV $ LitProphecy p) (Val v) @ s; E {{ Φ }}.
Proof.
  (* TODO we should try to use a generic lifting lemma (and avoid [wp_unfold])
     here, since this breaks the WP abstraction. *)
  iIntros (A He) "Hp WPe". rewrite !wp_unfold /wp_pre /= He. simpl in *.
  iIntros (σ1 κ κs n) "[Hσ Hκ]". destruct κ as [|[p' [w' v']] κ' _] using rev_ind.
  - iMod ("WPe" $! σ1 [] κs n with "[$Hσ $Hκ]") as "[Hs WPe]". iModIntro. iSplit.
    { iDestruct "Hs" as "%". iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). exfalso. apply step_resolve in step; last done.
    inversion step. match goal with H: ?κs ++ [_] = [] |- _ => by destruct κs end.
  - rewrite -app_assoc.
    iMod ("WPe" $! σ1 _ _ n with "[$Hσ $Hκ]") as "[Hs WPe]". iModIntro. iSplit.
    { iDestruct "Hs" as %?. iPureIntro. destruct s; [ by apply resolve_reducible | done]. }
    iIntros (e2 σ2 efs step). apply step_resolve in step; last done.
    inversion step; simplify_list_eq.
    iMod ("WPe" $! (Val w') σ2 efs with "[%]") as "WPe".
    { by eexists [] _ _. }
    iModIntro. iNext. iMod "WPe" as "[[$ [$ Hκ]] WPe]".
    iMod (proph_map_resolve_proph p' (w',v') κs with "[$Hκ $Hp]") as (vs' ->) "[$ HPost]".
    iModIntro. rewrite !wp_unfold /wp_pre /=. iDestruct "WPe" as "[HΦ $]".
    iMod "HΦ". iModIntro. by iApply "HΦ".
Qed.

(** Lemmas for some particular expression inside the [Resolve]. *)
Lemma wp_resolve_proph s E (p : proph_id) (pvs : list (val * val)) v :
  {{{ proph p pvs }}}
    ResolveProph (Val $ LitV $ LitProphecy p) (Val v) @ s; E
  {{{ pvs', RET (LitV LitUnit); ⌜pvs = (LitV LitUnit, v)::pvs'⌝ ∗ proph p pvs' }}}.
Proof.
  iIntros (Φ) "Hp HΦ". iApply (wp_resolve with "Hp"); first done.
  iApply wp_pure_step_later=> //=. iApply wp_value.
  iIntros "!>" (vs') "HEq Hp". iApply "HΦ". iFrame.
Qed.

Lemma wp_resolve_cmpxchg_suc s E l (p : proph_id) (pvs : list (val * val)) v1 v2 v :
  vals_compare_safe v1 v1 →
  {{{ proph p pvs ∗ ▷ l ↦ v1 }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; E
  {{{ RET (v1, #true) ; ∃ pvs', ⌜pvs = ((v1, #true)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦ v2 }}}.
Proof.
  iIntros (Hcmp Φ) "[Hp Hl] HΦ".
  iApply (wp_resolve with "Hp"); first done.
  assert (val_is_unboxed v1) as Hv1; first by destruct Hcmp.
  iApply (wp_cmpxchg_suc with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

Lemma wp_resolve_cmpxchg_fail s E l (p : proph_id) (pvs : list (val * val)) q v' v1 v2 v :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ proph p pvs ∗ ▷ l ↦{q} v' }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; E
  {{{ RET (v', #false) ; ∃ pvs', ⌜pvs = ((v', #false)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦{q} v' }}}.
Proof.
  iIntros (NEq Hcmp Φ) "[Hp Hl] HΦ".
  iApply (wp_resolve with "Hp"); first done.
  iApply (wp_cmpxchg_fail with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

End lifting.
