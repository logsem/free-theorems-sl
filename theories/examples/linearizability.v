From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl excl_auth gmap.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From intensional.heap_lang Require Import lifting proofmode notation.
From intensional.heap_lang Require Import adequacy.
From intensional.examples Require Import stdpp_extra iris_extra trace_helpers.
Set Default Proof Using "Type".
Implicit Types t : list val.

(** ** A concurrent specification using logically atomic triples (Section 6) *)

(** *** Separation logic specification *)

(** The Separation Logic specification is parameterized by:
    - a mathematical model of the data structure ([model] below)
    - two Separation Logic representation predicates [is_P] and [P_state] ([repr] below).
      - [is_P γ v] asserts that the value [v] is a valid instance of the
        structure, associated with the logical name [γ]. It is a persistent
        assertion. (It is named [IsP] in the paper.)
      - [P_state γ s] asserts that the current state of the data structure
        with ghost name [γ] is [s]. It is not a persistent assertion as it
        allows updating the state of the structure with operation [op].
        (It is named [PState] in the paper.)
*)

(** *** *)

(** The mathematical model of a data structure exposing a single operation,
   where:
   - [f s v s'] specifies that calling the operation on a structure at state [s]
     with argument [v] results in an updated state [s'];
   - [r s v v'] specifies that calling the operation on a structure at state [s]
     with argument [v] produces a result value [v']. *)
(** _NOTE_: [f] and [r] are here taken to be relations, whereas they are functions
   in the paper. This is a small generalization that has otherwise no impact on
   the proof. *)
Class model := {
  S : Type;
  s_init : S;
  f : S → val → S → Prop;
  r : S → val → val → Prop;
}.

(** The representation predicates [is_P] and [P_state]. *)
Record repr {Σ: gFunctors} `{model} := {
  is_P: gname → val → iProp Σ;
  P_state: gname → S → iProp Σ;
  is_P_persistent : ∀ γ x, Persistent (is_P γ x);
}.

Arguments repr Σ {_}.
#[export] Hint Resolve is_P_persistent : typeclass_instances.

Section Specs.
Context `{!heapGS Σ}.
Context `{model} (R: repr Σ).
Context (E: coPset).

Definition init_spec P0 (init: val) : iProp Σ :=
  {{{ P0 }}} init #() {{{ γ r, RET r; is_P R γ r ∗ P_state R γ s_init }}}.

(** The specification for the concurrent operation [op]. [<<< _ >>> _ <<< _ >>>]
    denotes a logically atomic triple. *)
Definition op_spec (op: val) : iProp Σ :=
  ∀ γ (x y: val),
    is_P R γ x -∗
    <<< ∀ s, P_state R γ s >>>
      op x y @ E
    <<< ∃ s' y', P_state R γ s' ∗ ⌜f s y s' ∧ r s y y'⌝, RET y' >>>.

End Specs.

Definition lib_spec `{model} (E: coPset) `{!heapGS Σ} (P0: iProp Σ) (lib: val) :
    iProp Σ :=
  ∃ (R: repr Σ),
  match lib with
  | (init, op)%V => init_spec R P0 init ∗ op_spec R E op
  | _ => False
  end.

(** *** The trace property [linearizable]: "concurrent calls to [op] are linearizable" *)

Section Trace.

Inductive linearization_trace : list val → Prop :=
  | linearization_trace_nil :
      linearization_trace []
  | linearization_trace_call (tag: string) (v: val) t :
      linearization_trace t →
      linearization_trace (t ++ [(#tag, (#"call", v))%V])
  | linearization_trace_lin (tag: string) (v v': val) t :
      linearization_trace t →
      linearization_trace (t ++ [(#tag, (#"lin", (v, v')))%V])
  | linearization_trace_ret (tag: string) (v v': val) t :
      linearization_trace t →
      linearization_trace (t ++ [(#tag, (#"ret", (v, v')))%V]).

(* whether lin events are sound wrt the model *)
Inductive linearized_sound `{model} : list val → S → S → Prop :=
  | linearized_sound_nil s :
      linearized_sound [] s s
  | linearized_sound_lin s0 s s' (tag:string) v v' t :
      linearized_sound t s0 s →
      r s v v' →
      f s v s' →
      linearized_sound (t ++ [(#tag, (#"lin", (v, v')))%V]) s0 s'.

Definition per_tag_linearized (t: list val) :=
  ∀ tag, ∃ v v',
        filter (check_tag tag) t
          `prefix_of`
        [(#tag, (#"call", v))%V;
         (#tag, (#"lin", (v, v')))%V;
         (#tag, (#"ret", (v, v')))%V].

Definition is_call_return (v: val) :=
  match v with
  | (#_, (#"call", _))%V | (#_, (#"ret", _))%V => true
  | _ => false
  end.

Definition is_lin (v: val) :=
  match v with
  | (#_, (#"lin", _))%V => true
  | _ => false
  end.

Definition linearizable `{model} t :=
  ∃ t', linearization_trace t'
        ∧ per_tag_linearized t'
        ∧ t = filter is_call_return t'
        ∧ ∃ s', linearized_sound (filter is_lin t') s_init s'.

(* lemmas about the linearizability notions above *)

Lemma linearizable_nil `{model}: linearizable [].
Proof.
  exists []. split_and!.
  { constructor. }
  { intros. exists #(), #(). apply prefix_nil. }
  { reflexivity. }
  { exists s_init. constructor. }
Qed.

Lemma per_tag_linearized_prefix t t' :
  per_tag_linearized t' →
  t `prefix_of` t' →
  per_tag_linearized t.
Proof.
  unfold per_tag_linearized. intros Ht' [l ->].
  intros tag. specialize (Ht' tag) as (v & v' & Ht'). exists v, v'.
  rewrite filter_app in Ht'. by apply prefix_app_l in Ht'.
Qed.

Lemma linearization_fresh_tag_call_ret t tag :
  linearization_trace t →
  per_tag_linearized t →
  tag ∉ tags (filter is_call_return t) →
  tag ∉ tags t.
Proof.
  intros Hl. revert tag. induction Hl. done.
  all: rewrite filter_app !tags_app.
  { intros tag0 Htl [Hf1 Hf2]%not_elem_of_app. apply not_elem_of_app. split.
    - apply IHHl; auto. eapply per_tag_linearized_prefix; eauto.
      by eapply prefix_app_r.
    - cbn. intros HH%elem_of_list_singleton. subst. apply Hf2.
      cbn. destruct (decide True); last done. cbn.
      by apply elem_of_list_singleton. }
  { intros tag0 Htl [Hf1 Hf2]%not_elem_of_app. apply not_elem_of_app. split.
    - apply IHHl; auto. eapply per_tag_linearized_prefix; eauto.
      by eapply prefix_app_r.
    - clear Hf2. pose proof Htl as Htl'.
      unfold per_tag_linearized in Htl. specialize (Htl tag0) as [v0 [v'0 Htl]].
      rewrite filter_app in Htl. rewrite (filter_is_nil _ t) in Htl; last first.
      { apply fresh_tag_nocheck. apply IHHl; eauto.
        eapply per_tag_linearized_prefix; eauto. by eapply prefix_app_r. }
      destruct (decide (tag0 = tag)).
      + subst. rewrite filter_check_single_tag_eq in Htl. cbn in Htl.
        destruct Htl as (? & HHH). inversion HHH.
      + subst. intros HH. by apply elem_of_list_singleton in HH. }
  { intros tag0 Htl [Hf1 Hf2]%not_elem_of_app. apply not_elem_of_app. split.
    - apply IHHl; auto. eapply per_tag_linearized_prefix; eauto.
      by eapply prefix_app_r.
    - cbn. intros HH%elem_of_list_singleton. subst. apply Hf2.
      cbn. destruct (decide True); last done. cbn.
      by apply elem_of_list_singleton. }
Qed.

Lemma per_tag_linearized_add_call t (tag:string) v:
  per_tag_linearized t →
  tag ∉ tags t →
  per_tag_linearized (t ++ [(#tag, (#"call", v))%V]).
Proof.
  intros Htl Htag. intro tag'.
  specialize (Htl tag') as (v0 & v0' & Htl).
  rewrite filter_app.
  destruct (decide (tag = tag')).
  { subst. exists v, v(*dummy*).
    rewrite (filter_is_nil _ t). 2: by apply fresh_tag_nocheck.
    rewrite filter_check_single_tag_eq /=. apply prefix_cons, prefix_nil. }
  { exists v0, v0'. rewrite filter_check_single_tag_neq // app_nil_r //. }
Qed.

Lemma per_tag_linearized_add_lin t (tag:string) v v':
  per_tag_linearized t →
  filter (λ v, check_tag tag v) t = [(#tag, (#"call", v))%V] →
  per_tag_linearized (t ++ [(#tag, (#"lin", (v, v')))%V]).
Proof.
  intros Htl Hft. intro tag'.
  specialize (Htl tag') as (v0 & v0' & Htl).
  rewrite filter_app.
  destruct (decide (tag = tag')).
  { subst. exists v, v'. rewrite Hft filter_check_single_tag_eq.
    repeat apply prefix_cons. apply prefix_nil. }
  { exists v0, v0'. rewrite filter_check_single_tag_neq // app_nil_r //. }
Qed.

Lemma per_tag_linearized_add_ret t (tag:string) v v':
  per_tag_linearized t →
  filter (λ v, check_tag tag v) t =
    [(#tag, (#"call", v))%V; (#tag, (#"lin", (v, v')))%V] →
  per_tag_linearized (t ++ [(#tag, (#"ret", (v, v')))%V]).
Proof.
  intros Htl Hft. intro tag'.
  specialize (Htl tag') as (v0 & v0' & Htl).
  rewrite filter_app.
  destruct (decide (tag = tag')).
  { subst. exists v, v'. rewrite Hft filter_check_single_tag_eq.
    repeat apply prefix_cons. apply prefix_nil. }
  { exists v0, v0'. rewrite filter_check_single_tag_neq // app_nil_r //. }
Qed.

End Trace.

(** *** Definition and correctness of the wrapper code *)

Module Wrap.

Inductive tag_state :=
  | AfterCall (v: val)
  | AfterLin (v v': val)
  | Done.

(* we need extra resource algebras for our ghost state *)
Class linG `{model} (Σ: gFunctors) := {
  lin_model_inG :> inG Σ (excl_authR (leibnizO S));
  lin_gnames_inG :> inG Σ (excl_authR (leibnizO (gname * gname * gname)));
  lin_tag_state_inG :> inG Σ (excl_authR (leibnizO tag_state));
  lin_tag_res_inG :> inG Σ (authR (gmapUR string (agreeR (leibnizO gname))));
}.

Definition linΣ `{model} : gFunctors :=
  #[GFunctor (excl_authR (leibnizO S));
    GFunctor (excl_authR (leibnizO (gname * gname * gname)));
    GFunctor (excl_authR (leibnizO tag_state));
    GFunctor (authR (gmapUR string (agreeR (leibnizO gname))))].

Instance subG_linG {Σ} `{model}: subG linΣ Σ → linG Σ.
Proof. solve_inG. Qed.

Section S.
Context {Σ: gFunctors}.
Context `{heapGS Σ, model, linG Σ}.
Context (N N': namespace) (HNN': N ## N').
Definition mainN := N' .@ "main".
Definition traceN := N' .@ "trace".

Local Notation SO := (leibnizO S).

Context (R_impl : repr Σ).
Context (Pinit_impl : iProp Σ).
Context (init_impl op_impl : val).

Definition init : val :=
  λ: "_", let: "r" := init_impl #() in "r".

Definition op : val :=
  λ: "x" "y",
    let: "t" := Fresh (#"call", "y") in
    let: "r" := op_impl "x" "y" in
    Emit ("t", (#"ret", ("y", "r"))) ;;
    "r".

(** The logical state associated with the tags indexed in [m]. (Named
    [tagsState] in the paper.) *)
Definition tags_state (t: list val) (m: gmap string (agree (leibnizO _))) :
    iProp Σ :=
  ([∗ map] tag↦gs ∈ m, ∃ γs tagst,
     ⌜gs = to_agree γs⌝ ∗ own γs (●E (tagst:leibnizO _)) ∗
     let elts := filter (check_tag tag) t in
     ⌜match tagst with
      | AfterCall v =>
        elts = [(#tag, (#"call", v))%V]
      | AfterLin v v' =>
        elts = [(#tag, (#"call", v))%V; (#tag, (#"lin", (v, v')))%V]
      | Done => True
      end⌝)%I.

Lemma tags_state_call_to_lin v v' t (m: gmap string (agree (leibnizO _)))
    (tag:string) γs :
  m !! tag = Some (to_agree γs) →
  own γs (◯E (AfterCall v : leibnizO _)) ∗ tags_state t m
  ==∗
  own γs (◯E (AfterLin v v' :leibnizO _)) ∗
  tags_state (t ++ [(#tag, (#"lin", (v, v')))%V]) m.
Proof.
  iIntros (Htag) "[Hs Hm]".
  iDestruct (big_sepM_delete _ _ tag with "Hm") as "(Htag & Hm)". done.
  iDestruct "Htag" as (? ? ?) "(Hsa & Hst)". simplify_eq.
  iDestruct "Hst" as %Hst.
  iDestruct (excl_auth_eq with "Hs Hsa") as %<-.
  iMod (excl_auth_upd _ _ _ _ (AfterLin v v') with "Hs Hsa") as "[Hs Hsa]".
  iFrame. iModIntro. rewrite /tags_state (big_sepM_delete _ m tag) //; [].
  iSplitL "Hsa".
  { iExists _, _. iSplitR; [by eauto|]. iFrame. iPureIntro.
    rewrite filter_app filter_check_single_tag_eq Hst //. }
  { iApply (big_sepM_mono with "Hm"). iIntros (tag' g Htag') "H".
    iDestruct "H" as (γ st ->) "(Hγ & H)". iDestruct "H" as %Hst'.
    apply lookup_delete_Some in Htag' as [? Htag']. iExists _, _.
    iSplitR; [by eauto|]. iFrame. iPureIntro.
    rewrite filter_app filter_check_single_tag_neq // app_nil_r //. }
Qed.

Lemma tags_state_lin_to_ret v v' t (m: gmap string (agree (leibnizO _)))
    (tag:string) γs :
  m !! tag = Some (to_agree γs) →
  own γs (◯E (AfterLin v v' : leibnizO _)) ∗ tags_state t m
  ==∗
  tags_state (t ++ [(#tag, (#"ret", (v, v')))%V]) m.
Proof.
  iIntros (Htag) "[Hs Hm]".
  iDestruct (big_sepM_delete _ _ tag with "Hm") as "(Htag & Hm)". done.
  iDestruct "Htag" as (? ? ?) "(Hsa & Hst)". simplify_eq.
  iDestruct "Hst" as %Hst.
  iDestruct (excl_auth_eq with "Hs Hsa") as %<-.
  iMod (excl_auth_upd _ _ _ _ Done with "Hs Hsa") as "[Hs Hsa]".
  iFrame. iModIntro. unfold tags_state.
  rewrite (big_sepM_delete _ m tag) //; [].
  iSplitL "Hsa".
  { iExists _, _. iSplitR; [by eauto|]. iFrame. }
  { iApply (big_sepM_mono with "Hm"). iIntros (tag' g Htag') "H".
    iDestruct "H" as (γ st ->) "(Hγ & H)". iDestruct "H" as %Hst'.
    apply lookup_delete_Some in Htag' as [? Htag']. iExists _, _.
    iSplitR; [by eauto|]. iFrame. iPureIntro.
    rewrite filter_app filter_check_single_tag_neq // app_nil_r //. }
Qed.

Lemma tags_state_lookup_sub γ (m m':gmap string (agree (leibnizO _)))
    tag g t :
  m !! tag = Some (to_agree g) →
  own γ (◯ m) -∗ own γ (● m') -∗ tags_state t m' -∗
  ⌜m' !! tag = Some (to_agree g)⌝.
Proof.
  iIntros (Hkv) "Hf Ha Hm".
  iDestruct (own_op with "[$Ha $Hf]") as "HH".
  iDestruct (own_valid with "HH") as %[Hsub Hv]%auth_both_valid_discrete.
  pose proof (dom_included _ _ Hsub) as Hsub_dom.
  rewrite lookup_included in Hsub |- * => Hsub. specialize (Hsub tag).
  assert (tag ∈ dom (gset string) m') as Htag''.
  { rewrite elem_of_subseteq in Hsub_dom |- * => Hsub_dom.
    eapply Hsub_dom, elem_of_dom_2; eauto. }
  apply elem_of_dom in Htag'' as [vtok'' Htag'']. rewrite Htag'' in Hsub.
  rewrite Hkv in Hsub. rewrite Some_included_total in Hsub |- * => Hsub.
  iDestruct (big_sepM_lookup _ _ tag with "Hm") as (? ? ?) "Hm". by eauto.
  subst vtok''. rewrite to_agree_included in Hsub |- * => Hsub.
  apply leibniz_equiv in Hsub. simplify_eq. done.
Qed.

(** The big auxiliary invariant for wrapper proof. It corresponds to [I] in the
    paper. *)
Definition main_inv (γ γi γs γe: gname) (s: S) : iProp Σ :=
  own γs (●E (s:SO)) ∗
  own γ (●E ((γi, γs, γe) : leibnizO (gname * gname * gname))) ∗
  ∃ (β: list val) (M: gmap string (agree (leibnizO gname))),
    ⌜linearization_trace β⌝ ∗
    ⌜linearized_sound (filter is_lin β) s_init s⌝ ∗
    ⌜per_tag_linearized β⌝ ∗
    trace_is (filter is_call_return β) ∗
    own γe (● M) ∗ own γe (◯ M) ∗
    ⌜ dom (gset string) M = list_to_set (tags (filter is_call_return β)) ⌝ ∗
    tags_state β M.

Definition is_P_wrap γ x : iProp Σ :=
  ∃ γi γs γe,
    is_P R_impl γi x ∗
    inv mainN (∃ s, main_inv γ γi γs γe s) ∗
    trace_inv traceN linearizable.

Definition P_state_wrap γ s : iProp Σ :=
  ∃ γi γs γe,
    P_state R_impl γi s ∗
    own γs (◯E (s:SO)) ∗
    own γ (◯E ((γi, γs, γe) : leibnizO (gname * gname * gname))).

Definition Pinit : iProp Σ :=
    Pinit_impl ∗ trace_is [] ∗ trace_inv traceN linearizable.

Definition R : repr Σ := Build_repr _ _ is_P_wrap P_state_wrap _.

Lemma main_inv_gnames_eq γ γi γs γe γi' γs' γe' s :
  own γ (◯E ((γi', γs', γe') : leibnizO _)) -∗
  main_inv γ γi γs γe s -∗
  ⌜γi' = γi ∧ γs' = γs ∧ γe' = γe⌝.
Proof.
  iIntros "H (? & HH & ?)".
  iDestruct (excl_auth_eq with "H HH") as %?. by simplify_eq.
Qed.

Lemma main_inv_state_eq γ γi γs γe s s' :
  own γs (◯E s' : leibnizO _) -∗
  main_inv γ γi γs γe s -∗
  ⌜s' = s⌝.
Proof.
  iIntros "H (HH & ?)".
  iDestruct (excl_auth_eq with "H HH") as %?. by simplify_eq.
Qed.

Lemma init_correct :
  init_spec R_impl Pinit_impl init_impl -∗
  init_spec R Pinit init.
Proof.
  iIntros "#spec" (φ) "!> (Hi & Ht & HT) Hφ". unfold init.
  iMod (excl_auth_alloc _ s_init) as (γs) "(Hwf & Hwa)".
  iMod (own_alloc (● (∅:gmap string (agree (leibnizO gname))) ⋅
                   ◯ (∅:gmap string (agree (leibnizO gname)))))
    as (γe) "(Htksa & Htksf)".
    apply auth_both_valid_2; done.
  wp_pures. wp_bind (init_impl _).
  iApply ("spec" with "Hi"). iIntros "!>" (γi x) "(HH1 & HH2)".
  iMod (excl_auth_alloc _ (γi, γs, γe)) as (γ) "(Hf & Ha)".
  iMod (inv_alloc mainN _ (∃ s, main_inv γ γi γs γe s)%I
    with "[Ht Ha Hwa Htksa Htksf]") as "HI".
  { iNext. iExists s_init. iFrame. iExists [], ∅. iFrame.
    rewrite /tags_state big_sepM_empty /=.
    iPureIntro. split_and!; eauto; try by constructor.
    { intros. exists #(), #(). apply prefix_nil. }
    by rewrite dom_empty_L //. }
  wp_pures. iApply "Hφ".
  iSplitL "HH1 HI HT". { iExists γi, γs, γe. iFrame. }
  iExists γi, γs, γe. iFrame.
Qed.

(* Main lemma for the first step of the instrumented [op] *)
Lemma op_correct_call γ γi γs γe s :
  main_inv γ γi γs γe s -∗ ∃ α,
    trace_is α ∗
    ⌜∀ (tag:string) v, tag ∉ tags α →
      linearizable (α ++ [(#tag, (#"call", v))%V])⌝ ∗
    (∀ (tag:string) v,
      trace_is (α ++ [(#tag, (#"call", v))%V]) ∗ ⌜tag ∉ tags α⌝ ==∗
      main_inv γ γi γs γe s ∗
      ∃ M (γtag: gname),
        own γe (◯ M) ∗ ⌜M !! tag = Some (to_agree γtag)⌝ ∗
        own γtag (◯E (AfterCall v:leibnizO _))).
Proof using HNN'.
  rewrite {1}/main_inv. iIntros "(Hγs & Hγ & Ht)".
  iDestruct "Ht" as (β tokens)
    "(% & % & Htlin & Ht & Hγea & Hγef & Htoks_dom & Htoks)".
  iDestruct "Htoks_dom" as %Htoks_dom. iDestruct "Htlin" as %Htlin.
  iExists _. iFrame "Ht".
  iSplitR.
  { iPureIntro. intros tag v Htag. unfold linearizable.
    exists (β ++ [(#tag, (#"call", v))%V]).
    unshelve epose proof (linearization_fresh_tag_call_ret _ _ _ _ Htag)
        as Hfresh; eauto; []. split_and!.
    by constructor; eauto.
    by apply per_tag_linearized_add_call; eauto.
    by rewrite filter_app.
    by eexists; rewrite filter_app app_nil_r //. }

  iIntros (tag v) "(Ht & Hfresh)". iDestruct "Hfresh" as %Hfresh.
  unfold main_inv.
  unshelve epose proof (linearization_fresh_tag_call_ret _ _ _ _ Hfresh)
    as Hfresh'; eauto; [].
  iMod (excl_auth_alloc _ (AfterCall v)) as (gts) "[Hgtsf Hgtsa]".
  set tokens' := <[ tag := to_agree (gts:leibnizO _) ]> tokens.
  assert (tokens !! tag = None).
  { eapply (@not_elem_of_dom _ _ (gset string)). typeclasses eauto.
    rewrite Htoks_dom. by apply not_elem_of_list_to_set. }
  iMod (own_update _ (● tokens ⋅ ◯ tokens) (● tokens' ⋅ ◯ tokens')
    with "[Hγea Hγef]") as "[Hγea #Hγef]".
  { apply auth_update. apply alloc_local_update; done. }
  { iSplit; iFrame. }

  iFrame. iModIntro. iSplitR "Hgtsf"; cycle 1.
  { iExists tokens', gts. iFrame "Hγef ∗". iPureIntro.
    by rewrite lookup_insert. }
  iExists (β ++ [(#tag, (#"call", v))%V]), tokens'.
  iSplitR. iPureIntro; by constructor.
  iSplitR. iPureIntro; by rewrite filter_app app_nil_r //.
  iSplitR. iPureIntro; by apply per_tag_linearized_add_call.
  iSplitL "Ht". by rewrite filter_app /=.
  iFrame "Hγea Hγef".
  iSplitR.
  { iPureIntro.
    rewrite filter_app tags_app /= list_to_set_app_L dom_insert_L -Htoks_dom.
    set_solver. }
  rewrite /tags_state big_sepM_insert; last first.
  { eapply (@not_elem_of_dom _ _ (gset string)). typeclasses eauto.
    rewrite Htoks_dom. by apply not_elem_of_list_to_set. }
  iSplitL "Hgtsa".
  { iExists _, _. iSplitR; [by eauto|]. iFrame. iPureIntro.
    rewrite filter_app /=. rewrite (filter_is_nil _ β); last first.
    by apply fresh_tag_nocheck. cbn. rewrite String.eqb_refl //=. }
  iApply (big_sepM_mono with "Htoks"). iIntros (k gs Hk) "HH".
  iDestruct "HH" as (γe' gts' ?) "HH". simplify_eq. iExists _, _.
  iSplitR; [by eauto |].
  rewrite filter_app filter_check_single_tag_neq ?app_nil_r //. intros ->.
  unshelve eapply @elem_of_dom_2 with (D := gset string) in Hk;
    try typeclasses eauto.
  rewrite Htoks_dom elem_of_list_to_set in Hk |- * => Hk. done.
Qed.

(* Main lemma for the second step of [op]: linearization point *)
Lemma op_correct_lin γ γi γs γe s s' γtag v v' tag
    (M: gmap string (agree (leibnizO _))) :
  M !! tag = Some (to_agree γtag) →
  f s v s' →
  r s v v' →
  main_inv γ γi γs γe s ∗
  own γe (◯ M) ∗
  own γs (◯E (s:leibnizO _)) ∗
  own γtag (◯E (AfterCall v:leibnizO _))
  ==∗
  main_inv γ γi γs γe s' ∗
  own γs (◯E (s':leibnizO _)) ∗
  own γtag (◯E ((AfterLin v v'):leibnizO _)).
Proof.
  iIntros (Hm Hs' Hv') "(HI & HM & HHf & Htag)".
  iDestruct "HI" as "(HHa & Hγa & HI)".
  iDestruct "HI" as (β' tokens'')
    "(% & % & % & Ht & Hγea & Hγef' & Htoks_dom & Htoks)".
  iDestruct "Htoks_dom" as %Htoks_dom'.
  iDestruct (excl_auth_upd _ _ _ _ s' with "HHf HHa") as ">[HHf HHa]".

  iDestruct (tags_state_lookup_sub _ _ _ tag with "HM Hγea Htoks") as %?.
    by eauto.

  iAssert (⌜filter (λ v, check_tag tag v) β' = [(#tag, (#"call", v))%V]⌝)%I
    as %Hprevtag.
  { iDestruct (big_sepM_lookup _ _ tag with "Htoks") as (? ? ?) "(Hts & Htok)".
      by eauto.
    simplify_eq. iDestruct (excl_auth_eq with "Htag Hts") as %<-. eauto. }

  iDestruct (tags_state_call_to_lin _ v' with "[$Htag $Htoks]")
    as ">[Htag Htoks]". done.

  iModIntro. unfold main_inv. iFrame.
  iExists (β' ++ [(#tag, (#"lin", (v, v')))%V]), tokens''.
  iFrame.
  iSplitR. iPureIntro; by constructor.
  iSplitR. iPureIntro; by rewrite filter_app; eapply linearized_sound_lin.
  iSplitR. iPureIntro; by apply per_tag_linearized_add_lin.
  rewrite filter_app app_nil_r. iFrame. done.
Qed.

(* Main lemma for the last step of [op] *)
Lemma op_correct_ret γ γi γs γe s s' v v' (tag:string) γtag
    (M: gmap string (agree (leibnizO _))) :
  M !! tag = Some (to_agree γtag) →
  r s v v' →
  main_inv γ γi γs γe s' ∗
  own γe (◯ M) ∗
  own γtag (◯E (AfterLin v v':leibnizO _))
  -∗ ∃ α,
    trace_is α ∗
    ⌜linearizable (α ++ [(#tag, (#"ret", (v, v')))%V])⌝ ∗
    (trace_is (α ++ [(#tag, (#"ret", (v, v')))%V]) ==∗
     main_inv γ γi γs γe s').
Proof using HNN'.
  iIntros (? ?) "(HI & HM & Htag)".
  iDestruct "HI" as "(? & ? & HI)".
  iDestruct "HI" as (β'' M') "(% & % & % & Ht & Hγea & Hγef' & Hdom_res & Hres)".
  iDestruct "Hdom_res" as %Hdom_res.

  iDestruct (tags_state_lookup_sub _ _ _ tag with "HM Hγea Hres") as %HMtag.
    by eauto.

  iAssert (⌜filter (λ v, check_tag tag v) β'' =
           [(#tag, (#"call", v))%V; (#tag, (#"lin", (v, v')))%V]⌝)%I
    as %Hprevtag'.
  { iDestruct (big_sepM_lookup _ _ tag with "Hres") as (? ? ?) "(Hts & Hres)".
      by eauto.
    simplify_eq. iDestruct (excl_auth_eq with "Htag Hts") as %<-. eauto. }

  iExists _. iFrame "Ht". iSplitR.
  { iPureIntro. unfold linearizable.
    exists (β'' ++ [(#tag, (#"ret", (v, v')))%V]). split_and!.
    by constructor.
    by apply per_tag_linearized_add_ret; eauto.
    by rewrite filter_app.
    by eexists; rewrite filter_app app_nil_r. }

  iIntros "Ht".
  iDestruct (tags_state_lin_to_ret with "[$Htag $Hres]") as ">Hres".
    done.

  iModIntro. iFrame. iExists (β'' ++ [(#tag, (#"ret", (v, v')))%V]), M'.
  rewrite filter_app app_nil_r. iFrame.
  iSplitR. iPureIntro; by constructor.
  iSplitR. by iPureIntro; eauto.
  iSplitR. by iPureIntro; apply per_tag_linearized_add_ret; eauto.
  iSplitL "Ht". by rewrite filter_app.
  iPureIntro. rewrite filter_app tags_app /= list_to_set_app_L Hdom_res. simpl.
  rewrite -Hdom_res.
  unshelve eapply @elem_of_dom_2 with (D:=gset string) in HMtag.
  all: try typeclasses eauto. set_solver.
Qed.

Lemma op_correct :
  op_spec R_impl (↑N) op_impl -∗
  op_spec R (↑N ∪ ↑mainN) op.
Proof using HNN'.
  iIntros "spec" (γ x y) "His".
  iDestruct "His" as (γi γs γe) "(#HPimpl & #? & #HT)".
  iIntros (φ) "HAU".

  (* first emit: call *)

  unfold op. wp_pures. wp_bind (Fresh _). unfold op_spec.
  iInv mainN as ">Ht" "Hclose". iDestruct "Ht" as (s) "HI".
  iDestruct (op_correct_call with "HI") as (α) "(Ht & % & Hcont)".
  iApply (wp_fresh with "[$Ht $HT]"). by solve_ndisj. by eauto.
  iNext. iIntros (tag) "(Ht & Hfresh)".
  iMod ("Hcont" with "[$Ht $Hfresh]") as "[HI HM]".
  iDestruct "HM" as (M γtag) "(#HγM & % & Hγtag)".
  iMod ("Hclose" with "[HI]") as "_". by iNext; iExists _; iFrame.
  iModIntro. wp_pures. clear dependent s.

  (* call to op_impl *)

  iSpecialize ("spec" $! _ _ y with "HPimpl"). awp_apply "spec".

  rewrite /atomic_acc /=.
  iInv mainN as ">HI" "Hclose". iDestruct "HI" as (s) "HI".
  iMod "HAU" as (_s) "(HH & Hnext)".
  iDestruct "HH" as (γi' γs' γe') "(HHi & HHf & Hγf)".
  iDestruct (main_inv_gnames_eq with "Hγf HI") as %?. destruct_and!; simplify_eq.
  iDestruct (main_inv_state_eq with "HHf HI") as %?. simplify_eq.

  iModIntro. iExists _. iFrame "HHi".
  iSplit.
  { (* abort case *)
    iIntros "HHi". iDestruct "Hnext" as "[Hnext _]".
    iSpecialize ("Hnext" with "[HHi HHf Hγf]").
    { iExists γi, γs, γe. iFrame. }
    iMod "Hnext". iMod ("Hclose" with "[HI]") as "_". by iExists _.
    iModIntro. iFrame. }

  (* continue case: update the invariant with a lin "ghost" emit *)
  iIntros (s' y') "[HHi [% %]]". iDestruct "Hnext" as "[_ Hnext]".
  iMod (op_correct_lin with "[$HI $HγM $HHf $Hγtag]")
    as "(HI & HHf & Hγtag)". done. done. done.
  iMod ("Hnext" with "[HHi HHf Hγf]").
  { iSplitL. by iExists γi, γs, γe; iFrame. eauto. }
  iMod ("Hclose" with "[HI]") as "_". by iExists _.

  (* final emit: ret *)

  iModIntro. wp_pures. wp_bind (Emit _).
  iInv mainN as ">HI" "Hclose". iDestruct "HI" as (s'') "HI".
  iDestruct (op_correct_ret with "[$HI $HγM $Hγtag]") as (α') "(Ht & % & Hcont)".
    done. done.
  iApply (wp_emit with "[$Ht $HT]"). solve_ndisj. by eauto.
  iIntros "!> Ht". iMod ("Hcont" with "Ht") as "HI".
  iMod ("Hclose" with "[HI]"). by iExists _.
  iModIntro. wp_pures. eauto.
Qed.

End S.

Definition lib (lib_impl: val): val :=
  match lib_impl with
  | (init_impl, op_impl)%V =>
    (init init_impl, op op_impl)
  | _ => #()
  end.

Lemma correct `{heapGS Σ, linG Σ} (N N': namespace) P0 (lib_impl: val) :
  N ## N' →
  lib_spec (↑N) P0 lib_impl -∗
  lib_spec (↑N ∪ ↑(N'.@"main"))
           (P0 ∗ trace_is [] ∗ trace_inv (N'.@"trace") linearizable)
           (lib lib_impl).
Proof.
  iIntros (HNN') "S". iDestruct "S" as (R_impl) "S".
  repeat case_match; eauto. iDestruct "S" as "(Hinit & Hop)".
  unfold lib_spec. iExists (Wrap.R N' R_impl). iSplit.
  iApply init_correct; eauto.
  iApply op_correct; eauto.
Qed.

End Wrap.

(** *** Adequacy *)

Definition libN := nroot .@ "lib".
Definition wrapN := nroot .@ "wrap".
Definition empty_state : state := Build_state ∅ [] ∅.

(** At every step of the execution, the trace from the operational semantics is
    [linearizable]. *)
Lemma wrap_lib_correct `{heapGpreS Σ, model, Wrap.linG Σ} (e: val → expr) (lib_init: expr) (lib: val) (P0: iProp Σ):
  (∀ `(heapGS Σ), ⊢ {{{ True }}} lib_init {{{ v, RET v; P0 }}}) →
  (∀ `(heapGS Σ), ⊢ lib_spec (↑libN) P0 lib) →
  (∀ `(heapGS Σ), ⊢ ∀ P E lib, lib_spec E P lib -∗
                              {{{ P }}} e lib {{{ v, RET v; True }}}) →
  ∀ σ' e',
    rtc erased_step ([(lib_init;; e (Wrap.lib lib))%E], empty_state) (e', σ') →
    linearizable (trace σ').
Proof.
  intros Hinit Hlib Hctx σ' e' Hsteps.
  eapply (@module_invariance Σ (HeapGpreS Σ _ _ _ _)
    (wrapN.@"trace") (@lib_spec _ (↑libN ∪ ↑(wrapN.@"main")) Σ) P0 e lib_init
    (Wrap.lib lib) linearizable empty_state).
  { cbn. apply linearizable_nil. }
  { iIntros (? ? ?) "?". by iApply Hctx. }
  { iIntros (? ? ?) "!>". iApply Hinit; eauto. }
  { iIntros (?). iApply Wrap.correct; eauto. solve_ndisj. iApply Hlib. }
  eauto.
Qed.
