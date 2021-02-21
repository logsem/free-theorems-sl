From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl excl_auth gmap.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From intensional.heap_lang Require Import lifting proofmode notation.
From intensional.heap_lang Require Import adequacy.
From intensional Require Import stdpp_extra trace_helpers.
Set Default Proof Using "Type".
Implicit Types t : list val.

Class model := {
  S :> Type;
  s_init : S;
  f : S → val → S;
  r : S → val → val;
}.

Record repr {Σ: gFunctors} `{model} := {
  is_P: gname → val → iProp Σ;
  P_content: gname → S → iProp Σ;
  is_P_persistent : ∀ γ x, Persistent (is_P γ x);
  P_content_timeless : ∀ γ s, Timeless (P_content γ s);
}.

Arguments repr Σ {_}.
Hint Resolve is_P_persistent : typeclass_instances.
Hint Resolve P_content_timeless : typeclass_instances.

Section Specs.
Context `{!heapG Σ}.
Context `{model} (R: repr Σ).
Context (E: coPset).

Definition init_spec P0 (init: val) : iProp Σ :=
  {{{ P0 }}} init #() {{{ γ r, RET r; is_P R γ r ∗ P_content R γ s_init }}}.

Definition op_spec (op: val) : iProp Σ :=
  ∀ γ (x y: val),
    is_P R γ x -∗
    <<< ∀ s, P_content R γ s >>>
      op x y @ ⊤∖E
    <<< P_content R γ (f s y), RET (r s y) >>>.

End Specs.

Definition lib_spec `{!heapG Σ} `{model} (P0: iProp Σ) (E: coPset) (lib: val) : iProp Σ :=
  ∃ (R: repr Σ),
  match lib with
  | (init, op)%V => init_spec R P0 init ∗ op_spec R E op
  | _ => False
  end.

Section Trace.

(* Inductive concurrent_trace : list val → Prop := *)
(*   | concurrent_trace_nil : *)
(*       concurrent_trace [] *)
(*   | concurrent_trace_call (tag: string) (v: val) t : *)
(*       concurrent_trace t → *)
(*       concurrent_trace (t ++ [(#tag, (#"call", v))%V]) *)
(*   | concurrent_trace_ret (tag: string) (v v': val) t : *)
(*       concurrent_trace t → *)
(*       concurrent_trace (t ++ [(#tag, (#"ret", (v, v')))%V]). *)

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

Inductive linearized_trace_for (tag: string) : list val → Prop :=
  | linearized_trace_for_nil :
      linearized_trace_for tag []
  | linearized_trace_for_call t (v v': val) :
      linearized_trace_for tag t →
      linearized_trace_for tag (t ++ [(#tag, (#"call", v)); (#tag, (#"lin", (v, v'))); (#tag, (#"ret", (v, v')))]%V).

Inductive linearized_sound `{model} : list val → S → S → Prop :=
  (* administrative steps. calls and rets are ignored. *)
  | linearized_sound_nil s :
      linearized_sound [] s s
  | linearized_sound_call_ret s0 s (tag op: string) arg t :
      linearized_sound t s0 s →
      op = "call" ∨ op = "ret" →
      linearized_sound (t ++ [(#tag, (#op, arg))%V]) s0 s
  (* lin events must be sound wrt the model *)
  | linearized_sound_lin s0 s (tag:string) v v' t :
      linearized_sound t s0 s →
      v' = r s v →
      linearized_sound (t ++ [(#tag, (#"lin", (v, v')))%V]) s0 (f s v).

Inductive matching_call_ret : list val → list val → Prop :=
  | matching_call_ret_nil t' :
      matching_call_ret [] t'
  | matching_call_ret_lin t t' (tag: string) v v':
      matching_call_ret t t' →
      matching_call_ret t (t' ++ [(#tag, (#"lin", (v, v')))%V])
  | matching_call_ret_call t t' (tag: string) v :
      matching_call_ret t t' →
      matching_call_ret (t ++ [(#tag, (#"call", v))%V]) (t' ++ [(#tag, (#"call", v))%V])
  | matching_call_ret_ret t t' (tag: string) v v' :
      matching_call_ret t t' →
      matching_call_ret (t ++ [(#tag, (#"ret", (v, v')))%V]) (t' ++ [(#tag, (#"ret", (v, v')))%V])
.

Definition linearizable `{model} t :=
  ∃ t', linearization_trace t'
        ∧ (∀ tag, linearized_trace_for tag (filter (check_tag tag) t'))
        ∧ matching_call_ret t t'
        ∧ ∃ s', linearized_sound t' s_init s'.

End Trace.

Definition per_tag_linearized (β: list val) :=
  ∀ tag, ∃ v v',
        filter (check_tag tag) β
          `prefix_of`
        [(#tag, (#"call", v))%V; (#tag, (#"lin", (v, v')))%V; (#tag, (#"ret", (v, v')))%V].

Lemma per_tag_linearized_prefix t t' :
  per_tag_linearized t' →
  t `prefix_of` t' →
  per_tag_linearized t.
Proof.
  unfold per_tag_linearized. intros Ht' [l ->].
  intros tag. specialize (Ht' tag) as (v & v' & Ht'). exists v, v'.
  rewrite filter_app in Ht'. by apply prefix_app_l in Ht'.
Qed.

Inductive emit_state :=
  | AfterCall (v: val)
  | AfterLin (v v': val)
  | AfterRet (v v': val).

(* we need extra resource algebras for our ghost state *)
Class linG `{model} (Σ: gFunctors) := {
  lin_model_inG :> inG Σ (excl_authR (leibnizO S));
  lin_gnames_inG :> inG Σ (excl_authR (leibnizO (gname * gname * gname)));
  lin_emit_state_inG :> inG Σ (excl_authR (leibnizO emit_state));
  lin_emit_res_inG :> inG Σ (authR (gmapUR string (agreeR (leibnizO gname))));
}.

Module Wrap.

Section S.
Context {Σ: gFunctors}.
Context `{heapG Σ, model, linG Σ}.
Context (N N': namespace) (HNN': N ## N').

Local Notation SO := (leibnizO S).
Local Notation valO := (leibnizO val).

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

Definition is_call_return (v: val) :=
  match v with
  | (#_, (#"call", _))%V | (#_, (#"ret", _))%V => true
  | _ => false
  end.

(* Notation "⋄" := (Excl (tt:leibnizO _)). *)
(* Notation "⋄" := (Excl tt) (only printing). *)

(* Lemma token_both_false γ : own γ ⋄ -∗ own γ ⋄ -∗ False. *)
(* Proof. *)
(*   iIntros "H1 H2". iDestruct (own_op with "[$H1 $H2]") as "H". *)
(*   iDestruct (own_valid with "H") as %valid. done. *)
(* Qed. *)

Lemma excl_auth_eq A `{inG Σ (excl_authR (leibnizO A))} γ (x y: A):
  own γ (◯E (x:leibnizO A)) -∗ own γ (●E (y:leibnizO A)) -∗ ⌜x = y⌝.
Proof.
  iIntros "H1 H2". iDestruct (own_op with "[$H1 $H2]") as "H".
  iDestruct (own_valid with "H") as %HH%excl_auth_agree. done.
Qed.

Lemma excl_auth_upd A `{inG Σ (excl_authR (leibnizO A))} γ (x y z: A):
  own γ (◯E (x:leibnizO A)) -∗ own γ (●E (y:leibnizO A)) ==∗
  own γ (◯E (z:leibnizO A)) ∗ own γ (●E (z:leibnizO A)).
Proof.
  iIntros "H1 H2".
  iDestruct (own_update_2 with "H1 H2") as ">[? ?]".
  apply excl_auth_update. iModIntro. iFrame.
Qed.

Lemma excl_auth_alloc A `{inG Σ (excl_authR (leibnizO A))} (x: A):
  ⊢ |==> ∃ γ, own γ (◯E (x:leibnizO A)) ∗ own γ (●E (x:leibnizO A)).
Proof.
  iIntros.
  iMod (own_alloc (●E (x:leibnizO A) ⋅ ◯E (x:leibnizO A))) as (γ) "[? ?]".
  apply excl_auth_valid. iModIntro. iExists _. iFrame.
Qed.

Definition emit_state_res (t: list val) (m: gmap string (agree (leibnizO gname))) : iProp Σ :=
  ([∗ map] tag↦gs ∈ m, ∃ γs tagst, ⌜gs = to_agree γs⌝ ∗ own γs (●E (tagst:leibnizO _)) ∗
     let elts := filter (check_tag tag) t in
     ⌜match tagst with
      | AfterCall v =>
        elts = [(#tag, (#"call", v))%V]
      | AfterLin v v' =>
        elts = [(#tag, (#"call", v))%V; (#tag, (#"lin", (v, v')))%V]
      | AfterRet v v' =>
        elts = [(#tag, (#"call", v))%V; (#tag, (#"lin", (v, v')))%V; (#tag, (#"ret", (v, v')))%V]
      end⌝)%I.

Lemma emit_state_res_call_to_lin v v' t (m: gmap string (agree (leibnizO gname))) (tag:string) γs :
  m !! tag = Some (to_agree γs) →
  own γs (◯E (AfterCall v : leibnizO _)) ∗ emit_state_res t m
  ==∗
  own γs (◯E (AfterLin v v' :leibnizO _)) ∗ emit_state_res (t ++ [(#tag, (#"lin", (v, v')))%V]) m.
Proof.
  iIntros (Htag) "[Hs Hm]".
  iDestruct (big_sepM_delete _ _ tag with "Hm") as "(Htag & Hm)". done.
  iDestruct "Htag" as (? ? ?) "(Hsa & Hst)". simplify_eq.
  iDestruct "Hst" as %Hst.
  iDestruct (excl_auth_eq with "Hs Hsa") as %<-.
  iMod (excl_auth_upd _ _ _ _ (AfterLin v v') with "Hs Hsa") as "[Hs Hsa]".
  iFrame. iModIntro. unfold emit_state_res. rewrite (big_sepM_delete _ m tag) //; [].
  iSplitL "Hsa".
  { iExists _, _. iSplitR; [by eauto|]. iFrame. iPureIntro.
    rewrite filter_app filter_check_single_tag_eq Hst //. }
  { iApply (big_sepM_mono with "Hm"). iIntros (tag' g Htag') "H".
    iDestruct "H" as (γ st ->) "(Hγ & H)". iDestruct "H" as %Hst'.
    apply lookup_delete_Some in Htag' as [? Htag']. iExists _, _.
    iSplitR; [by eauto|]. iFrame. iPureIntro.
    rewrite filter_app filter_check_single_tag_neq // app_nil_r //. }
Qed.

Lemma emit_state_res_lin_to_ret v v' t (m: gmap string (agree (leibnizO gname))) (tag:string) γs :
  m !! tag = Some (to_agree γs) →
  own γs (◯E (AfterLin v v' : leibnizO _)) ∗ emit_state_res t m
  ==∗
  own γs (◯E (AfterRet v v' :leibnizO _)) ∗ emit_state_res (t ++ [(#tag, (#"ret", (v, v')))%V]) m.
Proof.
  iIntros (Htag) "[Hs Hm]".
  iDestruct (big_sepM_delete _ _ tag with "Hm") as "(Htag & Hm)". done.
  iDestruct "Htag" as (? ? ?) "(Hsa & Hst)". simplify_eq.
  iDestruct "Hst" as %Hst.
  iDestruct (excl_auth_eq with "Hs Hsa") as %<-.
  iMod (excl_auth_upd _ _ _ _ (AfterRet v v') with "Hs Hsa") as "[Hs Hsa]".
  iFrame. iModIntro. unfold emit_state_res. rewrite (big_sepM_delete _ m tag) //; [].
  iSplitL "Hsa".
  { iExists _, _. iSplitR; [by eauto|]. iFrame. iPureIntro.
    rewrite filter_app filter_check_single_tag_eq Hst //. }
  { iApply (big_sepM_mono with "Hm"). iIntros (tag' g Htag') "H".
    iDestruct "H" as (γ st ->) "(Hγ & H)". iDestruct "H" as %Hst'.
    apply lookup_delete_Some in Htag' as [? Htag']. iExists _, _.
    iSplitR; [by eauto|]. iFrame. iPureIntro.
    rewrite filter_app filter_check_single_tag_neq // app_nil_r //. }
Qed.

Definition trace_inv (γ γi γw γt: gname) (s: S) : iProp Σ :=
  own γw (●E (s:SO)) ∗
  own γ (●E ((γi, γw, γt) : leibnizO (gname * gname * gname))) ∗
  ∃ (β: list val) (M: gmap string (agree (leibnizO gname))),
    ⌜linearization_trace β⌝ ∗
    ⌜linearized_sound β s_init s⌝ ∗
    ⌜per_tag_linearized β⌝ ∗
    trace_is (filter is_call_return β) ∗

    own γt (● M) ∗ own γt (◯ M) ∗
    ⌜ dom (gset string) M = list_to_set (tags (filter is_call_return β)) ⌝ ∗
    emit_state_res β M.

Definition is_P_wrap γ x : iProp Σ :=
  ∃ γi γw γt,
    is_P R_impl γi x ∗
    inv N' (∃ s, trace_inv γ γi γw γt s).

Definition P_content_wrap γ s : iProp Σ :=
  ∃ γi γw γt,
    P_content R_impl γi s ∗
    own γw (◯E (s:SO)) ∗
    own γ (◯E ((γi, γw, γt) : leibnizO (gname * gname * gname))).

Definition Pinit : iProp Σ :=
    Pinit_impl ∗ trace_is [].

Definition R : repr Σ := Build_repr _ _ is_P_wrap P_content_wrap _ _.

Lemma init_correct :
  init_spec R_impl Pinit_impl init_impl -∗
  init_spec R Pinit init.
Proof.
  iIntros "#spec" (φ) "!> (Hi & Ht) Hφ". unfold init.
  iMod (excl_auth_alloc _ s_init) as (γw) "(Hwf & Hwa)".
  iMod (own_alloc (● (∅:gmap string (agree (leibnizO gname))) ⋅
                   ◯ (∅:gmap string (agree (leibnizO gname)))))
    as (γt) "(Htksa & Htksf)".
    apply auth_both_valid_2; done.
  wp_pures. wp_bind (init_impl _).
  iApply ("spec" with "Hi"). iIntros "!>" (γi x) "(HH1 & HH2)".
  iMod (excl_auth_alloc _ (γi, γw, γt)) as (γ) "(Hf & Ha)".
  iMod (inv_alloc N' _ (∃ s, trace_inv γ γi γw γt s)%I with "[Ht Ha Hwa Htksa Htksf]")
    as "HI".
  { iNext. iExists s_init. iFrame. iExists [], ∅. iFrame.
    rewrite /emit_state_res big_sepM_empty /=.
    iPureIntro. split_and!; eauto; try by constructor.
    { intros. exists #(), #(). apply prefix_nil. }
    by rewrite dom_empty_L //. }
  wp_pures. iApply "Hφ".
  iSplitL "HH1 HI". { iExists γi, γw, γt. iFrame. }
  iExists γi, γw, γt. iFrame.
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
      cbn. destruct (decide True); last done. cbn. by apply elem_of_list_singleton. }
  { intros tag0 Htl [Hf1 Hf2]%not_elem_of_app. apply not_elem_of_app. split.
    - apply IHHl; auto. eapply per_tag_linearized_prefix; eauto.
      by eapply prefix_app_r.
    - clear Hf2. pose proof Htl as Htl'.
      unfold per_tag_linearized in Htl. specialize (Htl tag0) as [v0 [v'0 Htl]].
      rewrite filter_app in Htl. rewrite (filter_is_nil _ t) in Htl; last first.
      { apply fresh_tag_nocheck. apply IHHl; eauto. eapply per_tag_linearized_prefix; eauto.
        by eapply prefix_app_r. }
      destruct (decide (tag0 = tag)).
      + subst. rewrite filter_check_single_tag_eq in Htl. cbn in Htl.
        destruct Htl as (? & HHH). inversion HHH.
      + subst. intros HH. by apply elem_of_list_singleton in HH. }
  { intros tag0 Htl [Hf1 Hf2]%not_elem_of_app. apply not_elem_of_app. split.
    - apply IHHl; auto. eapply per_tag_linearized_prefix; eauto.
      by eapply prefix_app_r.
    - cbn. intros HH%elem_of_list_singleton. subst. apply Hf2.
      cbn. destruct (decide True); last done. cbn. by apply elem_of_list_singleton. }
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
  filter (λ v, check_tag tag v) t = [(#tag, (#"call", v))%V; (#tag, (#"lin", (v, v')))%V] →
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

Lemma emit_state_res_lookup_sub γ (m m':gmap string (agree (leibnizO gname))) tag g t:
  m !! tag = Some (to_agree g) →
  own γ (◯ m) -∗ own γ (● m') -∗ emit_state_res t m' -∗
  ⌜m' !! tag = Some (to_agree g)⌝.
Proof.
  iIntros (Hkv) "Hf Ha Hm".
  iDestruct (own_op with "[$Ha $Hf]") as "HH".
  iDestruct (own_valid with "HH") as %[Hsub Hv]%auth_both_valid.
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

Lemma op_correct :
  op_spec R_impl (↑N) op_impl -∗
  op_spec R (↑N ∪ ↑N') op.
Proof using HNN'.
  iIntros "spec" (γ x y) "His".
  iDestruct "His" as (γi γw γt) "(#HPimpl & #?)".
  iIntros (φ) "HAU".

  (* first emit: call *)

  unfold op. wp_pures. wp_bind (Fresh _). unfold op_spec.
  iInv N' as ">Ht" "Hclose".
  iDestruct "Ht" as (s) "(Hγw & Hγ & Ht)".
  iDestruct "Ht" as (β tokens) "(% & % & Htlin & Ht & Hγta & Hγtf & Htoks_dom & Htoks)".
  iDestruct "Htoks_dom" as %Htoks_dom. iDestruct "Htlin" as %Htlin.
  iApply (wp_fresh with "Ht"). iNext. iIntros (tag) "(Ht & Hfresh)".
  iDestruct "Hfresh" as %Hfresh.
  unshelve epose proof (linearization_fresh_tag_call_ret _ _ _ _ Hfresh)
    as Hfresh'; eauto; [].
  iMod (excl_auth_alloc _ (AfterCall y)) as (gts) "[Hgtsf Hgtsa]".
  set tokens' := <[ tag := to_agree (gts:leibnizO _) ]> tokens.
  assert (tokens !! tag = None).
  { eapply (@not_elem_of_dom _ _ (gset string)). typeclasses eauto.
    rewrite Htoks_dom. by apply not_elem_of_list_to_set. }
  iMod (own_update _ (● tokens ⋅ ◯ tokens) (● tokens' ⋅ ◯ tokens') with "[Hγta Hγtf]")
    as "[Hγta #Hγtf]".
  { apply auth_update. apply alloc_local_update; done. }
  { iSplit; iFrame. }

  iMod ("Hclose" with "[Ht Hγw Hγ Hγta Hγtf Htoks Hgtsa]") as "_".
  { iNext. iExists s. unfold trace_inv at 2. iFrame.
    iExists (β ++ [(#tag, (#"call", y))%V]), tokens'.
    iSplitR. iPureIntro; by constructor.
    iSplitR. iPureIntro; by constructor; eauto.
    iSplitR. iPureIntro; by apply per_tag_linearized_add_call.
    iSplitL "Ht". by rewrite filter_app /=.
    iFrame "Hγta Hγtf".
    iSplitR.
    { iPureIntro.
      rewrite filter_app tags_app /= list_to_set_app_L dom_insert_L -Htoks_dom.
      set_solver. }
    rewrite /emit_state_res big_sepM_insert; last first.
    { eapply (@not_elem_of_dom _ _ (gset string)). typeclasses eauto.
      rewrite Htoks_dom. by apply not_elem_of_list_to_set. }
    iSplitL "Hgtsa".
    { iExists _, _. iSplitR; [by eauto|]. iFrame. iPureIntro.
      rewrite filter_app /=. rewrite (filter_is_nil _ β); last first.
      by apply fresh_tag_nocheck. cbn. rewrite String.eqb_refl //=. }
    iApply (big_sepM_mono with "Htoks"). iIntros (k gs Hk) "HH".
    iDestruct "HH" as (γt' gts' ?) "HH". simplify_eq. iExists _, _.
    iSplitR; [by eauto |]. rewrite filter_app filter_check_single_tag_neq ?app_nil_r //.
    intros ->. unshelve eapply @elem_of_dom_2 with (D := gset string) in Hk; try typeclasses eauto.
    rewrite Htoks_dom elem_of_list_to_set in Hk |- * => Hk. done. }

  iModIntro. wp_pures. clear dependent s.

  iSpecialize ("spec" $! _ _ y with "HPimpl").
  awp_apply "spec".

  rewrite /atomic_acc /=.
  iInv N' as ">HI" "Hclose". iDestruct "HI" as (s) "HI".
  iMod "HAU" as (s') "(HH & Hnext)". by set_solver.
  iDestruct "HH" as (γi' γw' γt') "(HHi & HHf & Hγf)".
  iDestruct "HI" as "(HHa & Hγa & HI)".
  iDestruct (excl_auth_eq with "Hγf Hγa") as %?. simplify_eq.
  iDestruct (excl_auth_eq with "HHf HHa") as %->.
  iModIntro. iExists _. iFrame "HHi".
  iSplit.
  { (* abort case *)
    iIntros "HHi". iDestruct "Hnext" as "[Hnext _]".
    iSpecialize ("Hnext" with "[HHi HHf Hγf]").
    { iExists γi, γw, γt. iFrame. }
    iMod "Hnext". iMod ("Hclose" with "[HI HHa Hγa]") as "_".
    { iNext. iExists _. iFrame. }
    iModIntro. iFrame. }

  (* continue case: lin "ghost" emit *)
  iIntros "HHi". iDestruct "Hnext" as "[_ Hnext]".
  iDestruct "HI" as (β' tokens'') "(% & % & % & Ht & Hγta & Hγtf' & Htoks_dom & Htoks)".
  iDestruct "Htoks_dom" as %Htoks_dom'.
  iDestruct (excl_auth_upd _ _ _ _ (f s y) with "HHf HHa") as ">[HHf HHa]".
  iSpecialize ("Hnext" with "[HHi HHf Hγf]").
  { iExists γi, γw, γt. iFrame. }

  iDestruct (emit_state_res_lookup_sub _ _ _ tag with "Hγtf Hγta Htoks") as %?.
    by rewrite lookup_insert //.

  iAssert (⌜filter (λ v, check_tag tag v) β' = [(#tag, (#"call", y))%V]⌝)%I as %Hprevtag.
  { iDestruct (big_sepM_lookup _ _ tag with "Htoks") as (? ? ?) "(Hts & Htok)". by eauto.
    simplify_eq. iDestruct (excl_auth_eq with "Hgtsf Hts") as %<-. eauto. }

  iDestruct (emit_state_res_call_to_lin _ (r s y) with "[$Hgtsf $Htoks]") as ">[Hgtsf Htoks]".
    done.

  iMod "Hnext". iMod ("Hclose" with "[Ht HHa Hγa Hγta Hγtf' Htoks]") as "_".
  { iNext. iExists _. unfold trace_inv at 2. iFrame.
    iExists (β' ++ [(#tag, (#"lin", (y, r s y)))%V]), tokens''.
    rewrite filter_app app_nil_r. iFrame.
    iSplitR. iPureIntro; by constructor.
    iSplitR. iPureIntro; by eapply linearized_sound_lin.
    iSplitR. iPureIntro; by apply per_tag_linearized_add_lin.
    done. }

  (* final emit: ret *)

  iModIntro. wp_pures. wp_bind (Emit _).
  iInv N' as ">HI" "Hclose".
  iDestruct "HI" as (s') "(HHa & Hγa & HI)".
  iDestruct "HI" as (β'' M) "(% & % & % & Ht & Hγta & Hγtf' & Hdom_res & Hres)".
  iDestruct "Hdom_res" as %Hdom_res.
  iApply (wp_emit with "Ht"). iIntros "!> Ht".

  iDestruct (emit_state_res_lookup_sub _ _ _ tag with "Hγtf Hγta Hres") as %HMtag.
    by rewrite lookup_insert //.

  iAssert (⌜filter (λ v, check_tag tag v) β'' = [(#tag, (#"call", y))%V; (#tag, (#"lin", (y, r s y)))%V]⌝)%I
    as %Hprevtag'.
  { iDestruct (big_sepM_lookup _ _ tag with "Hres") as (? ? ?) "(Hts & Hres)". by eauto.
    simplify_eq. iDestruct (excl_auth_eq with "Hgtsf Hts") as %<-. eauto. }

  iDestruct (emit_state_res_lin_to_ret with "[$Hgtsf $Hres]") as ">[Hgtsf Hres]".
    done.

  iMod ("Hclose" with "[HHa Hγa Ht Hγta Hγtf' Hres]").
  { iNext. iExists _. unfold trace_inv at 2. iFrame.
    iExists (β'' ++ [(#tag, (#"ret", (y, r s y)))%V]), M.
    rewrite filter_app. iFrame.
    iSplitR. iPureIntro; by constructor.
    iSplitR. by iPureIntro; constructor; eauto.
    iSplitR. iPureIntro; apply per_tag_linearized_add_ret; eauto.
    iPureIntro. rewrite tags_app /= list_to_set_app_L Hdom_res. simpl.
    rewrite -Hdom_res. unshelve eapply @elem_of_dom_2 with (D:=gset string) in HMtag.
    all: try typeclasses eauto. set_solver. }

  iModIntro. wp_pures. eauto.
Qed.

End S.

Definition lib (lib_impl: val): val :=
  match lib_impl with
  | (init_impl, op_impl)%V =>
    (init init_impl, op op_impl)
  | _ => #()
  end.

Lemma correct `{heapG Σ, model, linG Σ} (N N': namespace) P0 (lib_impl: val) :
  N ## N' →
  lib_spec P0 (↑N) lib_impl -∗
  lib_spec (P0 ∗ trace_is []) (↑N ∪ ↑N') (lib lib_impl).
Proof.
  iIntros (HNN') "S". iDestruct "S" as (R_impl) "S".
  repeat case_match; eauto. iDestruct "S" as "(Hinit & Hop)".
  unfold lib_spec. iExists (Wrap.R N' R_impl). iSplit.
  iApply init_correct; eauto.
  iApply op_correct; eauto.
Qed.

End Wrap.


Definition libN := nroot .@ "lib".
Definition wrapN := nroot .@ "wrap".
Definition empty_state : state := Build_state ∅ [] ∅.

Lemma wrap_lib_correct {Σ} `{heapPreG Σ, model, linG Σ} (e: val → expr) (lib: val):
  (⊢ ∀ `{heapG Σ}, lib_spec True (↑libN) lib) →
  (⊢ ∀ `{heapG Σ} P E lib, lib_spec P E lib -∗ {{{ P }}} e lib {{{ v, RET v; True }}}) →
  ∀ σ' e',
    rtc erased_step ([(#();; e (Wrap.lib lib))%E], empty_state) (e', σ') →
    linearizable (trace σ').
Proof.
  intros Hlib Hctx σ' e' Hsteps.
(*   eapply (@heap_invariance Σ _ wrapN *)


(*   eapply (@module_invariance Σ _ stacklibN (@stacklib_spec Σ) True e #() (Wrap.lib lib) *)
(*                             good_stack_trace empty_state). *)
(*   { cbn. apply good_stack_trace_nil. } *)
(*   { iIntros (? ? ?) "?". by iApply Hctx. } *)
(*   { iIntros (? _) "!>". iApply wp_value; eauto. } *)
(*   { iIntros (?). iApply Wrap.correct. iApply Hlib. } *)
(*   eauto. *)
(* Qed. *)
Admitted.
