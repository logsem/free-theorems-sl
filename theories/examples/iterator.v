From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import invariants.
From intensional.heap_lang Require Import lifting proofmode notation.
From intensional.heap_lang Require Import adequacy.
From intensional.examples Require Import stdpp_extra tactics.
Set Default Proof Using "Type".
Implicit Types t : list val.

(** ** An iterator over a mutable collection (Section 5.2) *)

(** *** Separation logic specification *)

Definition size_spec `{!heapG Σ} (Coll: val → iProp Σ) (Iter: val → val → iProp Σ) (size: val): iProp Σ :=
  ∀ c, {{{ Coll c }}} size #() {{{ x, RET x; Coll c }}}.

Definition add_spec `{!heapG Σ} (Coll: val → iProp Σ) (Iter: val → val → iProp Σ) (add: val): iProp Σ :=
  ∀ (c x: val), {{{ Coll c }}} add x {{{ c', RET #(); Coll c' }}}.

Definition remove_spec `{!heapG Σ} (Coll: val → iProp Σ) (Iter: val → val → iProp Σ) (remove: val): iProp Σ :=
  ∀ (c x: val), {{{ Coll c }}} remove x {{{ c', RET #(); Coll c' }}}.

Definition iterator_spec `{!heapG Σ} (Coll: val → iProp Σ) (Iter: val → val → iProp Σ) (iterator: val): iProp Σ :=
  ∀ c, {{{ Coll c }}} iterator #() {{{ r, RET r; Coll c ∗ Iter r c }}}.

Definition next_spec `{!heapG Σ} (Coll: val → iProp Σ) (Iter: val → val → iProp Σ) (next: val): iProp Σ :=
  ∀ (c x: val), {{{ Coll c ∗ Iter x c }}} next x {{{ RET #(); Coll c ∗ Iter x c }}}.

Definition iterlib_spec `{!heapG Σ} (P0: iProp Σ) (lib: val): iProp Σ :=
  ∃ (Coll: val → iProp Σ) (Iter: val → val → iProp Σ),
  □ (P0 -∗ ∃ (c:val), Coll c) ∗
  match lib with
  | (size, add, remove, iterator, next)%V =>
    size_spec Coll Iter size ∗
    add_spec Coll Iter add ∗
    remove_spec Coll Iter remove ∗
    iterator_spec Coll Iter iterator ∗
    next_spec Coll Iter next
  | _ => False
  end.

(** *** The trace property [iterator_trace]: "an iterator can only be used if the collection has not been destructively updated in the meantime". *)

Section Trace.

Definition iterator_trace t :=
  ∀ (i:nat) l, t !! i = Some (#"next", l)%V →
    ∃ (j:nat), j < i ∧ t !! j = Some (#"iterator", l)%V ∧
               ∀ (k:nat), j < k < i → t !! k ≠ Some (#"add", #())%V ∧
                                      t !! k ≠ Some (#"remove", #())%V.

Lemma iterator_trace_nil :
  iterator_trace [].
Proof. unfold iterator_trace. go*. Qed.

Lemma iterator_trace_size t :
  iterator_trace t →
  iterator_trace (t ++ [(#"size", #())%V]).
Proof. unfold iterator_trace. go*. Qed.

Lemma iterator_trace_add t :
  iterator_trace t →
  iterator_trace (t ++ [(#"add", #())%V]).
Proof. unfold iterator_trace. go*. Qed.

Lemma iterator_trace_remove t :
  iterator_trace t →
  iterator_trace (t ++ [(#"remove", #())%V]).
Proof. unfold iterator_trace. go*. Qed.

Lemma iterator_trace_iterator t x :
  iterator_trace t →
  iterator_trace (t ++ [(#"iterator", x)%V]).
Proof. unfold iterator_trace. go*. Qed.

Lemma iterator_trace_next t t' (n0 k: nat) x :
  t' !! k = Some (#"iterator", x)%V →
  t' `prefix_of` t →
  n0 ≤ k →
  (∀ (k:nat) (tag:string),
     n0 ≤ k → t !! k = Some (#tag, #())%V → tag ≠ "add" ∧ tag ≠ "remove") →
  iterator_trace t →
  iterator_trace (t ++ [(#"next", x)%V]).
Proof. unfold iterator_trace. go*. Qed.

End Trace.

(** *** Definition and correctness of the wrapper code *)

Module Wrap.

Section S.
Context {Σ: gFunctors}.
Context `{heapG Σ}.
Context (N: namespace).

Context (Coll_impl: val → iProp Σ) (Iter_impl: val → val → iProp Σ).
Context (size_impl add_impl remove_impl iterator_impl next_impl: val).

Definition size : val :=
  λ: "_", let: "r" := size_impl #() in Emit (#"size", #()) ;; "r".

Definition add : val :=
  λ: "x", add_impl "x" ;; Emit (#"add", #()).

Definition remove : val :=
  λ: "x", remove_impl "x" ;; Emit (#"remove", #()).

Definition iterator : val :=
  λ: "_", let: "r" := iterator_impl #() in Emit (#"iterator", "r") ;; "r".

Definition next : val :=
  λ: "x", let: "r" := next_impl "x" in Emit (#"next", "x") ;; "r".

Definition Coll (x: val) : iProp Σ :=
  ∃ (y:val) (n: nat), ⌜x = (y, # n)%V⌝ ∗ Coll_impl y ∗
  ∃ t, trace_is t ∗ trace_inv N iterator_trace ∗
       ⌜n ≤ length t⌝ ∗
       ⌜∀ (k:nat) (tag:string), n ≤ k → t !! k = Some (#tag, #())%V →
                                tag ≠ "add" ∧ tag ≠ "remove"⌝.

Definition Iter (r x: val) : iProp Σ :=
  ∃ (y:val) (n: nat), ⌜x = (y, # n)%V⌝ ∗ Iter_impl r y ∗
  ∃ t, hist t ∗ ⌜∃ (k:nat), n ≤ k ∧ t !! k = Some (#"iterator", r)%V⌝.

Lemma size_correct :
  size_spec Coll_impl Iter_impl size_impl -∗
  size_spec Coll Iter size.
Proof.
  iIntros "#spec". iIntros (c φ) "!> Hc Hφ".
  unfold size. wp_pures. wp_bind (size_impl _).
  iDestruct "Hc" as (? ? ?) "(? & Ht)". iDestruct "Ht" as (t) "(Ht & #HI & %)".
  iMod (trace_is_inv with "Ht HI") as "(Ht & %)".
  iApply ("spec" with "[$]"). iIntros "!>" (?) "Hc". wp_pures.
  wp_bind (Emit _). iApply (wp_emit with "[$Ht $HI]"); eauto.
  by apply iterator_trace_size.
  iIntros "!> Ht". wp_pures. iApply "Hφ". unfold Coll.
  iExists _, _. iFrame. iSplitR; eauto. iExists _. iFrame "HI ∗". iPureIntro. go*.
Qed.

Lemma add_correct :
  add_spec Coll_impl Iter_impl add_impl -∗
  add_spec Coll Iter add.
Proof.
  iIntros "#spec". iIntros (c x φ) "!> Hc Hφ".
  unfold add. wp_pures. wp_bind (add_impl _).
  iDestruct "Hc" as (? ? ?) "(? & Ht)". iDestruct "Ht" as (t) "(Ht & #HI & _)".
  iMod (trace_is_inv with "Ht HI") as "(Ht & %)".
  iApply ("spec" with "[$]"). iIntros "!>" (?) "Hc". wp_pures.
  iApply (wp_emit with "[$Ht $HI]"); eauto.
  by apply iterator_trace_add.
  iIntros "!> Ht". iApply ("Hφ" $! (_, # (length t + 1)%nat)%V). unfold Coll.
  iExists _, _. iFrame. iSplitR; eauto. iExists _. iFrame "HI ∗". iPureIntro. go*.
Qed.

Lemma remove_correct :
  remove_spec Coll_impl Iter_impl remove_impl -∗
  remove_spec Coll Iter remove.
Proof.
  iIntros "#spec". iIntros (c x φ) "!> Hc Hφ".
  unfold remove. wp_pures. wp_bind (remove_impl _).
  iDestruct "Hc" as (? ? ?) "(? & Ht)". iDestruct "Ht" as (t) "(Ht & #HI & _)".
  iMod (trace_is_inv with "Ht HI") as "(Ht & %)".
  iApply ("spec" with "[$]"). iIntros "!>" (?) "Hc". wp_pures.
  iApply (wp_emit with "[$Ht $HI]"); eauto.
  by apply iterator_trace_remove.
  iIntros "!> Ht". iApply ("Hφ" $! (_, # (length t + 1)%nat)%V). unfold Coll.
  iExists _, _. iFrame. iSplitR; eauto. iExists _. iFrame "HI ∗". iPureIntro. go*.
Qed.

Lemma iterator_correct :
  iterator_spec Coll_impl Iter_impl iterator_impl -∗
  iterator_spec Coll Iter iterator.
Proof.
  iIntros "#spec". iIntros (c φ) "!> Hc Hφ".
  unfold iterator. wp_pures. wp_bind (iterator_impl _).
  iDestruct "Hc" as (? ? ?) "(? & Ht)". iDestruct "Ht" as (t) "(Ht & #HI & [% %])".
  iMod (trace_is_inv with "Ht HI") as "(Ht & %)".
  iApply ("spec" with "[$]"). iIntros "!>" (?) "(Hc & Hi)". wp_pures.
  wp_bind (Emit _). iApply (wp_emit with "[$Ht $HI]"); eauto.
  by apply iterator_trace_iterator.
  iIntros "!> Ht". wp_pures.
  iDestruct (alloc_hist with "Ht") as "(Ht & Hh)".
  iApply "Hφ". iSplitL "Hc Ht".
  { iExists _, _. iFrame. iSplitR; eauto. iExists _. iFrame "HI ∗". iPureIntro. go*. }
  { iExists _, _. iFrame. iSplitR; eauto. iExists _. iFrame. iPureIntro.
    exists (length t). go*. }
Qed.

Lemma next_correct :
  next_spec Coll_impl Iter_impl next_impl -∗
  next_spec Coll Iter next.
Proof.
  iIntros "#spec". iIntros (c x φ) "!> (Hc & Hi) Hφ".
  unfold next. wp_pures. wp_bind (next_impl _).
  iDestruct "Hc" as (? ? ?) "(? & Ht)".
  iDestruct "Ht" as (t) "(Ht & #HI & [% %])".
  iDestruct "Hi" as (? ? ?) "(? & Ht')".
  iDestruct "Ht'" as (t') "(Ht' & %)".
  simplify_eq.
  iDestruct (hist_trace_is_prefix with "Ht Ht'") as %?.
  iMod (trace_is_inv with "Ht HI") as "(Ht & %)".
  iApply ("spec" with "[$]"). iIntros "!> (Hc & Hi)". wp_pures.
  wp_bind (Emit _). iApply (wp_emit with "[$Ht $HI]"); eauto.
  { go. by eapply iterator_trace_next. }
  iIntros "!> Ht". wp_pures.
  iDestruct (alloc_hist with "Ht") as "(Ht & Hh)".
  iApply "Hφ". iSplitL "Hc Ht".
  { iExists _, _. iFrame. iSplitR; eauto. iExists _. iFrame "HI ∗". iPureIntro. go*. }
  { iExists _, _. iFrame. iSplitR; eauto. iExists _. iFrame. iPureIntro. go*. }
Qed.

End S.

(** Wrapping code for an entire library *)
Definition lib (lib_impl: val): val :=
  match lib_impl with
  | (size_impl, add_impl, remove_impl, iterator_impl, next_impl)%V =>
    (size size_impl, add add_impl, remove remove_impl, iterator iterator_impl, next next_impl)
  | _ => #()
  end.

(** Correctness of the wrapper code *)
Lemma correct `{!heapG Σ} N P0 (lib_impl: val) :
  iterlib_spec P0 lib_impl -∗
  iterlib_spec (P0 ∗ trace_is [] ∗ trace_inv N iterator_trace) (lib lib_impl).
Proof.
  iIntros "S". iDestruct "S" as (Coll_impl Iter_impl) "(#H0 & S)".
  repeat case_match; eauto. iDestruct "S" as "(? & ? & ? & ? & ?)".
  subst. unfold iterlib_spec.
  iExists (Coll N Coll_impl), (Iter Iter_impl). repeat iSplit.
  { iIntros "!> (HP0 & ? & ?)". iDestruct ("H0" with "HP0") as (c) "?".
    iExists _. unfold Coll. iExists c, 0%nat. iSplitR; eauto.
    iFrame. iExists []. iFrame. iPureIntro. go*. }
  iApply size_correct; eauto.
  iApply add_correct; eauto.
  iApply remove_correct; eauto.
  iApply iterator_correct; eauto.
  iApply next_correct; eauto.
Qed.

End Wrap.

(** *** Adequacy *)

Definition iterlibN := nroot .@ "iterlib".
Definition empty_state : state := Build_state ∅ [] ∅.

(** The trace property [iterator_trace] is satisfied at every step of the
    execution at the level of the operational semantics. *)
Lemma wrap_iterlib_correct (e: val → expr) (lib: val):
  (∀ `(heapG Σ), ⊢ iterlib_spec True lib) →
  (∀ `(heapG Σ), ⊢ ∀ P lib, iterlib_spec P lib -∗ {{{ P }}} e lib {{{ v, RET v; True }}}) →
  ∀ σ' e',
    rtc erased_step ([(#();; e (Wrap.lib lib))%E], empty_state) (e', σ') →
    iterator_trace (trace σ').
Proof.
  set (Σ := #[invΣ; gen_heapΣ loc val; traceΣ; proph_mapΣ proph_id (val * val)]).
  intros Hlib Hctx σ' e' Hsteps.
  eapply (@module_invariance Σ (HeapPreG Σ _ _ _ _)
                             iterlibN (@iterlib_spec Σ) True e #() (Wrap.lib lib)
                            iterator_trace empty_state).
  { cbn. apply iterator_trace_nil. }
  { iIntros (? ? ?) "?". by iApply Hctx. }
  { iIntros (? _) "!>". iApply wp_value; eauto. }
  { iIntros (?). iApply Wrap.correct. iApply Hlib. }
  eauto.
Qed.
