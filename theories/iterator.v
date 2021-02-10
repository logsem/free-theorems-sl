From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import invariants.
From intensional.heap_lang Require Import lifting proofmode notation.
From intensional.heap_lang Require Import adequacy.
From intensional Require Import stdpp_extra tactics.
Set Default Proof Using "Type".
Implicit Types t : list event.

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

Instance iterlib_persistent `{!heapG Σ} P0 lib : Persistent (iterlib_spec P0 lib).
Proof.
  apply bi.exist_persistent. intro.
  repeat case_match; try typeclasses eauto.
Qed.

Section Trace.

Definition iterator_trace t :=
  ∀ (i:nat) l, t !! i = Some ("next", l) →
    ∃ (j:nat), j < i ∧ t !! j = Some ("iterator", l) ∧
               ∀ (k:nat), j < k < i → t !! k ≠ Some ("add", #()) ∧
                                      t !! k ≠ Some ("remove", #()).

Lemma iterator_trace_size t :
  iterator_trace t →
  iterator_trace (t ++ [("size", #())]).
Proof. unfold iterator_trace. go*. Qed.

Lemma iterator_trace_add t :
  iterator_trace t →
  iterator_trace (t ++ [("add", #())]).
Proof. unfold iterator_trace. go*. Qed.

Lemma iterator_trace_remove t :
  iterator_trace t →
  iterator_trace (t ++ [("remove", #())]).
Proof. unfold iterator_trace. go*. Qed.

End Trace.

Module Wrap.

Section S.
Context {Σ: gFunctors}.
Context `{heapG Σ}.
Context (N: namespace).

Context (Coll_impl: val → iProp Σ) (Iter_impl: val → val → iProp Σ).
Context (size_impl add_impl remove_impl iterator_impl next_impl: val).

Definition size : val :=
  λ: "_", let: "r" := size_impl #() in Emit "size" #() ;; "r".

Definition add : val :=
  λ: "x", add_impl "x" ;; Emit "add" #().

Definition remove : val :=
  λ: "x", remove_impl "x" ;; Emit "remove" #().

Definition iterator : val :=
  λ: "_", let: "r" := iterator_impl #() in Emit "iterator" "r" ;; "r".

Definition next : val :=
  λ: "x", let: "r" := next_impl "x" in Emit "next" "x" ;; "r".

Definition Coll (x: val) : iProp Σ :=
  ∃ (y:val) (n: nat), ⌜x = (y, # n)%V⌝ ∗ Coll_impl y ∗
  ∃ t, trace_is t ∗ trace_inv N iterator_trace ∗
       (* ⌜n ≤ length t⌝ ∗ *)
       ⌜∀ (k:nat) lbl, n < k → t !! k = Some (lbl, #()) →
                       lbl ≠ "add" ∧ lbl ≠ "remove"⌝.

Definition Iter (r x: val) : iProp Σ :=
  ∃ (y:val) (n: nat), ⌜x = (y, # n)%V⌝ ∗ Iter_impl r y ∗
  ∃ t, hist t ∗ ⌜∃ (k:nat), n < k ∧ t !! k = Some ("iterator", r)⌝.

Lemma size_correct :
  size_spec Coll_impl Iter_impl size_impl -∗
  size_spec Coll Iter size.
Proof.
  iIntros "#spec". iIntros (c) "!>". iIntros (φ) "Hc Hφ".
  unfold size. wp_pures. wp_bind (size_impl _).
  iDestruct "Hc" as (? ? ?) "(? & Ht)". iDestruct "Ht" as (t) "(Ht & #HI & %)".
  iMod (trace_is_inv with "Ht HI") as "(Ht & %)".
  iApply ("spec" with "[$]"). iIntros "!>" (?) "Hc". wp_pures.
  wp_bind (Emit _ _). iApply (wp_emit with "[$Ht $HI]"); eauto.
  by apply iterator_trace_size.
  iIntros "!> Ht". wp_pures. iApply "Hφ". unfold Coll.
  iExists _, _. iFrame. iSplitR; eauto. iExists _. iFrame "HI ∗". iPureIntro. go.
Qed.

Lemma add_correct :
  add_spec Coll_impl Iter_impl add_impl -∗
  add_spec Coll Iter add.
Proof.
  iIntros "#spec". iIntros (c x) "!>". iIntros (φ) "Hc Hφ".
  unfold add. wp_pures. wp_bind (add_impl _).
  iDestruct "Hc" as (? ? ?) "(? & Ht)". iDestruct "Ht" as (t) "(Ht & #HI & _)".
  iMod (trace_is_inv with "Ht HI") as "(Ht & %)".
  iApply ("spec" with "[$]"). iIntros "!>" (?) "Hc". wp_pures.
  iApply (wp_emit with "[$Ht $HI]"); eauto.
  by apply iterator_trace_add.
  iIntros "!> Ht". iApply ("Hφ" $! (_, # (length t + 1)%nat)%V). unfold Coll.
  iExists _, _. iFrame. iSplitR; eauto. iExists _. iFrame "HI ∗". iPureIntro. go.
Qed.

Lemma remove_correct :
  remove_spec Coll_impl Iter_impl remove_impl -∗
  remove_spec Coll Iter remove.
Proof.
  iIntros "#spec". iIntros (c x) "!>". iIntros (φ) "Hc Hφ".
  unfold remove. wp_pures. wp_bind (remove_impl _).
  iDestruct "Hc" as (? ? ?) "(? & Ht)". iDestruct "Ht" as (t) "(Ht & #HI & _)".
  iMod (trace_is_inv with "Ht HI") as "(Ht & %)".
  iApply ("spec" with "[$]"). iIntros "!>" (?) "Hc". wp_pures.
  iApply (wp_emit with "[$Ht $HI]"); eauto.
  by apply iterator_trace_remove.
  iIntros "!> Ht". iApply ("Hφ" $! (_, # (length t + 1)%nat)%V). unfold Coll.
  iExists _, _. iFrame. iSplitR; eauto. iExists _. iFrame "HI ∗". iPureIntro. go.
Qed.
