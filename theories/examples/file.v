From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import invariants.
From intensional.heap_lang Require Import lifting proofmode notation.
From intensional.heap_lang Require Import adequacy.
From intensional.examples Require Import stdpp_extra tactics.
Set Default Proof Using "Type".
Implicit Types t : list val.

Definition open_spec `{!heapG Σ} (isClosed isOpen: iProp Σ) (open: val): iProp Σ :=
  {{{ isClosed }}} open #() {{{ RET #(); isOpen }}}.

Definition close_spec `{!heapG Σ} (isClosed isOpen: iProp Σ) (close: val): iProp Σ :=
  {{{ isOpen }}} close #() {{{ RET #(); isClosed }}}.

Definition read_spec `{!heapG Σ} (isOpen: iProp Σ) (read: val): iProp Σ :=
  {{{ isOpen }}} read #() {{{ v, RET v; isOpen }}}.

Definition filelib_spec `{!heapG Σ} (P0: iProp Σ) (lib: val): iProp Σ :=
  ∃ (isOpen isClosed: iProp Σ),
  □ (P0 -∗ isClosed) ∗
  match lib with
  | (open, close, read)%V =>
    open_spec isClosed isOpen open ∗
    close_spec isClosed isOpen close ∗
    read_spec isOpen read
  | _ => False
  end.

Section Trace.

Definition noclose (t: list val) (m n: nat) :=
  ∀ (k:nat) v, m < k < n → t !! k ≠ Some (#"close", v)%V.

Definition isopen (t: list val) (n: nat) :=
  ∃ (m:nat), m < n ∧ t !! m = Some (#"open", #())%V ∧ noclose t m n.

Definition file_trace (t: list val) :=
  ∀ (n:nat), t !! n = Some (#"read", #())%V ∨ t !! n = Some (#"close", #())%V →
             isopen t n.

Lemma noclose_open t n m :
  noclose t n m →
  noclose (t ++ [(#"open", #())%V]) n m.
Proof. unfold noclose. go. Qed.

Lemma isopen_open t n :
  isopen t n →
  isopen (t ++ [(#"open", #())%V]) n.
Proof. unfold isopen, noclose. go*. Qed.

Lemma isopen_open' t n e :
  isopen t n →
  n <= length t →
  isopen (t ++ [e]) n.
Proof. unfold isopen, noclose. go*. Qed.

Lemma noclose_open_last t :
  noclose (t ++ [(#"open", #())%V]) (length t) (length t + 1).
Proof. unfold noclose. go. Qed.

Lemma noclose_read_last t v m :
  noclose t m (length t) →
  noclose (t ++ [(#"read", v)%V]) m (length t + 1).
Proof.
  unfold noclose. intros HH k v' ?. go.
  specialize (HH k v' ltac:(go)); go.
Qed.

Lemma isopen_open_last t :
  isopen (t ++ [(#"open", #())%V]) (length t + 1).
Proof. exists (length t). unfold noclose; go*. Qed.

Lemma isopen_read_last t v :
  isopen t (length t) →
  isopen (t ++ [(#"read", v)%V]) (length t + 1).
Proof.
  intros [m ?]. go. exists m. split_and!; go. by apply noclose_read_last.
Qed.

Lemma file_trace_open t :
  file_trace t →
  file_trace (t ++ [(#"open", #())%V]).
Proof. unfold file_trace. intros. apply isopen_open. go. Qed.

Lemma file_trace_close t :
  isopen t (length t) →
  file_trace t →
  file_trace (t ++ [(#"close", #())%V]).
Proof. unfold file_trace. intros. go; apply isopen_open'; go. Qed.

Lemma file_trace_read t v :
  isopen t (length t) →
  file_trace t →
  file_trace (t ++ [(#"read", v)%V]).
Proof. unfold file_trace. intros. go; apply isopen_open'; go. Qed.

Lemma file_trace_nil : file_trace [].
Proof. unfold file_trace; go. Qed.

End Trace.


Module Wrap.
Section S.
Context {Σ: gFunctors}.
Context `{heapG Σ}.
Context (N: namespace).

Context (isOpen_impl isClosed_impl : iProp Σ).
Context (open_impl close_impl read_impl : val).

Definition open : val :=
  λ: "_", open_impl #() ;; Emit (#"open", #()).

Definition close : val :=
  λ: "_", close_impl #() ;; Emit (#"close", #()).

Definition read : val :=
  λ: "_", read_impl #() ;; Emit (#"read", #()).

Definition isOpen : iProp Σ :=
  isOpen_impl ∗ trace_inv N file_trace ∗
  ∃ t, trace_is t ∗ ⌜ isopen t (length t) ⌝.

Definition isClosed : iProp Σ :=
  isClosed_impl ∗ trace_inv N file_trace ∗ ∃ t, trace_is t.

Lemma open_correct :
  open_spec isClosed_impl isOpen_impl open_impl -∗
  open_spec isClosed isOpen open.
Proof.
  iIntros "#spec". iIntros "!>" (φ) "(Hc & #Hi & Ht) Hφ". unfold open.
  wp_pures. wp_bind (open_impl _). iApply ("spec" with "[$]").
  iIntros "!> Ho". wp_pures. iDestruct "Ht" as (t) "Ht".
  iMod (trace_is_inv with "Ht Hi") as "[Ht Hft]". iDestruct "Hft" as %Hft.
  iApply (wp_emit with "[$Hi $Ht]"); eauto. by apply file_trace_open.
  iNext. iIntros "Ht". iApply "Hφ". rewrite /isOpen. iFrame "Hi ∗".
  iExists _. iFrame. iPureIntro. go. apply isopen_open_last.
Qed.

Lemma close_correct :
  close_spec isClosed_impl isOpen_impl close_impl -∗
  close_spec isClosed isOpen close.
Proof.
  iIntros "#spec". iIntros "!>" (φ) "(Hc & #Hi & Ht) Hφ". unfold close.
  wp_pures. wp_bind (close_impl _). iApply ("spec" with "[$]").
  iIntros "!> Hc". wp_pures. iDestruct "Ht" as (t) "(Ht & %)".
  iMod (trace_is_inv with "Ht Hi") as "[Ht %]".
  iApply (wp_emit with "[$]"); eauto. by apply file_trace_close.
  iNext. iIntros "Ht". iApply "Hφ". rewrite /isClosed. iFrame "Hi ∗".
  iExists _. iFrame.
Qed.

Lemma read_correct :
  read_spec isOpen_impl read_impl -∗
  read_spec isOpen read.
Proof.
  iIntros "#spec". iIntros "!>" (φ) "(Hc & #Hi & Ht) Hφ". unfold read.
  wp_pures. wp_bind (read_impl _). iApply ("spec" with "[$]").
  iIntros "!>" (?) "Ho". wp_pures. iDestruct "Ht" as (t) "(Ht & %)".
  iMod (trace_is_inv with "Ht Hi") as "[Ht %]".
  iApply (wp_emit with "[$Hi $Ht]"); eauto. by apply file_trace_read.
  iNext. iIntros "Ht". iApply "Hφ". rewrite /isOpen. iFrame "Hi ∗".
  iExists _. iFrame. iPureIntro. go; apply isopen_read_last; go.
Qed.

End S.

Definition lib (lib_impl: val): val :=
  match lib_impl with
  | (open_impl, close_impl, read_impl)%V =>
    (open open_impl, close close_impl, read read_impl)
  | _ => #()
  end.

Lemma correct `{!heapG Σ} N P0 (lib_impl: val) :
  filelib_spec P0 lib_impl -∗
  filelib_spec (P0 ∗ trace_is [] ∗ trace_inv N file_trace) (lib lib_impl).
Proof.
  iIntros "S". iDestruct "S" as (isOpen_impl isClosed_impl) "(#H0 & S)".
  repeat case_match; eauto. iDestruct "S" as "(Ho & Hc & Hr)".
  subst. unfold filelib_spec.
  iExists (isOpen N isOpen_impl), (isClosed N isClosed_impl).
  repeat iSplit.
  { iIntros "!> (HP0 & ? & ?)". iDestruct ("H0" with "HP0") as "Hci".
    iFrame. eauto. }
  iApply open_correct; eauto.
  iApply close_correct; eauto.
  iApply read_correct; eauto.
Qed.

End Wrap.

Definition filelibN := nroot .@ "filelib".
Definition empty_state : state := Build_state ∅ [] ∅.

Lemma wrap_filelib_correct (e: val → expr) (lib: val):
  (∀ `(heapG Σ), ⊢ filelib_spec True lib) →
  (∀ `(heapG Σ), ⊢ ∀ P lib, filelib_spec P lib -∗ {{{ P }}} e lib {{{ v, RET v; True }}}) →
  ∀ σ' e',
    rtc erased_step ([(#();; e (Wrap.lib lib))%E], empty_state) (e', σ') →
    file_trace (trace σ').
Proof.
  set (Σ := #[invΣ; gen_heapΣ loc val; traceΣ; proph_mapΣ proph_id (val * val)]).
  intros Hlib Hctx σ' e' Hsteps.
  eapply (@module_invariance Σ (HeapPreG Σ _ _ _ _)
                             filelibN (@filelib_spec Σ) True e #() (Wrap.lib lib)
                             file_trace empty_state).
  { cbn. apply file_trace_nil. }
  { iIntros (? ? ?) "?". by iApply Hctx. }
  { iIntros (? _) "!>". iApply wp_value; eauto. }
  { iIntros (?). iApply Wrap.correct. iApply Hlib. }
  eauto.
Qed.
