From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import invariants.
From intensional.heap_lang Require Import lang lifting proofmode notation adequacy.
From intensional Require Import stdpp_extra tactics.
Set Default Proof Using "Type".
Implicit Types t : list val.

Definition create_spec `{!heapG Σ} P0 (Stack: list val → val → iProp Σ) (create: val) : iProp Σ :=
  {{{ P0 }}}
    create #()
  {{{ s, RET s; Stack [] s }}}.

Definition push_spec `{!heapG Σ} (Stack: list val → val → iProp Σ) (push: val) : iProp Σ :=
  ∀ l s x,
     {{{ Stack l s }}}
       push s x
     {{{ RET #(); Stack (x :: l) s }}}.

Definition pop_spec `{!heapG Σ} (Stack: list val → val → iProp Σ) (pop: val) : iProp Σ :=
  ∀ l s,
   {{{ Stack l s }}}
     pop s
   {{{ v, RET v;
     match l with
     | [] => ⌜ v = #() ⌝ ∗ Stack [] s
     | x :: l' => ⌜ v = x ⌝ ∗ Stack l' s
     end }}}.

Definition stacklib_spec `{!heapG Σ} (P0 : iProp Σ) (lib: val): iProp Σ :=
  ∃ (Stack : list val → val → iProp Σ),
    match lib with
    | (create, push, pop)%V =>
      create_spec P0 Stack create ∗ push_spec Stack push ∗ pop_spec Stack pop
    | _ => False
    end.

Section Trace.

Definition good_stack_trace (t: list val): Prop :=
  ∀ (i: nat) (v: val),
    t !! i = Some (#"pop", v)%V → v ≠ #() →
    ∃ j, (j < i)%nat ∧ t !! j = Some (#"push", v)%V.

Lemma good_stack_trace_nil : good_stack_trace [].
Proof. unfold good_stack_trace; go. Qed.

Lemma good_stack_trace_push t v :
  good_stack_trace t → good_stack_trace (t ++ [(#"push", v)%V]).
Proof. unfold good_stack_trace. go*. Qed.

Lemma good_stack_trace_pop_nil t :
  good_stack_trace t →
  good_stack_trace (t ++ [(#"pop", #())%V]).
Proof. unfold good_stack_trace. go*. Qed.

Lemma good_stack_trace_pop t v i :
  good_stack_trace t →
  t !! i = Some (#"push", v)%V →
  good_stack_trace (t ++ [(#"pop", v)%V]).
Proof. unfold good_stack_trace. go*. Qed.

End Trace.


Module Wrap.
Section S.
Context {Σ: gFunctors}.
Context `{heapG Σ}.
Context (N: namespace).

Context (stack_impl: list val → val → iProp Σ).
Context (push_impl pop_impl create_impl : val).

Definition push : val :=
  λ: "s" "x", push_impl "s" "x" ;; Emit (#"push", "x").

Definition pop : val :=
  λ: "s", let: "r" := pop_impl "s" in Emit (#"pop", "r") ;; "r".

Definition create : val :=
  create_impl.

Definition stack_val (l: list val) (v: val) : iProp Σ :=
  stack_impl l v ∗ trace_inv N good_stack_trace ∗
  ∃ t, trace_is t ∗ ⌜ Forall (λ x, ∃ i, t !! i = Some (#"push", x)%V) l ⌝.

Lemma create_correct P0 :
  create_spec P0 stack_impl create_impl -∗
  create_spec (P0 ∗ trace_is [] ∗ trace_inv N good_stack_trace) stack_val create.
Proof.
  iIntros "#create_impl_spec". iModIntro.
  iIntros (φ) "(H0 & Htr & HI) Hφ". unfold create.
  iApply ("create_impl_spec" with "[$]").
  iIntros "!>" (?) "?". iApply "Hφ". rewrite /stack_val.
  iFrame. iExists []. iFrame. iPureIntro. by apply Forall_nil.
Qed.

Lemma push_correct :
  push_spec stack_impl push_impl -∗
  push_spec stack_val push.
Proof.
  iIntros "#push_impl_spec" (l s x) "!>".
  iIntros (φ) "Hs Hφ". unfold push.
  iDestruct "Hs" as "(Hs & #HI & Htr)". iDestruct "Htr" as (t) "(Ht & %)".
  wp_pures. wp_bind (push_impl _ _).
  iApply ("push_impl_spec" with "Hs"). iIntros "!> Hs". wp_pures.
  iMod (trace_is_inv with "[$] HI") as "(Ht & %)".
  iApply (wp_emit with "[$Ht $HI]"); eauto. by apply good_stack_trace_push.
  iIntros "!> Ht". iApply "Hφ".
  rewrite /stack_val; iFrame "HI∗".
  iExists _; iFrame. iPureIntro. rewrite Forall_cons. split.
  { eexists. go. }
  { eapply Forall_impl. eassumption. cbn. go; eexists; go. }
Qed.

Lemma pop_correct :
  pop_spec stack_impl pop_impl -∗
  pop_spec stack_val pop.
Proof.
  iIntros "#pop_impl_spec" (l s) "!>".
  iIntros (φ) "Hs Hφ". unfold pop.
  iDestruct "Hs" as "(Hs & #HI & Htr)". iDestruct "Htr" as (t) "(Ht & HF)".
  iDestruct "HF" as %HF. wp_pures. wp_bind (pop_impl _).
  iApply ("pop_impl_spec" with "Hs"). iIntros "!>" (v) "Hs".
  iMod (trace_is_inv with "[$] HI") as "(Ht & %)".
  wp_pures. wp_bind (Emit _).
  destruct l as [|x l'].
  { iDestruct "Hs" as "(-> & Hs)".
    iApply (wp_emit with "[$Ht $HI]"); eauto.
    by apply good_stack_trace_pop_nil.
    iIntros "!> Ht". wp_pures. iApply "Hφ". iSplitR; first done.
    rewrite /stack_val; iFrame "HI∗".
    iExists _. iFrame. iPureIntro; eauto. }
  { iDestruct "Hs" as "(-> & Hs)".
    apply Forall_cons in HF as [[i Hti] HF].
    iApply (wp_emit with "[$Ht $HI]"); eauto.
    by eapply good_stack_trace_pop.
    iIntros "!> Ht". wp_pures. iApply "Hφ". iSplitR; first done.
    rewrite /stack_val; iFrame "HI∗".
    iExists _. iFrame. iPureIntro; eauto.
    eapply Forall_impl; [ apply HF |]. cbn. go; eexists; go. }
Qed.

End S.

Definition lib (lib_impl: val): val :=
  match lib_impl with
  | (create_impl, push_impl, pop_impl)%V =>
    (create create_impl, push push_impl, pop pop_impl)
  | _ => #()
  end.

Lemma correct `{!heapG Σ} N P0 (lib_impl: val) :
  stacklib_spec P0 lib_impl -∗
  stacklib_spec (P0 ∗ trace_is [] ∗ trace_inv N good_stack_trace) (lib lib_impl).
Proof.
  iIntros "S". iDestruct "S" as (stack_val_impl) "S".
  repeat case_match; eauto. iDestruct "S" as "(Hcreate & Hpush & Hpop)".
  subst. unfold stacklib_spec.
  iExists (stack_val N stack_val_impl). repeat iSplit.
  iApply create_correct; eauto.
  iApply push_correct; eauto.
  iApply pop_correct; eauto.
Qed.

End Wrap.


Definition stacklibN := nroot .@ "stacklib".
Definition empty_state : state := Build_state ∅ [] ∅.

Lemma wrap_stacklib_correct {Σ} `{heapPreG Σ} (e: val → expr) (lib: val):
  (⊢ ∀ `(heapG Σ), stacklib_spec True lib) →
  (⊢ ∀ `(heapG Σ) P lib, stacklib_spec P lib -∗ {{{ P }}} e lib {{{ v, RET v; True }}}) →
  ∀ σ' e',
    rtc erased_step ([(#();; e (Wrap.lib lib))%E], empty_state) (e', σ') →
    good_stack_trace (trace σ').
Proof.
  intros Hlib Hctx σ' e' Hsteps.
  eapply (@module_invariance Σ _ stacklibN (@stacklib_spec Σ) True e #() (Wrap.lib lib)
                            good_stack_trace empty_state).
  { cbn. apply good_stack_trace_nil. }
  { iIntros (? ? ?) "?". by iApply Hctx. }
  { iIntros (? _) "!>". iApply wp_value; eauto. }
  { iIntros (?). iApply Wrap.correct. iApply Hlib. }
  eauto.
Qed.
