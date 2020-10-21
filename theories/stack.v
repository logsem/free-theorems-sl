From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import invariants.
From intensional.heap_lang Require Import lifting proofmode notation.
From intensional.heap_lang Require Import adequacy.
Set Default Proof Using "Type".

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

Instance stacklib_persistent `{!heapG Σ} P0 lib : Persistent (stacklib_spec P0 lib).
Proof.
  apply bi.exist_persistent. intro.
  repeat case_match; try typeclasses eauto.
Qed.


Section Trace.

Print event. (* event = string * val *)

Definition good_stack_trace (t: list event): Prop :=
  ∀ (i: nat) (v: val),
    t !! i = Some ("pop", v) → v ≠ #() →
    ∃ j, (j < i)%nat ∧ t !! j = Some ("push", v).

Lemma good_stack_trace_nil : good_stack_trace [].
Proof.
  intros i v Hti. rewrite lookup_nil in Hti; congruence.
Qed.

Lemma good_stack_trace_push t v :
  good_stack_trace t → good_stack_trace (t ++ [("push", v)]).
Proof.
  intros Ht i u [Hi|[_ Hi]]%lookup_app_Some Hv; cycle 1.
  { set X := (i - length t)%nat in Hi. destruct X.
    all: cbn in Hi; inversion Hi. }
  specialize (Ht i u Hi) as [j [? ?]]; auto. exists j. split; eauto.
  rewrite lookup_app_l //. eapply lookup_lt_Some; eauto.
Qed.

Lemma lookup_snoc_Some A (l: list A) (x y: A) (i: nat) :
  (l ++ [x]) !! i = Some y ↔
  l !! i = Some y ∨
  (i = length l ∧ y = x).
Proof.
  rewrite lookup_app_Some. split; intros [H|[H1 H2]]; eauto.
  { destruct (decide (i - length l = 0)%nat) as [e|].
    { rewrite e /= in H2. inversion H2; subst; eauto. right.
      split; auto. assert (i ≤ length l)%nat by lia. lia. }
    rewrite lookup_cons_ne_0 // in H2. }
  { subst. right. split; eauto. rewrite Nat.sub_diag //=. }
Qed.

Lemma good_stack_trace_pop_nil t :
  good_stack_trace t →
  good_stack_trace (t ++ [("pop", #())]).
Proof.
  intros Hgood i v Hti Hv.
  apply lookup_snoc_Some in Hti as [Hti | [_ ?]].
  { specialize (Hgood _ _ Hti Hv) as [j [? ?]]. exists j; split; eauto.
    rewrite lookup_app_l //. apply lookup_lt_is_Some_1; eauto. }
  { congruence. }
Qed.

Lemma good_stack_trace_pop t v i :
  good_stack_trace t →
  t !! i = Some ("push", v) →
  good_stack_trace (t ++ [("pop", v)]).
Proof.
  intros Hgood Hti j v' Htj Hv'.
  apply lookup_snoc_Some in Htj as [Htj|[-> Hvv']].
  { specialize (Hgood _ _ Htj Hv') as [k [? ?]].
    exists k. split; eauto. rewrite lookup_app_l //.
    apply lookup_lt_is_Some_1; eauto. }
  { inversion Hvv'; subst.
    assert (i < length t)%nat by (apply lookup_lt_is_Some_1; eauto).
    exists i. split.
    - eapply (Nat.lt_le_trans _ (length t)%nat); eauto. (* lia. ??? *)
    - rewrite lookup_app_l //. }
Qed.

End Trace.


Module Wrap.
Section S.
Context {Σ: gFunctors}.
Context `{heapG Σ}.
Context (N: namespace).

Context (stack_impl: list val → val → iProp Σ).
Context (push_impl pop_impl create_impl : val).

Definition push : val :=
  λ: "s" "x", push_impl "s" "x" ;; Emit "push" "x".

Definition pop : val :=
  λ: "s", let: "r" := pop_impl "s" in Emit "pop" "r" ;; "r".

Definition create : val :=
  create_impl.

Definition stack_val (l: list val) (v: val) : iProp Σ :=
  stack_impl l v ∗ trace_inv N good_stack_trace ∗
  ∃ t, trace_is t ∗ ⌜good_stack_trace t⌝ ∗
  ⌜ Forall (λ x, ∃ i, t !! i = Some ("push", x)) l ⌝.

Lemma create_correct P0 :
  create_spec P0 stack_impl create_impl -∗
  create_spec (P0 ∗ trace_is [] ∗ trace_inv N good_stack_trace) stack_val create.
Proof.
  iIntros "#create_impl_spec". iModIntro.
  iIntros (φ) "(H0 & Htr & HI) Hφ". unfold create.
  iApply ("create_impl_spec" with "[$]").
  iIntros "!>" (?) "?". iApply "Hφ". rewrite /stack_val.
  iFrame. iExists []. iFrame. iPureIntro; split.
  by apply good_stack_trace_nil.
  by apply Forall_nil.
Qed.

Lemma push_correct :
  push_spec stack_impl push_impl -∗
  push_spec stack_val push.
Proof.
  iIntros "#push_impl_spec" (l s x) "!>".
  iIntros (φ) "Hs Hφ". unfold push.
  iDestruct "Hs" as "(Hs & #HI & Htr)". iDestruct "Htr" as (t) "(Ht & Hgood & HF)".
  iDestruct "Hgood" as %Hgood. iDestruct "HF" as %HF.
  wp_pures. wp_bind (push_impl _ _).
  iApply ("push_impl_spec" with "Hs"). iIntros "!> Hs".
  wp_pures.
  eapply good_stack_trace_push in Hgood.
  iApply (wp_emit with "[$Ht $HI]"); eauto.
  iIntros "!> Ht". iApply "Hφ".
  rewrite /stack_val; iFrame "HI∗".
  iExists _; iFrame. iPureIntro; split; eauto.
  rewrite Forall_cons. split.
  { exists (length t). by apply list_lookup_middle. }
  { eapply Forall_impl; [ apply HF |]. cbn.
    intros v [i Hti]. exists i. by apply lookup_app_l_Some. }
Qed.

Lemma pop_correct :
  pop_spec stack_impl pop_impl -∗
  pop_spec stack_val pop.
Proof.
  iIntros "#pop_impl_spec" (l s) "!>".
  iIntros (φ) "Hs Hφ". unfold pop.
  iDestruct "Hs" as "(Hs & #HI & Htr)". iDestruct "Htr" as (t) "(Ht & Hgood & HF)".
  iDestruct "Hgood" as %Hgood. iDestruct "HF" as %HF.
  wp_pures. wp_bind (pop_impl _).
  iApply ("pop_impl_spec" with "Hs"). iIntros "!>" (v) "Hs".
  wp_pures. wp_bind (Emit _ _).
  destruct l as [|x l'].
  { iDestruct "Hs" as "(-> & Hs)".
    apply good_stack_trace_pop_nil in Hgood.
    iApply (wp_emit with "[$Ht $HI]"); eauto.
    iIntros "!> Ht". wp_pures. iApply "Hφ". iSplitR; first done.
    rewrite /stack_val; iFrame "HI∗".
    iExists _. iFrame. iPureIntro; split; eauto. }
  { iDestruct "Hs" as "(-> & Hs)".
    apply Forall_cons in HF as [[i Hti] HF].
    eapply good_stack_trace_pop in Hgood; eauto.
    iApply (wp_emit with "[$Ht $HI]"); eauto.
    iIntros "!> Ht". wp_pures. iApply "Hφ". iSplitR; first done.
    rewrite /stack_val; iFrame "HI∗".
    iExists _. iFrame. iPureIntro; split; eauto.
    eapply Forall_impl; [ apply HF |]. cbn.
    intros v [j Htj].
    destruct (decide (i = j)) as [<-|].
    { rewrite Htj in Hti. inversion Hti; subst.
      exists i. rewrite lookup_app_l //. apply lookup_lt_is_Some_1; eauto. }
    { exists j. rewrite lookup_app_l //. apply lookup_lt_is_Some_1; eauto. } }
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
  iIntros "#S". iDestruct "S" as (stack_val_impl) "S".
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
  (⊢ ∀ `{heapG Σ}, stacklib_spec True lib) →
  (⊢ ∀ `{heapG Σ} P lib, stacklib_spec P lib -∗ {{{ P }}} e lib {{{ v, RET v; True }}}) →
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
