From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import invariants.
From intensional.heap_lang Require Import lifting proofmode notation.
From intensional.heap_lang Require Import adequacy.
Set Default Proof Using "Type".
Implicit Types t : list val.

(** ** Stack with a [foreach] operation (Section 5.4) *)

(* Minor remark: compared to the paper, we assume a [create] function to
   initialize the library, instead of a condition □ (P0 -∗ ∃ s, Stack [] s).
   This is purely a matter of style. *)

(** *** Separation logic specification *)

Notation trace := (list val) (only parsing).

Definition create_spec `{!heapG Σ} P0 (Stack: list val → val → iProp Σ) (create: val) : iProp Σ :=
  {{{ P0 }}}
    create #()
  {{{ s, RET s; Stack [] s }}}.

Definition push_spec `{!heapG Σ} (Stack: list val → val → iProp Σ) (push: val) : iProp Σ :=
  ∀ l s x,
     {{{ Stack l s ∗ ⌜x ≠ #()⌝ }}}
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

Definition foreach_spec `{!heapG Σ} (Stack: list val → val → iProp Σ) (foreach: val) : iProp Σ :=
  ∀ l s (f: val) (I: list val → iProp Σ),
  {{{ (∀ p x,
        ⌜(p ++ [x]) `prefix_of` l⌝ →
        {{{ I p }}} f x {{{ RET #(); I (p ++ [x]) }}}) ∗
      Stack l s ∗ I []
  }}}
    foreach s f
  {{{ RET #(); Stack l s ∗ I l }}}.

Definition stacklib_spec `{!heapG Σ} (P0 : iProp Σ) (lib: val): iProp Σ :=
  ∃ (Stack : list val → val → iProp Σ),
    match lib with
    | (create, push, pop, foreach)%V =>
      create_spec P0 Stack create ∗
      push_spec Stack push ∗
      pop_spec Stack pop ∗
      foreach_spec Stack foreach
    | _ => False
    end.

(** *** The trace property [good_trace]: "foreach calls the client function on elements stored in the stack, once each and in the right order". *)

Section Trace.

Definition traversal_trace (f: val) (l: list val): trace :=
  l ≫= (λ x, [(#"call:foreach_client", (f, x))%V; (#"ret:foreach_client", f)%V]).

Inductive good_trace_for : list val → trace → Prop :=
| good_trace_for_nil: good_trace_for [] []
| good_trace_for_push x l t:
    good_trace_for l t →
    good_trace_for (x :: l) (t ++ [(#"call:push", x)%V; (#"ret:push", #())%V])
| good_trace_for_pop_nil t:
    good_trace_for [] t →
    good_trace_for [] (t ++ [(#"call:pop", #())%V; (#"ret:pop", #())%V])
| good_trace_for_pop x l t:
    good_trace_for (x :: l) t →
    good_trace_for l (t ++ [(#"call:pop", #())%V; (#"ret:pop", x)%V])
| good_trace_for_foreach l t f:
    good_trace_for l t →
    good_trace_for l (t ++ [(#"call:foreach", f)%V]
                        ++ traversal_trace f l
                        ++ [(#"ret:foreach", #())%V])
.

Definition good_trace (t: trace) :=
  ∃ l t', t `prefix_of` t' ∧ good_trace_for l t'.

Lemma good_trace_nil : good_trace [].
Proof. eexists [],[]. split; eauto. constructor. Qed.

Lemma traversal_trace_app f l l' :
  traversal_trace f (l ++ l') = traversal_trace f l ++ traversal_trace f l'.
Proof. unfold traversal_trace. apply bind_app. Qed.

Lemma traversal_trace_prefix f l l' :
  l `prefix_of` l' →
  traversal_trace f l `prefix_of` traversal_trace f l'.
Proof.
  revert l'. induction l as [| x l]; cbn; intros l'.
  { intros [? ->]. cbn. eexists; eauto. }
  { intros [? ->]. cbn. do 2 apply prefix_cons.
    rewrite bind_app. by apply prefix_app_r. }
Qed.

End Trace.

(** *** Definition and correctness of the wrapper code *)

Module Wrap.
Section S.
Context {Σ: gFunctors}.
Context `{heapG Σ}.
Context (N: namespace).

Context (stack_impl: list val → val → iProp Σ).
Context (push_impl pop_impl create_impl foreach_impl: val).

Definition push : val :=
  λ: "s" "x",
    Emit (#"call:push", "x") ;;
    push_impl "s" "x" ;;
    Emit (#"ret:push", #()).

Definition pop : val :=
  λ: "s",
    Emit (#"call:pop", #()) ;;
    let: "r" := pop_impl "s" in
    Emit (#"ret:pop", "r") ;;
    "r".

Definition create : val :=
  create_impl.

Definition foreach : val :=
  λ: "s" "f",
    Emit (#"call:foreach", "f") ;;
    foreach_impl "s" (λ: "x",
      Emit (#"call:foreach_client", ("f", "x")) ;;
      "f" "x" ;;
      Emit (#"ret:foreach_client", "f")
    ) ;;
    Emit (#"ret:foreach", #()).

Definition stack_val (l: list val) (s: val): iProp Σ :=
  stack_impl l s ∗ trace_inv N good_trace ∗
  ∃ t, ⌜good_trace_for l t⌝ ∗ trace_is t.

Lemma create_correct P0 :
  create_spec P0 stack_impl create_impl -∗
  create_spec (P0 ∗ trace_is [] ∗ trace_inv N good_trace) stack_val create.
Proof.
  iIntros "#create_impl_spec". iModIntro.
  iIntros (φ) "(H0 & Htr & HI) Hφ". unfold create.
  iApply ("create_impl_spec" with "[$]").
  iIntros "!>" (?) "?". iApply "Hφ". rewrite /stack_val.
  iFrame. iExists []. iFrame. iPureIntro. apply good_trace_for_nil.
Qed.

Lemma push_correct :
  push_spec stack_impl push_impl -∗
  push_spec stack_val push.
Proof.
  iIntros "#push_impl_spec" (l s x) "!>".
  iIntros (φ) "(Hs & %) Hφ". unfold push.
  iDestruct "Hs" as "(Hs & #HI & Htr)". iDestruct "Htr" as (t) "(Hgood & Ht)".
  iDestruct "Hgood" as %Hgood.
  wp_pures. wp_bind (Emit _).
  iApply (wp_emit with "[$Ht $HI]"); eauto.
  { do 2 eexists. split; cycle 1.
    by eapply good_trace_for_push, Hgood.
    apply prefix_app. eexists; eauto. }
  iIntros "!> Ht". wp_pures. wp_bind (push_impl _ _).
  iApply ("push_impl_spec" with "[Hs]"). by iFrame. iIntros "!> Hs".
  wp_pures.
  iApply (wp_emit with "[$Ht $HI]"); eauto.
  { do 2 eexists. split; [reflexivity|].
    rewrite -app_assoc /=. by eapply good_trace_for_push. }
  iIntros "!> Ht". iApply "Hφ".
  rewrite /stack_val; iFrame "HI∗".
  iExists _; iFrame. iPureIntro.
  rewrite -app_assoc /=. by eapply good_trace_for_push.
Qed.

Lemma pop_correct :
  pop_spec stack_impl pop_impl -∗
  pop_spec stack_val pop.
Proof.
  iIntros "#pop_impl_spec" (l s) "!>".
  iIntros (φ) "Hs Hφ". unfold pop.
  iDestruct "Hs" as "(Hs & #HI & Htr)". iDestruct "Htr" as (t) "(Hgood & Ht)".
  iDestruct "Hgood" as %Hgood.
  wp_pures. wp_bind (Emit _).
  iApply (wp_emit with "[$Ht $HI]"); eauto.
  { destruct l; eexists _,_; split;
    [| by eapply good_trace_for_pop_nil |
     | by eapply good_trace_for_pop ];
    eexists; rewrite -app_assoc //=. }
  iIntros "!> Ht". wp_pures. wp_bind (pop_impl _).
  iApply ("pop_impl_spec" with "Hs"). iIntros "!>" (v) "Hs".
  wp_pures. wp_bind (Emit _).
  destruct l as [|x l'].
  { iDestruct "Hs" as "(-> & Hs)".
    iApply (wp_emit with "[$Ht $HI]"); eauto.
    { rewrite -app_assoc /=. eexists _,_. split.
      2: eapply good_trace_for_pop_nil; eauto. eauto. }
    iIntros "!> Ht". wp_pures. iApply "Hφ". iSplitR; first done.
    rewrite /stack_val; iFrame "HI∗".
    iExists _. iFrame. iPureIntro.
    rewrite -app_assoc/=. by apply good_trace_for_pop_nil. }
  { iDestruct "Hs" as "(-> & Hs)".
    iApply (wp_emit with "[$Ht $HI]"); eauto.
    { rewrite -app_assoc /=. eexists _,_. split.
      2: eapply good_trace_for_pop; eauto. eauto. }
    iIntros "!> Ht". wp_pures. iApply "Hφ". iSplitR; first done.
    rewrite /stack_val; iFrame "HI∗".
    iExists _. iFrame. iPureIntro.
    rewrite -app_assoc/=. by apply good_trace_for_pop. }
Qed.

Lemma foreach_correct :
  foreach_spec stack_impl foreach_impl -∗
  foreach_spec stack_val foreach.
Proof.
  iIntros "#foreach_impl_spec" (l s f I) "!>".
  iIntros (φ) "(#Hf & Hs & HfI) Hφ". unfold foreach.
  iDestruct "Hs" as "(Hs & #HI & Htr)". iDestruct "Htr" as (t) "(Hgood & Ht)".
  iDestruct "Hgood" as %Hgood.
  wp_pures. wp_bind (Emit _).
  iApply (wp_emit with "[$Ht HI]"); eauto.
  { eexists _,_; split. 2: by eapply good_trace_for_foreach.
    apply prefix_app. eexists; eauto. }
  iIntros "!> Ht". wp_pures. wp_bind (foreach_impl _ _).
  unfold foreach_spec.
  pose (λ p, I p ∗ trace_is (t ++ [(#"call:foreach", f)%V] ++ traversal_trace f p))%I as I'.
  iApply ("foreach_impl_spec" $! _ _ _ I' with "[$Hs $HfI $Ht]").
  { iIntros (p x Hpl φ') "!> HfI Hφ'". wp_pures. wp_bind (Emit _).
    rewrite {1}/I'. iDestruct "HfI" as "(HfI & Htr)".
    iApply (wp_emit with "[$Htr $HI]"); eauto.
    { rewrite -!app_assoc. eexists _,_. split.
      2: by apply good_trace_for_foreach.
      do 2 apply prefix_app. apply prefix_app_r. transitivity (traversal_trace f (p ++ [x])).
      2: by apply traversal_trace_prefix.
      rewrite traversal_trace_app /=. apply prefix_app. eexists; eauto. }
    iIntros "!> Htr". wp_pures. wp_bind (f x).
    iApply ("Hf" with "[] HfI"); eauto. iIntros "!> HfI". wp_pures.
    iApply (wp_emit with "[$Htr $HI]"); eauto.
    { rewrite -!app_assoc. eexists _,_. split.
      2: by apply good_trace_for_foreach.
      do 2 apply prefix_app. apply prefix_app_r. transitivity (traversal_trace f (p ++ [x])).
      2: by apply traversal_trace_prefix.
      rewrite traversal_trace_app /=. apply prefix_app. eexists; eauto. }
    iIntros "!> Htr". iApply "Hφ'". rewrite /I' traversal_trace_app /= -!app_assoc. iFrame. }
  iIntros "!> (Hs & (HI' & Htr))". wp_pures.
  iApply (wp_emit with "[Htr HI]"); eauto.
  { eexists _,_. split; eauto. rewrite -app_assoc. by eapply good_trace_for_foreach. }
  iIntros "!> Htr". iApply "Hφ". iFrame "HI∗". iExists _. iFrame. iPureIntro.
  rewrite -app_assoc. by apply good_trace_for_foreach.
Qed.

End S.

(** Wrapping code for an entire library *)
Definition lib (lib_impl: val): val :=
  match lib_impl with
  | (create_impl, push_impl, pop_impl, foreach_impl)%V =>
    (create create_impl, push push_impl, pop pop_impl, foreach foreach_impl)
  | _ => #()
  end.

(** Correctness of the wrapper at the level of the library *)
Lemma correct `{!heapG Σ} N P0 (lib_impl: val):
  stacklib_spec P0 lib_impl -∗
  stacklib_spec (P0 ∗ trace_is [] ∗ trace_inv N good_trace) (lib lib_impl).
Proof.
  iIntros "S". iDestruct "S" as (stack_val_impl) "S".
  repeat case_match; eauto. iDestruct "S" as "(Hcreate & Hpush & Hpop & Hforeach)".
  subst. unfold stacklib_spec.
  iExists (stack_val N stack_val_impl). repeat iSplit.
  iApply create_correct; eauto.
  iApply push_correct; eauto.
  iApply pop_correct; eauto.
  iApply foreach_correct; eauto.
Qed.

End Wrap.

(** *** Adequacy *)

Definition stacklibN := nroot .@ "traversable_stacklib".
Definition empty_state : state := Build_state ∅ [] ∅.

(** The trace property [good_trace] is satisfied at every step of the execution,
    at the level of the operational semantics *)
Lemma wrap_stacklib_correct (e: val → expr) (lib: val):
  (∀ `(heapG Σ), ⊢ stacklib_spec True lib) →
  (∀ `(heapG Σ), ⊢ ∀ P lib, stacklib_spec P lib -∗ {{{ P }}} e lib {{{ v, RET v; True }}}) →
  ∀ σ' e',
    rtc erased_step ([(#();; e (Wrap.lib lib))%E], empty_state) (e', σ') →
    good_trace (heap_lang.trace σ').
Proof.
  set (Σ := #[invΣ; gen_heapΣ loc val; traceΣ; proph_mapΣ proph_id (val * val)]).
  intros Hlib Hctx σ' e' Hsteps.
  eapply (@module_invariance Σ (HeapPreG Σ _ _ _ _)
                             stacklibN (@stacklib_spec Σ) True e #() (Wrap.lib lib)
                             good_trace empty_state).
  { cbn. apply good_trace_nil. }
  { iIntros (? ? ?) "?". by iApply Hctx. }
  { iIntros (? _) "!>". iApply wp_value; eauto. }
  { iIntros (?). iApply Wrap.correct. iApply Hlib. }
  eauto.
Qed.
