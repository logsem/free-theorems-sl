From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import invariants.
From intensional.heap_lang Require Import lifting proofmode notation.
From intensional.heap_lang Require Import adequacy.
From intensional Require Import stdpp_extra tactics.
Set Default Proof Using "Type".
Implicit Types t : list val.

Definition withRes_spec `{!heapG Σ} (locked: iProp Σ) (unlocked: val → iProp Σ) (withRes: val): iProp Σ :=
  ∀ P Q (f: val),
    {{{ locked ∗ P ∗
        (∀ (y x: val), {{{ unlocked y ∗ P }}} f x {{{ RET #(); unlocked y ∗ Q }}})
    }}}
      withRes f
    {{{ RET #(); locked ∗ Q }}}.

Definition op_spec `{!heapG Σ} (locked: iProp Σ) (unlocked: val → iProp Σ) (op: val): iProp Σ :=
  ∀ (x y: val), {{{ unlocked y }}} op x {{{ RET #(); unlocked y }}}.

Definition bfilelib_spec `{!heapG Σ} (P0: iProp Σ) (lib: val): iProp Σ :=
  ∃ (locked: iProp Σ) (unlocked: val → iProp Σ),
  □ (P0 -∗ locked) ∗
  match lib with
  | (withRes, op)%V =>
    withRes_spec locked unlocked withRes ∗
    op_spec locked unlocked op
  | _ => False
  end.

Section Trace.

Inductive op_trace : list val → Prop :=
| op_trace_nil : op_trace []
| op_trace_call t :
    op_trace t →
    op_trace (t ++ [(#"call:op", #())%V; (#"ret:op", #())%V]).

Inductive withRes_trace : list val → Prop :=
| withRes_trace_nil : withRes_trace []
| withRes_trace_call t t_op f :
    withRes_trace t →
    op_trace t_op →
    withRes_trace (t ++ [(#"call:withRes", f)%V; (#"call", f)%V]
                     ++ t_op
                     ++ [(#"ret", f)%V; (#"ret:withRes", f)%V]).

Definition bfile_trace t :=
  ∃ t', t `prefix_of` t' ∧ withRes_trace t'.

(* *** *)

Definition trace1 t f :=
  ∃ t', withRes_trace t' ∧ t = t' ++ [(#"call:withRes", f)%V].

Definition trace2 t (f:val) :=
  ∃ t' t_op, withRes_trace t'
           ∧ op_trace t_op
           ∧ t = t' ++ [(#"call:withRes", f)%V; (#"call", f)%V] ++ t_op.

Definition trace3 t (f: val) :=
  ∃ t' t_op, withRes_trace t'
           ∧ op_trace t_op
           ∧ t = t' ++ [(#"call:withRes", f)%V; (#"call", f)%V]
                    ++ t_op
                    ++ [(#"ret", f)%V].

End Trace.


Module Wrap.
Section S.
Context {Σ: gFunctors}.
Context `{heapG Σ}.
Context (N: namespace).

Context (locked_impl: iProp Σ) (unlocked_impl: val → iProp Σ).
Context (withRes_impl op_impl : val).

Definition withRes : val :=
  λ: "f",
    Emit (#"call:withRes", "f") ;;
    withRes_impl (λ: "x",
      Emit (#"call", "f") ;; "f" "x" ;; Emit (#"ret", "f")
    ) ;;
    Emit (#"ret:withRes", "f").

Definition op : val :=
  λ: "x",
    Emit (#"call:op", #()) ;;
    op_impl "x" ;;
    Emit (#"ret:op", #()).

Definition T0 : iProp Σ :=
  ∃ t, trace_is t ∗ trace_inv N bfile_trace ∗ ⌜ withRes_trace t ⌝.

Definition T1 f : iProp Σ :=
  ∃ t, trace_is t ∗ trace_inv N bfile_trace ∗ ⌜ trace1 t f ⌝.

Definition T2 f : iProp Σ :=
  ∃ t, trace_is t ∗ trace_inv N bfile_trace ∗ ⌜ trace2 t f ⌝.

Definition T3 f : iProp Σ :=
  ∃ t, trace_is t ∗ trace_inv N bfile_trace ∗ ⌜ trace3 t f ⌝.

Definition unlocked (x: val) : iProp Σ :=
  ∃ (y z:val), ⌜x = (y, z)%V⌝ ∗ unlocked_impl y ∗ T2 z.

Definition locked : iProp Σ :=
  locked_impl ∗ T0.

Lemma withRes_correct :
  withRes_spec locked_impl unlocked_impl withRes_impl -∗
  withRes_spec locked unlocked withRes.
Proof.
  iIntros "#spec" (P Q f φ) "!> (Hl & HP & #HS) Hφ".
  iDestruct "Hl" as "(Hl & Ht0)". iDestruct "Ht0" as (t) "(Ht & #Hi & %)".
  iMod (trace_is_inv with "Ht Hi") as "[Ht %]".
  unfold withRes. wp_pures. wp_bind (Emit _).
  iApply (wp_emit with "[$Ht $Hi]"); eauto.
  { eexists. split. 2: eapply withRes_trace_call.
    by apply prefix_app, prefix_cons, prefix_nil.
    auto. constructor. }
  iIntros "!> Ht". wp_pures. wp_bind (withRes_impl _).
  iApply ("spec" $! (P ∗ T1 f)%I (Q ∗ T3 f)%I with "[$Hl $HP Ht]").
  { iSplitL "Ht".
    { iExists _. iFrame "Hi ∗". iPureIntro. unfold trace1. go. }
    iIntros (y x ψ) "!> (Hu & [HP Ht1]) Hψ". wp_pures. wp_bind (Emit _).
    iDestruct "Ht1" as (t') "(Ht' & _ & Ht1)". iDestruct "Ht1" as %Ht1.
    iApply (wp_emit with "[$Ht' $Hi]"); eauto.
    { destruct Ht1 as [t'' [? ->]]. eexists. split. 2: eapply withRes_trace_call.
      rewrite -app_assoc. apply prefix_app, prefix_cons, prefix_cons, prefix_nil.
      eauto. constructor. }
    iIntros "!> Ht'". wp_pures. wp_bind (f _).
    iApply ("HS" $! (y, f)%V with "[Hu Ht' $HP]").
    { iExists _, _. iSplitR. done. iFrame. iExists _. iFrame "Hi ∗". iPureIntro.
      destruct Ht1 as [t'' [? ->]]. exists t'', []. repeat split; eauto. constructor.
      by list_simplifier. }
    iIntros "!> [Hu HQ]". wp_pures. iDestruct "Hu" as (y' z) "(% & Hy & Ht2)".
    simplify_eq. iDestruct "Ht2" as (t'') "(Ht'' & _ & Ht2)". iDestruct "Ht2" as %Ht2.
    destruct Ht2 as [t''' [t_op (? & ? & ->)]].
    iApply (wp_emit with "[$Ht'' $Hi]"); eauto.
    { eexists. split. 2: eapply withRes_trace_call. rewrite -app_assoc. cbn.
      apply prefix_app, prefix_cons, prefix_cons, prefix_app, prefix_cons, prefix_nil.
      all: eauto. }
    iIntros "!> Ht'''". iApply "Hψ". iFrame. iExists _. iFrame "Hi ∗".
    iPureIntro. exists t''', t_op. repeat split; eauto. by list_simplifier. }
  iIntros "!> (Hl & HQ & Ht3)". iDestruct "Ht3" as (t') "(Ht' & _ & Ht3)".
  iDestruct "Ht3" as %Ht3. destruct Ht3 as [t'' [t_op (? & ? & ->)]].
  wp_pures. iApply (wp_emit with "[$Ht' $Hi]"); eauto.
  { eexists. split. reflexivity. rewrite -!app_assoc. constructor; eauto. }
  iIntros "!> Ht". iApply "Hφ". iFrame. iExists _. iFrame "Hi ∗". iPureIntro.
  rewrite -!app_assoc. constructor; eauto.
Qed.

Lemma op_correct :
  op_spec locked_impl unlocked_impl op_impl -∗
  op_spec locked unlocked op.
Proof.
  iIntros "#spec" (x y φ) "!> Hu Hφ". iDestruct "Hu" as (y' z ->) "(Hu & Ht2)".
  iDestruct "Ht2" as (t) "(Ht & #Hi & Ht2)". iDestruct "Ht2" as %Ht2.
  unfold op. wp_pures. wp_bind (Emit _).
  destruct Ht2 as [t' [t_op (? & ? & ->)]].
  iApply (wp_emit with "[$Ht $Hi]"); eauto.
  { eexists. split. 2: eapply withRes_trace_call. rewrite -!app_assoc.
    apply prefix_app, prefix_cons, prefix_cons.
    3: apply op_trace_call. rewrite -app_assoc.
    apply prefix_app, prefix_cons, prefix_nil. all: eauto. }
  iIntros "!> Ht". wp_pures. wp_bind (op_impl _).
  iApply ("spec" with "Hu"). iIntros "!> Hu". wp_pures.
  iApply (wp_emit with "[$Ht $Hi]"); eauto.
  { eexists. split. 2: eapply withRes_trace_call.
    3: apply op_trace_call; eauto. rewrite -!app_assoc.
    repeat first [ apply prefix_app | apply prefix_cons | apply prefix_nil ].
    eauto. }
  iIntros "!> Ht". iApply "Hφ". iExists _, _. iSplitR. done. iFrame.
  iExists _. iFrame "Hi ∗". iPureIntro. exists t'. eexists. split; [eauto|].
  split. apply op_trace_call; eauto. by list_simplifier.
Qed.

End S.

Definition lib (lib_impl: val): val :=
  match lib_impl with
  | (withRes_impl, op_impl)%V =>
    (withRes withRes_impl, op op_impl)
  | _ => #()
  end.

Lemma correct `{!heapG Σ} N P0 (lib_impl: val):
  bfilelib_spec P0 lib_impl -∗
  bfilelib_spec (P0 ∗ trace_is [] ∗ trace_inv N bfile_trace) (lib lib_impl).
Proof.
  iIntros "S". iDestruct "S" as (locked_impl unlocked_impl) "(#H0 & S)".
  repeat case_match; eauto. iDestruct "S" as "(? & ?)".
  unfold bfilelib_spec.
  iExists (locked N locked_impl), (unlocked N unlocked_impl). repeat iSplit.
  { iIntros "!> (HP0 & ? & #Hi)". iDestruct ("H0" with "HP0") as "?". iFrame.
    iExists _. iFrame "Hi ∗". iPureIntro. constructor. }
  iApply withRes_correct; eauto.
  iApply op_correct; eauto.
Qed.

End Wrap.

Definition bfilelibN := nroot .@ "bfilelib".
Definition empty_state : state := Build_state ∅ [] ∅.

Lemma wrap_bfilelib_correct {Σ} `{heapPreG Σ} (e: val → expr) (lib: val):
  (⊢ ∀ `{heapG Σ}, bfilelib_spec True lib) →
  (⊢ ∀ `{heapG Σ} P lib, bfilelib_spec P lib -∗ {{{ P }}} e lib {{{ v, RET v; True }}}) →
  ∀ σ' e',
    rtc erased_step ([(#();; e (Wrap.lib lib))%E], empty_state) (e', σ') →
    bfile_trace (trace σ').
Proof.
  intros Hlib Hctx σ' e' Hsteps.
  eapply (@module_invariance Σ _ bfilelibN (@bfilelib_spec Σ) True e #() (Wrap.lib lib)
                            bfile_trace empty_state).
  { cbn. exists []. split; eauto; constructor. }
  { iIntros (? ? ?) "?". by iApply Hctx. }
  { iIntros (? _) "!>". iApply wp_value; eauto. }
  { iIntros (?). iApply Wrap.correct. iApply Hlib. }
  eauto.
Qed.
