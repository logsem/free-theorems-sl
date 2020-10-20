From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import invariants.
From intensional.heap_lang Require Import lifting proofmode notation.
Set Default Proof Using "Type".

Definition push : val :=
  λ: "s" "x",
    let: "l" := !"s" in
    let: "l'" := SOME (ref ("x", "l")) in
    "s" <- "l'".

Definition pop : val :=
  λ: "s",
    match: !"s" with
      NONE => #()
    | SOME "l" =>
      let: "x" := Fst !"l" in
      let: "t" := Snd !"l" in
      "s" <- "t" ;;
      "x"
    end.

Section Stack_API.
Context `{!heapG Σ}.

Fixpoint list_val (l: list val) (v: val) : iProp Σ :=
  match l with
  | [] => ⌜ v = NONEV ⌝
  | x :: l' => ∃ (ℓ: loc) t, ⌜ v = SOMEV #ℓ ⌝ ∗ ℓ ↦ (x, t) ∗ list_val l' t
  end.

(*
  type 'a stack = 'a list ref
*)
Definition stack_val (l: list val) (v: val) : iProp Σ :=
  ∃ (ℓ: loc) lv, ⌜ v = #ℓ ⌝ ∗ ℓ ↦ lv ∗ list_val l lv.


Lemma push_spec s x l :
  {{{ stack_val l s }}}
    push s x
  {{{ RET #(); stack_val (x :: l) s }}}.
Proof.
  rewrite /push. iIntros (φ) "Hs Hφ".
  wp_pures. rewrite {1}/stack_val.
  iDestruct "Hs" as (ℓ lv) "(-> & ? & ?)".
  wp_load. wp_pures.
  wp_alloc ℓ'. wp_pures.
  wp_store.
  iApply "Hφ".
  unfold stack_val. iExists ℓ, _. iFrame.
  iSplit; eauto. cbn. iExists _, _. by iFrame.
Qed.

Lemma pop_spec s l :
  {{{ stack_val l s }}}
    pop s
  {{{ v, RET v;
    match l with
    | [] => ⌜ v = #() ⌝ ∗ stack_val [] s
    | x :: l' => ⌜ v = x ⌝ ∗ stack_val l' s
    end }}}.
Proof.
  rewrite /pop. iIntros (φ) "Hs Hφ".
  wp_pures. rewrite {1}/stack_val.
  iDestruct "Hs" as (ℓ lv) "(-> & ? & Hl)".
  wp_load.
  destruct l as [| x l].
  { cbn. iDestruct "Hl" as %->. wp_match.
    iApply "Hφ". iSplit; eauto. unfold stack_val.
    iExists _, _. eauto. }
  { cbn. iDestruct "Hl" as (ℓ' t) "(-> & ? & ?)".
    wp_match. wp_load. wp_pures. wp_load. wp_pures.
    wp_store. iApply "Hφ". iSplit; eauto.
    unfold stack_val. iExists _, _. by iFrame. }
Qed.

End Stack_API.


Definition good_trace (t: list event): Prop :=
  ∀ (i: nat) (v: val),
    t !! i = Some ("pop", v) → v ≠ #() →
    ∃ j, (j < i)%nat ∧ t !! j = Some ("push", v).

Lemma good_trace_push t v :
  good_trace t → good_trace (t ++ [("push", v)]).
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

Lemma good_trace_pop_nil t :
  good_trace t →
  good_trace (t ++ [("pop", #())]).
Proof.
  intros Hgood i v Hti Hv.
  apply lookup_snoc_Some in Hti as [Hti | [_ ?]].
  { specialize (Hgood _ _ Hti Hv) as [j [? ?]]. exists j; split; eauto.
    rewrite lookup_app_l //. apply lookup_lt_is_Some_1; eauto. }
  { congruence. }
Qed.

Lemma good_trace_pop t v i :
  good_trace t →
  t !! i = Some ("push", v) →
  good_trace (t ++ [("pop", v)]).
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

Section Wrapped_Stack_API.
Context `{!heapG Σ}.
Context (N: namespace).

Definition stack_val' (l: list val) (v: val) : iProp Σ :=
  stack_val l v ∗ trace_inv N good_trace ∗
  ∃ t, trace_is t ∗ ⌜good_trace t⌝ ∗
  ⌜ Forall (λ x, ∃ i, t !! i = Some ("push", x)) l ⌝.

Definition push' : val :=
  λ: "s" "x", push "s" "x" ;; Emit "push" "x".

Definition pop' : val :=
  λ: "s", let: "r" := pop "s" in Emit "pop" "r" ;; "r".

Lemma push'_spec s x l :
  {{{ stack_val' l s }}}
    push' s x
  {{{ RET #(); stack_val' (x :: l) s }}}.
Proof.
  iIntros (φ) "Hs Hφ". unfold push'.
  iDestruct "Hs" as "(Hs & #HI & Htr)". iDestruct "Htr" as (t) "(Ht & Hgood & HF)".
  iDestruct "Hgood" as %Hgood. iDestruct "HF" as %HF.
  wp_pures. wp_bind (push _ _).
  iApply (push_spec with "Hs"). iIntros "!> Hs".
  wp_pures.
  eapply good_trace_push in Hgood.
  iApply (wp_emit with "[$Ht $HI]"); eauto.
  iIntros "!> Ht". iApply "Hφ".
  rewrite /stack_val'; iFrame "HI∗".
  iExists _; iFrame. iPureIntro; split; eauto.
  rewrite Forall_cons. split.
  { exists (length t). by apply list_lookup_middle. }
  { eapply Forall_impl; [ apply HF |]. cbn.
    intros v [i Hti]. exists i. by apply lookup_app_l_Some. }
Qed.

Lemma pop'_spec s l :
  {{{ stack_val' l s }}}
    pop' s
  {{{ v, RET v;
      match l with
      | [] => ⌜ v = #() ⌝ ∗ stack_val' [] s
      | x :: l' => ⌜ v = x ⌝ ∗ stack_val' l' s
      end }}}.
Proof.
  iIntros (φ) "Hs Hφ". unfold pop'.
  iDestruct "Hs" as "(Hs & #HI & Htr)". iDestruct "Htr" as (t) "(Ht & Hgood & HF)".
  iDestruct "Hgood" as %Hgood. iDestruct "HF" as %HF.
  wp_pures. wp_bind (pop _).
  iApply (pop_spec with "Hs"). iIntros "!>" (v) "Hs".
  wp_pures. wp_bind (Emit _ _).
  destruct l as [|x l'].
  { iDestruct "Hs" as "(-> & Hs)".
    apply good_trace_pop_nil in Hgood.
    iApply (wp_emit with "[$Ht $HI]"); eauto.
    iIntros "!> Ht". wp_pures. iApply "Hφ". iSplitR; first done.
    rewrite /stack_val'; iFrame "HI∗".
    iExists _. iFrame. iPureIntro; split; eauto. }
  { iDestruct "Hs" as "(-> & Hs)".
    apply Forall_cons in HF as [[i Hti] HF].
    eapply good_trace_pop in Hgood; eauto.
    iApply (wp_emit with "[$Ht $HI]"); eauto.
    iIntros "!> Ht". wp_pures. iApply "Hφ". iSplitR; first done.
    rewrite /stack_val'; iFrame "HI∗".
    iExists _. iFrame. iPureIntro; split; eauto.
    eapply Forall_impl; [ apply HF |]. cbn.
    intros v [j Htj].
    destruct (decide (i = j)) as [<-|].
    { rewrite Htj in Hti. inversion Hti; subst.
      exists i. rewrite lookup_app_l //. apply lookup_lt_is_Some_1; eauto. }
    { exists j. rewrite lookup_app_l //. apply lookup_lt_is_Some_1; eauto. } }
Qed.

End Wrapped_Stack_API.
