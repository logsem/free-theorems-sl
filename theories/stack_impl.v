From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import invariants.
From intensional.heap_lang Require Import lifting proofmode notation.
From intensional.heap_lang Require Import adequacy.
Set Default Proof Using "Type".

From intensional Require Import stack.

Module Stack_impl.
Section S.
Context {Σ: gFunctors}.
Context `{heapG Σ}.

Definition create : val :=
  λ: "u", ref (InjL #()).

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

Lemma create_correct :
  {{{ True }}} create #() {{{ s, RET s; stack_val [] s }}}.
Proof.
  rewrite /create. iIntros (φ) "_ Hφ".
  wp_pures. wp_alloc ℓ. iApply "Hφ".
  rewrite /stack_val. iExists _, _. iFrame. eauto.
Qed.

Lemma push_correct s x l :
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

Lemma pop_correct s l :
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

Lemma correct : ⊢ stacklib_spec True (create, push, pop).
Proof.
  iIntros "". unfold stacklib_spec.
  iExists stack_val. repeat iSplit.
  iIntros (?); iApply create_correct.
  iIntros (? ? ? ?); iApply push_correct.
  iIntros (? ? ?); iApply pop_correct.
Qed.

End S.
End Stack_impl.
