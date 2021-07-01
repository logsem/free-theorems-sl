From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From iris.base_logic.lib Require Import invariants.
From intensional.heap_lang Require Import lifting proofmode notation.
From intensional.heap_lang Require Import adequacy.
Set Default Proof Using "Type".

From intensional Require stack traversable_stack.

(** *** Bonus: an example implementation of a stack library satisfying the specifications in [stack] and [traversable_stack]. *)

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

Definition foreach : val :=
  λ: "s" "f",
    let: "loop" := rec: "loop" "l" :=
      match: "l" with
        NONE => #()
      | SOME "c" =>
        let: "x" := Fst !"c" in
        let: "t" := Snd !"c" in
        "f" "x" ;;
        "loop" "t"
      end
    in
    "loop" (!"s").

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
  {{{ stack_val l s ∗ ⌜x ≠ #()⌝ }}}
    push s x
  {{{ RET #(); stack_val (x :: l) s }}}.
Proof.
  rewrite /push. iIntros (φ) "(Hs & ?) Hφ".
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

Lemma foreach_correct s l (f: val) (I: list val → iProp Σ) :
  {{{ (∀ p x,
        ⌜(p ++ [x]) `prefix_of` l⌝ →
        {{{ I p }}} f x {{{ RET #(); I (p ++ [x]) }}}) ∗
      stack_val l s ∗ I [] }}}
    foreach s f
  {{{ RET #(); stack_val l s ∗ I l }}}.
Proof.
  set p := {3} []. assert (Hp: p `prefix_of` l) by apply prefix_nil.
  iIntros (φ) "(#Hf & Hs & HI) Hφ". rewrite /foreach. wp_pures.
  iDestruct "Hs" as (ℓ lv) "(-> & Hℓ & Hlv)".
  wp_bind (! #ℓ)%E. wp_load.
  set k := {2} l. assert (Hk: p ++ k = l) by eauto.
  set lk := {2 3} lv.
  iAssert (list_val k lk -∗ list_val l lv)%I with "[]" as "-#Hclose".
  { subst k lk. eauto. }
  clearbody k p lk. iRename "Hlv" into "Hlk".
  iLöb as "IH" forall (p k lk Hp Hk) "HI Hlk Hclose".
  wp_rec.
  destruct k as [| x k].
  { cbn. iDestruct "Hlk" as "->". wp_match. iApply "Hφ".
    rewrite app_nil_r in Hk. subst p.
    iFrame. rewrite {2}/stack_val. iExists _, _. iFrame.
    iSplit; eauto. iApply "Hclose"; eauto. }
  { cbn. iDestruct "Hlk" as (ℓ' t) "(-> & Hℓ' & Ht)". wp_match.
    wp_bind (! #ℓ')%E. wp_load. wp_pures.
    wp_bind (! #ℓ')%E. wp_load. wp_pures.
    wp_bind (f x).
    assert ((p ++ [x]) `prefix_of` l) as Hp'.
    { eexists. rewrite -Hk -app_assoc //. }
    iApply ("Hf" $! _ _ Hp' with "HI").
    iIntros "!> HI". wp_seq.
    iApply ("IH" with "[] [Hf] Hℓ Hφ HI Ht").
    { iPureIntro. unfold prefix. exists k. subst l. rewrite -app_assoc //. }
    { iPureIntro. rewrite -app_assoc //=. }
    { iIntros "Hk". iApply "Hclose". iExists _, _. iFrame. eauto. } }
Qed.


Lemma correct : ⊢ stack.stacklib_spec True (create, push, pop).
Proof.
  iIntros "". unfold stack.stacklib_spec.
  iExists stack_val. repeat iSplit.
  iIntros (?); iApply create_correct.
  iIntros (? ? ? ?); iApply push_correct.
  iIntros (? ? ?); iApply pop_correct.
Qed.

Lemma traversable_correct : ⊢ traversable_stack.stacklib_spec True (create, push, pop, foreach).
Proof.
  iIntros "". unfold traversable_stack.stacklib_spec.
  iExists stack_val. repeat iSplit.
  iIntros (?); iApply create_correct.
  iIntros (? ? ? ?); iApply push_correct.
  iIntros (? ? ?); iApply pop_correct.
  iIntros (? ? ? ? ?); iApply foreach_correct.
Qed.

End S.
End Stack_impl.
