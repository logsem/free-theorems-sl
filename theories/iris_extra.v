From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl excl_auth gmap.
From iris.base_logic.lib Require Import own.

Lemma excl_auth_eq A `{inG Σ (excl_authR (leibnizO A))} γ (x y: A):
  own γ (◯E (x:leibnizO A)) -∗ own γ (●E (y:leibnizO A)) -∗ ⌜x = y⌝.
Proof.
  iIntros "H1 H2". iDestruct (own_op with "[$H1 $H2]") as "H".
  iDestruct (own_valid with "H") as %HH%excl_auth_agree. done.
Qed.

Lemma excl_auth_upd A `{inG Σ (excl_authR (leibnizO A))} γ (x y z: A):
  own γ (◯E (x:leibnizO A)) -∗ own γ (●E (y:leibnizO A)) ==∗
  own γ (◯E (z:leibnizO A)) ∗ own γ (●E (z:leibnizO A)).
Proof.
  iIntros "H1 H2".
  iDestruct (own_update_2 with "H1 H2") as ">[? ?]".
  apply excl_auth_update. iModIntro. iFrame.
Qed.

Lemma excl_auth_alloc A `{inG Σ (excl_authR (leibnizO A))} (x: A):
  ⊢ |==> ∃ γ, own γ (◯E (x:leibnizO A)) ∗ own γ (●E (x:leibnizO A)).
Proof.
  iIntros.
  iMod (own_alloc (●E (x:leibnizO A) ⋅ ◯E (x:leibnizO A))) as (γ) "[? ?]".
  apply excl_auth_valid. iModIntro. iExists _. iFrame.
Qed.
