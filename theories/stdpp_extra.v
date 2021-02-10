From Coq Require Import ssreflect.
From stdpp Require Import list.

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
