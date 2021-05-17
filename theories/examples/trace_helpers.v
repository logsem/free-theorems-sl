From intensional.heap_lang Require Import lang notation.
From intensional.examples Require Import stdpp_extra tactics.
Set Default Proof Using "Type".
Implicit Types t : list val.

Definition check_tag (tag: string) (v: val) :=
  match v with
  | (# (LitTag tag'), _)%V => String.eqb tag tag'
  | _ => false
  end.

Lemma check_tag_in_tags tag v t :
  check_tag tag v = true →
  v ∈ t →
  tag ∈ tags t.
Proof.
  revert tag v. induction t as [|v' t].
  { intros ? ? ?. inversion 1. }
  { intros * H1 [->|H2]%elem_of_cons. cbn.
    { unfold check_tag in H1. repeat case_match; simplify_eq; eauto.
      apply String.eqb_eq in H1. subst. constructor. }
    { cbn. apply elem_of_app. right. eapply IHt; eauto. } }
Qed.

Lemma fresh_tag_nocheck t tag :
  tag ∉ tags t →
  Forall (λ v, ¬ check_tag tag v) t.
Proof.
  induction t as [|v t]. done.
  cbn. repeat case_match; eauto; simplify_eq.
  intros [? ?]%not_elem_of_cons. apply Forall_cons. split; eauto.
  unfold check_tag. intros Heq%Is_true_eq_true.
  by apply String.eqb_eq in Heq as ->.
Qed.

Lemma not_check_tag_iff (tag tag':string) v :
  ¬ check_tag tag (#tag', v)%V ↔ tag ≠ tag'.
Proof.
  unfold check_tag. split; intros HH1 HH2; apply HH1.
  { subst. rewrite String.eqb_refl //. }
  { apply Is_true_eq_true, String.eqb_eq in HH2. auto. }
Qed.

Lemma check_tag_iff (tag tag':string) v :
  check_tag tag (#tag', v)%V = true ↔ tag = tag'.
Proof.
  unfold check_tag. split; intros HH.
  { apply String.eqb_eq in HH. auto. }
  { subst. rewrite String.eqb_refl //. }
Qed.

Lemma filter_check_single_tag_neq (tag tag':string) v :
  tag ≠ tag' →
  filter (λ v, check_tag tag v) [(#tag', v)%V] = [].
Proof.
  intros. apply filter_is_nil. repeat constructor.
  by apply not_check_tag_iff.
Qed.

Lemma filter_check_single_tag_eq (tag:string) v :
  filter (λ v, check_tag tag v) [(#tag, v)%V] = [(#tag, v)%V].
Proof.
  intros. apply filter_Forall_id. repeat constructor.
  by apply Is_true_eq_left, check_tag_iff.
Qed.

Lemma tags_app t u : tags (t ++ u) = tags t ++ tags u.
Proof.
  induction t as [|v t].
  { cbn [tags]. done. }
  { cbn. case_match. all: try rewrite IHt //. subst.
    repeat case_match; auto. }
Qed.

