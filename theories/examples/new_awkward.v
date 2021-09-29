From iris.algebra Require Import auth gmap agree frac.
From iris.base_logic Require Import invariants.
From iris.heap_lang Require Import adequacy notation proofmode.
From iris.bi.lib Require Import fractional.
From iris.staging.algebra Require Import monotone.

Definition awkward : expr :=
  let: "r" := ref #0 in
  λ: "g", "r" <- #0;; "g" #();; "r" <- #1;; "g" #();; !"r".



Definition res_id := positive.

Definition res_map := gmap res_id gname.

Definition res_mapUR := gmapUR res_id (prodR fracR (agreeR gnameO)).

Class res_mapG Σ := {res_map_inG :> inG Σ (authUR res_mapUR); res_map_name : gname}.

Definition res_mapΣ := #[GFunctor (authUR res_mapUR)].

Instance res_map_subΣ_inG Σ : subG res_mapΣ Σ → inG Σ (authUR res_mapUR).
Proof. solve_inG. Qed.

Section named_res.
  Context `{!res_mapG Σ}.

  Definition res_map_full (M : res_map) : iProp Σ :=
    own res_map_name (● ((λ x : gname, (1%Qp, to_agree x)) <$> M : res_mapUR)).

  Definition res_name (id : res_id) (q : Qp) (name : gname) : iProp Σ :=
    own res_map_name (◯ {[id := (q, to_agree name) ]}).

  Typeclasses Opaque res_name res_map_full.

  Global Instance res_name_Timeless id q name : Timeless (res_name id q name).
  Proof. rewrite /res_name; apply _. Qed.

  Global Instance res_map_full_Timeless M : Timeless (res_map_full M).
  Proof. rewrite /res_map_full; apply _. Qed.

  Global Instance res_name_Fractional id name : Fractional (λ q, res_name id q name).
  Proof.
    intros p q.
    rewrite /res_name -own_op -auth_frag_op gmap_op.
    do 2 f_equiv.
    apply map_equiv_iff.
    intros j.
    destruct (decide (j = id)) as [->|].
    - rewrite lookup_merge !lookup_insert /= -Some_op -pair_op /= agree_idemp //.
    - rewrite lookup_merge !lookup_insert_ne //.
  Qed.

  Global Instance res_name_as_fractional id q name :
    AsFractional (res_name id q name) (λ q, res_name id q name) q.
  Proof. by constructor; last apply _. Qed.

  Lemma res_name_agree M id q name : res_map_full M -∗ res_name id q name -∗ ⌜M !! id = Some name⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hvl _]%auth_both_valid_discrete; iPureIntro.
    apply singleton_included_l in Hvl as ([p n] & Hpn1 & Hpn2).
    apply Some_included in Hpn2.
    destruct Hpn2 as [[Hpn21 Hpn22]|Hpn2]; simpl in *.
    - setoid_subst.
      rewrite lookup_fmap in Hpn1.
      revert Hpn1; case: (M !! id); simpl; last by inversion 1.
      intros ? [? ->%to_agree_inj%leibniz_equiv]%Some_equiv_inj; done.
    - apply pair_included in Hpn2 as [_ Hpn2].
      rewrite lookup_fmap in Hpn1.
      revert Hpn1; case: (M !! id); simpl; last by inversion 1.
      intros ? [? ?]%Some_equiv_inj; simpl in *; setoid_subst.
      apply to_agree_included, leibniz_equiv in Hpn2 as ->; done.
  Qed.

  Lemma res_name_update M id name name':
    res_map_full M -∗ res_name id 1%Qp name ==∗
    res_map_full (<[id := name']>M) ∗ res_name id 1%Qp name'.
  Proof.
    rewrite /res_map_full /res_name.
    iIntros "H1 H2".
    iMod (own_update_2
            _ _ _ (● ((λ x : gname, (1%Qp, to_agree x)) <$> <[id := name']>M : res_mapUR) ⋅
                     ◯ {[id := (1%Qp, to_agree name') ]}) with "H1 H2") as "[$ $]"; last done.
    apply auth_update.
    rewrite fmap_insert.
    apply singleton_local_update_any.
    intros ? ?. apply exclusive_local_update; done.
  Qed.

  Lemma res_name_alloc M name :
    res_map_full M ==∗
    ∃ id, ⌜id ∉ dom (gset res_id) M⌝ ∗ res_map_full (<[id := name]>M) ∗ res_name id 1%Qp name.
  Proof.
    rewrite /res_map_full /res_name.
    set (id := fresh (dom (gset res_id) M)).
    iIntros "H".
    iMod (own_update
            _ _ (● ((λ x : gname, (1%Qp, to_agree x)) <$> <[id := name]>M : res_mapUR) ⋅
                   ◯ {[id := (1%Qp, to_agree name) ]}) with "H") as "[? ?]".
    - apply auth_update_alloc.
      rewrite fmap_insert.
      apply alloc_singleton_local_update; last done.
      rewrite -(not_elem_of_dom (D := gset res_id)) dom_fmap.
      apply is_fresh.
    - iModIntro; iExists _; iFrame.
      iPureIntro. apply is_fresh.
  Qed.

End named_res.

Lemma res_name_init `{!inG Σ (authUR res_mapUR)}: ⊢ |==> ∃ γ, own γ (● ∅).
Proof. apply own_alloc, auth_auth_valid; done. Qed.

Definition rel : relation bool :=
  λ b1 b2,
  match b2 with
  | true => True
  | false =>
    match b1 with
    | true => False
    | false => True
    end
  end.

Instance rel_PreOrder : PreOrder rel.
Proof. split; repeat intros []; done. Qed.

Section rel.
  Context `{!inG Σ (authUR (mraUR rel))}.

  Definition exactly (γ : gname) (b : bool) := own γ (● principal rel b).

  Definition atleast (γ : gname) (b : bool) := own γ (◯ principal rel b).

  Lemma exactly_update γ b1 b2 : rel b1 b2 → exactly γ b1 ==∗ exactly γ b2 ∗ atleast γ b2.
  Proof.
    intros.
    rewrite -own_op; apply own_update.
    apply auth_update_alloc.
    apply mra_local_update_grow; done.
  Qed.

  Lemma exactly_alloc b : ⊢ |==> ∃ γ, exactly γ b.
  Proof. apply own_alloc; apply auth_auth_valid; done. Qed.

  Lemma exatly_atleast_rel γ b1 b2 : exactly γ b1 -∗ atleast γ b2 -∗ ⌜rel b2 b1⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hincl _]%auth_both_valid_discrete.
    revert Hincl; rewrite principal_included; done.
  Qed.

End rel.

Definition relΣ := #[GFunctor (authUR (mraUR rel))].

Instance sub_relΣ_inG Σ : subG relΣ Σ → inG Σ (authUR (mraUR rel)).
Proof. solve_inG. Qed.

Section awkward_proof.
  Context `{!heapGS Σ, !res_mapG Σ, !inG Σ (authUR (mraUR rel))}.

  Lemma awkward_proof M :
    {{{ res_map_full M }}}
      awkward
    {{{ (f : val) N, RET f;
        ⌜M ⊆ N⌝ ∗ res_map_full N ∗
         □ (∀ (g : val), (∀ M', {{{ res_map_full M' }}}
                      g #()
                    {{{ N', RET #(); ⌜M' ⊆ N'⌝ ∗ res_map_full N' }}}) -∗
                (∀ M', {{{ res_map_full M' }}}
                         f g
                       {{{ N', RET #1; ⌜M' ⊆ N'⌝ ∗ res_map_full N' }}})
           )
    }}}.
  Proof.
    iIntros (Φ) "HM HΦ".
    rewrite /awkward.
    wp_alloc l as "Hl".
    iMod (exactly_alloc false) as (γ) "Hex".
    iMod (res_name_alloc _ γ with "HM") as (id HidM) "[HM Hid]".
    rewrite insert_union_singleton_r; last first.
    { rewrite -(not_elem_of_dom (D := gset res_id)); done. }
    iMod (inv_alloc
            (nroot .@ "awk") _
            (∃ γ b, res_name id 1 γ ∗ exactly γ b ∗ if b then l ↦ #1 else l ↦ #0)%I
            with "[Hex Hid Hl]") as "#Hinv".
    { iNext; iExists γ, false; iFrame. }
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame "HM".
    iSplit.
    { iPureIntro. apply map_union_subseteq_l. }
    iModIntro.
    iIntros (g) "#Hg".
    iIntros (M' Ψ) "!# HM' HΨ".
    wp_pures.
    wp_bind (_ <- _)%E.
    iInv (nroot .@ "awk") as (γ1 b) "(>Hid & >Hex1 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b; iExists _; iFrame. }
    iDestruct (res_name_agree with "HM' Hid") as %Hids1.
    iMod (exactly_alloc false) as (γ2) "Hex2".
    iMod (res_name_update _ _ _ γ2 with "HM' Hid") as "[HM' Hid]".
    wp_store.
    iMod ("Hcl" with "[Hex2 Hid Hl]") as "_".
    { iNext; iExists γ2, false; iFrame. }
    iModIntro.
    wp_pures.
    wp_apply ("Hg" with "HM'").
    iIntros (N1) "[%HN1 HMN]".
    wp_pures.
    iMod (exactly_update _ _ true with "Hex1") as "[Hex1 Hat1]"; first done.
    wp_bind (_ <- _)%E.
    iInv (nroot .@ "awk") as (γ3 b2) "(>Hid & >Hex2 & Hl)" "Hcl".
    iAssert (∃ v, ▷ l ↦ v)%I with "[Hl]" as (?) ">Hl".
    { destruct b2; iExists _; iFrame. }
    iMod (res_name_update _ _ _ γ1 with "HMN Hid") as "[HMN Hid]".
    wp_store.
    iMod ("Hcl" with "[Hex1 Hid Hl]") as "_".
    { iNext; iExists γ1, true; iFrame. }
    iModIntro.
    wp_pures.
    wp_apply ("Hg" with "HMN").
    iIntros (N2) "[%HN2 HMN]".
    wp_pures.
    iInv (nroot .@ "awk") as (γ4 b3) "(>Hid & >Hex1 & Hl)" "Hcl".
    iDestruct (res_name_agree with "HMN Hid") as %Hids2.
    assert (N2 !! id = Some γ1) as Heq.
    { eapply lookup_weaken; last by apply HN2.
      rewrite lookup_insert; done. }
    simplify_eq.
    iDestruct (exatly_atleast_rel with "Hex1 Hat1") as %?.
    destruct b3; last done.
    wp_load.
    iMod ("Hcl" with "[Hex1 Hid Hl]") as "_".
    { iNext; iExists _, true; iFrame. }
    iModIntro.
    iApply "HΨ"; iFrame.
    iPureIntro.
    etrans; last apply HN2.
    etrans; last apply insert_mono, HN1.
    rewrite insert_insert insert_id; auto.
  Qed.

End awkward_proof.

Definition awkward_self_app : expr :=
  let: "f" := awkward in
  "f" (λ: <>, "f" (λ: <>, #());; #()).

Lemma awkward_self_app_returns_one :
  adequate
    NotStuck
    awkward_self_app
    {| heap := ∅; used_proph_id := ∅ |}
    (λ v _, v = #1).
Proof.
  set (Σ := #[heapΣ; res_mapΣ; relΣ]).
  eapply (heap_adequacy Σ).
  iIntros (?) "Hinv".
  rewrite /awkward_self_app.
  iMod res_name_init as (resN) "HM".
  set (rnGS := {| res_map_name := resN |} : res_mapG Σ).
  wp_apply (awkward_proof ∅ with "[HM]").
  { rewrite /res_map_full fmap_empty; iFrame. }
  iIntros (f N) "(%HN & HN & #Hf)".
  wp_pures.
  wp_apply ("Hf" with "[] HN"); last by auto.
  iIntros (M' Φ) "!# HM' HΦ".
  wp_pures.
  wp_apply ("Hf" with "[] HM'").
  - iIntros (M'' Ψ) "!# HM'' HΨ".
    wp_pures.
    iModIntro.
    iApply "HΨ"; eauto.
  - iIntros (?) "?".
    wp_pures.
    iModIntro.
    iApply "HΦ"; done.
Qed.
