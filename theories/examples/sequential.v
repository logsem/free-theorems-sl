From iris.algebra Require Import auth gmap agree frac agree.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.staging.algebra Require Import monotone.
From intensional.heap_lang Require Import adequacy notation proofmode.

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


Section Trace.

  Inductive sequential_with_opened : list val → list val → Prop :=
    | sequential_with_opened_nil :
        sequential_with_opened [] []
    | sequential_with_opened_open tag o t :
        sequential_with_opened o t →
        sequential_with_opened (tag :: o) (t ++ (tag, #"(")%V :: nil)
    | sequential_with_opened_close tag o t :
        sequential_with_opened (tag :: o) t →
        sequential_with_opened o (t ++ (tag, #")")%V :: nil).

  Definition sequential_trace (t: list val) :=
    ∃ o, sequential_with_opened o t.

(*
  Inductive sequential_full_trace : list val → Prop :=
    | sequential_full_trace_nil : sequential_full_trace []
    | sequential_full_trace_wrap tag t :
        sequential_full_trace t →
        sequential_full_trace ((tag, #"(")%V :: t ++ (tag, #")")%V :: nil)
    | sequential_full_trace_app t t' :
        sequential_full_trace t →
        sequential_full_trace t' →
        sequential_full_trace (t ++ t').

  Definition sequential_trace (t: list val) :=
    ∃ t', sequential_full_trace t' ∧ t `prefix_of` t'.

  Lemma sequential_call tag :
    sequential_full_trace [(tag, #"(")%V ; (tag, #")")%V].
  Proof. apply (sequential_full_trace_wrap tag _ sequential_full_trace_nil). Qed.

  Lemma sequential_full_trace_call_middle tag t t' :
    sequential_full_trace (t ++ t') →
    sequential_full_trace (t ++ (tag, #"(")%V :: (tag, #")")%V :: t').
  Proof.
    set tt := t ++ t'. intros Htt. assert (tt = t ++ t') as HH by done. revert HH; clearbody tt.
    revert t t'. induction Htt as [| tag' |].
    { intros ? ? [-> ->]%eq_sym%app_eq_nil. cbn. apply sequential_call. }
    { intros t1 t2 HH. rewrite app_comm_cons in HH.
      apply app_eq_inv in HH as [HH|HH].
      { destruct HH as [? [Ht1 Ht2]]. subst.
        destruct t1.
        { cbn in *. subst. cbn.
          pose proof (sequential_full_trace_app _ _ (sequential_call tag)
                       (sequential_full_trace_wrap tag' t Htt)). done. }
        { cbn in *. inversion Ht1; subst. specialize (IHHtt _ _ eq_refl).
          pose proof (sequential_full_trace_wrap tag' _ IHHtt). rewrite -app_assoc // in H. } }
      { destruct HH as [? [Ht1 Ht2]]. subst. apply eq_sym, app_eq_unit in Ht2.
        destruct_or!; destruct_and!; subst; cbn.
        { rewrite app_nil_r /=.
          pose proof (sequential_full_trace_app _ _ Htt (sequential_call tag)) as HH.
          pose proof (sequential_full_trace_wrap tag' _ HH). rewrite -app_assoc // in H. }
        { apply (sequential_full_trace_app _ _
                   (sequential_full_trace_wrap tag' _ Htt) (sequential_call tag)). } } }
    { intros t1 t2 Ht1t2. apply app_eq_inv in Ht1t2 as [HH|HH].
      { destruct HH as [? [-> ->]]. specialize (IHHtt1 _ _ eq_refl).
        pose proof (sequential_full_trace_app _ _ IHHtt1 Htt2) as HH. rewrite -app_assoc // in HH. }
      { destruct HH as [? [-> ->]]. specialize (IHHtt2 _ _ eq_refl).
        pose proof (sequential_full_trace_app _ _ Htt1 IHHtt2) as HH. rewrite -app_assoc //. } }
  Qed.

  Lemma sequential_with_opened_sequential o t :
    sequential_with_opened o t →
    sequential_trace t.
  Proof.
    set closing : list val → list val := map (λ tag, (tag, #")")%V).
    enough (Hind: sequential_with_opened o t → sequential_full_trace (t ++ closing o)).
    { intros Ho. specialize (Hind Ho). eexists. split; eauto.
      by apply prefix_app_r. }

    induction 1 as [| ? ? ? Ho Ht|].
    { rewrite /=. constructor. }
    { rewrite /=. eapply (sequential_full_trace_call_middle tag) in Ht. rewrite -app_assoc//. }
    { cbn in *. rewrite -app_assoc //. }
  Qed.

  Lemma prefix_snoc_inv {A} (l1 l2: list A) x :
    l1 `prefix_of` (l2 ++ [x]) →
    l1 = l2 ++ [x] ∨ l1 `prefix_of` l2.
  Proof.
    revert l1 x. induction l2 as [| y l2].
    { cbn. intros ? ? HH. destruct l1. right; done.
      pose proof (prefix_cons_inv_1 _ _ _ _ HH) as ->.
      apply (prefix_cons_inv_2), prefix_nil_inv in HH. subst. by left. }
    { cbn. intros ? ? HH. destruct l1. right; by apply prefix_nil.
      pose proof (prefix_cons_inv_1 _ _ _ _ HH) as ->.
      apply (prefix_cons_inv_2), IHl2 in HH as [->|HH]. by left.
      right. by apply prefix_cons. }
  Qed.

  Lemma sequential_with_opened_of_sequential t :
    sequential_trace t →
    ∃ o, sequential_with_opened o t.
  Proof.
    intros [t' [Ht' Htt']].
    revert t Htt'. induction Ht'.
    { intros ? ->%prefix_nil_inv. eexists. econstructor. }
    { intros t'. rename Ht' into Ht. intros Ht'.
      destruct t' as [| ? t']. by eexists; econstructor.
      pose proof (prefix_cons_inv_1 _ _ _ _ Ht') as ->.
      apply prefix_cons_inv_2, prefix_snoc_inv in Ht' as [->|Ht'].
  Abort.
*)
End Trace.


Section S.
Context `{!heapGS Σ, !res_mapG Σ}.

Definition seq_triple (P: iProp Σ) e (Q: val → iProp Σ): iProp Σ :=
  ∀ M,
    {{{ res_map_full M ∗ P }}}
      e
    {{{ v N, RET v; ⌜M ⊆ N⌝ ∗ res_map_full N ∗ Q v }}}.

Definition awk_spec P0 (awk: expr) :=
  seq_triple P0 awk (λ (f: val),
    □ (∀ (g: val), seq_triple True (g #()) (λ _, True) -∗
                   seq_triple True (f g) (λ v, ⌜v = #1⌝ )))%I.
End S.

Module Wrap.
Section S.
Context `{!heapGS Σ, !res_mapG Σ, !inG Σ (agreeR (leibnizO (list val)))}.

Context (awk_impl: expr).

Definition awk : expr :=
  let: "f" := awk_impl in
  λ: "g",
  (* fresh *)
    "f" (λ: <>,
      let: "t" := Fresh (#"(") in
      "g" #() ;;
      Emit ("t", #")")
    (* emit *)
).

Lemma correct (P: iProp Σ) (Q: val → iProp Σ) t :
  awk_spec True awk_impl -∗
  awk_spec (trace_is t ∗ trace_inv (nroot .@ "trace") sequential_trace) awk.
Proof.
  iIntros "#Hspec". rewrite /awk /awk_spec /seq_triple.
  iIntros (M φ) "!> (HM & Ht & #HI) Hφ".

  iMod (trace_is_inv with "Ht HI") as "[Ht %Ht]".
  destruct Ht as [o Ht].

  iMod (own_alloc (to_agree (o:leibnizO _))) as (γ) "Hγ". done.
  iMod (res_name_alloc _ γ with "HM") as (id HidM) "[HM Hid]".

  iMod (inv_alloc
          (nroot .@ "wrap") _
          (∃ γ (o: list val) t, res_name id 1 γ ∗ own γ (to_agree (o:leibnizO _)) ∗
                    trace_is t ∗ ⌜sequential_with_opened o t⌝)%I
        with "[Hid Hγ Ht]") as "#Hinv".
  { iNext. iExists γ, o, t. by iFrame. }

  wp_bind awk_impl. iApply ("Hspec" with "[$HM]").
  iIntros "!>" (f M') "(%HMM' & HM' & #Hf)".
  wp_pures. iApply "Hφ". iFrame "HM'". iSplitR.
  { iPureIntro. rewrite map_subseteq_spec in HMM' |- * => HMM'.
    apply map_subseteq_spec. intros ? ? ?. eapply HMM'.
    rewrite lookup_insert_ne //. intros ->. apply not_elem_of_dom in HidM.
    congruence. }

  iIntros "!>" (g) "#HG".
  iIntros (M'' φ') "!> [HM'' _] Hφ'". wp_pures.
  iApply ("Hf" with "[] [$HM''] Hφ'").

  iIntros (N ?) "!> [HN _] Hφ".

  wp_pures. wp_bind (Fresh _).
  iInv (nroot .@ "wrap") as (γ1 o1 t1) "(>Hid & >Hγ1 & >Ht1 & >%Ht1)" "Hclose".
  iDestruct (res_name_agree with "HN Hid") as %HNid.
  iApply (wp_fresh with "[$Ht1 $HI]"). solve_ndisj.
  { intros tag Htag. exists (#tag :: o1). by constructor. }
  iIntros "!>" (tag) "[Ht1 %Htag]".
  iMod (own_alloc (to_agree ((#tag :: o1):leibnizO _))) as (γ2) "#Hγ2". done.
  iMod (res_name_update _ _ _ γ2 with "HN Hid") as "[HN' Hid]".
  iMod ("Hclose" with "[Ht1 Hγ2 Hid]") as "_".
  { iNext. iExists γ2, (#tag :: o1), _. iFrame "Hγ2 ∗". iPureIntro. by constructor. }
  iModIntro.

  wp_pures. wp_bind (g _). iApply ("HG" with "[$HN']").
  iIntros "!>" (? N') "[% [HN' _]]".
  assert (N' !! id = Some γ2) as HN'id.
  { eapply lookup_weaken; last by eauto. by rewrite lookup_insert. }

  wp_pures.
  iInv (nroot .@ "wrap") as (γ3 o3 t3) "(>Hid & >Hγ3 & >Ht3 & >%Ht3)" "Hclose".
  iDestruct (res_name_agree with "HN' Hid") as %HN'id'. simplify_eq.
  iDestruct "Hγ2" as "-#Hγ2".
  iDestruct (own_op with "[$Hγ2 $Hγ3]") as "Hγ2".
  iDestruct (own_valid with "Hγ2") as %Ho3%to_agree_op_inv%leibniz_equiv. subst o3.
  iClear "Hγ2".

  iApply (wp_emit with "[$Ht3 $HI]"). solve_ndisj.
  { eexists. by econstructor. }
  iIntros "!> Ht".
  iMod (res_name_update _ _ _ γ1 with "HN' Hid") as "[HN' Hid]".
  iMod ("Hclose" with "[Ht Hγ1 Hid]") as "_".
  { iNext. iExists _, _, _. iFrame. iPureIntro. by constructor. }
  iModIntro.

  iApply "Hφ". iFrame. iPureIntro.
  etrans. 2: apply insert_mono; eassumption.
  rewrite insert_insert insert_id//.
Qed.

End S.

End Wrap.
