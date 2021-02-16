From stdpp Require Import fin_maps.
From iris.bi Require Import lib.fractional.
From iris.proofmode Require Import tactics.
From intensional.heap_lang Require Export lifting.
From intensional.heap_lang Require Import tactics notation.
Set Default Proof Using "Type".

(** This file defines the [array] connective, a version of [mapsto] that works
with lists of values. It also contains array versions of the basic heap
operations of HeapLang. *)

Definition array `{!heapG Σ} (l : loc) (q : Qp) (vs : list val) : iProp Σ :=
  ([∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦{q} v)%I.
Notation "l ↦∗{ q } vs" := (array l q vs)
  (at level 20, q at level 50, format "l  ↦∗{ q }  vs") : bi_scope.
Notation "l ↦∗ vs" := (array l 1 vs)
  (at level 20, format "l  ↦∗  vs") : bi_scope.

(** We have [FromSep] and [IntoSep] instances to split the fraction (via the
[AsFractional] instance below), but not for splitting the list, as that would
lead to overlapping instances. *)

Section lifting.
Context `{!heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types q : Qp.
Implicit Types l : loc.
Implicit Types sz off : nat.

Global Instance array_timeless l q vs : Timeless (array l q vs) := _.

Global Instance array_fractional l vs : Fractional (λ q, l ↦∗{q} vs)%I := _.
Global Instance array_as_fractional l q vs :
  AsFractional (l ↦∗{q} vs) (λ q, l ↦∗{q} vs)%I q.
Proof. split; done || apply _. Qed.

Lemma array_nil l q : l ↦∗{q} [] ⊣⊢ emp.
Proof. by rewrite /array. Qed.

Lemma array_singleton l q v : l ↦∗{q} [v] ⊣⊢ l ↦{q} v.
Proof. by rewrite /array /= right_id loc_add_0. Qed.

Lemma array_app l q vs ws :
  l ↦∗{q} (vs ++ ws) ⊣⊢ l ↦∗{q} vs ∗ (l +ₗ length vs) ↦∗{q} ws.
Proof.
  rewrite /array big_sepL_app.
  setoid_rewrite Nat2Z.inj_add.
  by setoid_rewrite loc_add_assoc.
Qed.

Lemma array_cons l q v vs : l ↦∗{q} (v :: vs) ⊣⊢ l ↦{q} v ∗ (l +ₗ 1) ↦∗{q} vs.
Proof.
  rewrite /array big_sepL_cons loc_add_0.
  setoid_rewrite loc_add_assoc.
  setoid_rewrite Nat2Z.inj_succ.
  by setoid_rewrite Z.add_1_l.
Qed.

Global Instance array_cons_frame l q v vs R Q :
  Frame false R (l ↦{q} v ∗ (l +ₗ 1) ↦∗{q} vs) Q →
  Frame false R (l ↦∗{q} (v :: vs)) Q.
Proof. by rewrite /Frame array_cons. Qed.

Lemma update_array l q vs off v :
  vs !! off = Some v →
  ⊢ l ↦∗{q} vs -∗ ((l +ₗ off) ↦{q} v ∗ ∀ v', (l +ₗ off) ↦{q} v' -∗ l ↦∗{q} <[off:=v']>vs).
Proof.
  iIntros (Hlookup) "Hl".
  rewrite -[X in (l ↦∗{_} X)%I](take_drop_middle _ off v); last done.
  iDestruct (array_app with "Hl") as "[Hl1 Hl]".
  iDestruct (array_cons with "Hl") as "[Hl2 Hl3]".
  assert (off < length vs)%nat as H by (apply lookup_lt_is_Some; by eexists).
  rewrite take_length min_l; last by lia. iFrame "Hl2".
  iIntros (w) "Hl2".
  clear Hlookup. assert (<[off:=w]> vs !! off = Some w) as Hlookup.
  { apply list_lookup_insert. lia. }
  rewrite -[in (l ↦∗{_} <[off:=w]> vs)%I](take_drop_middle (<[off:=w]> vs) off w Hlookup).
  iApply array_app. rewrite take_insert; last by lia. iFrame.
  iApply array_cons. rewrite take_length min_l; last by lia. iFrame.
  rewrite drop_insert_gt; last by lia. done.
Qed.

(** * Rules for allocation *)
Lemma mapsto_seq_array l q v n :
  ([∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦{q} v) -∗
  l ↦∗{q} replicate n v.
Proof.
  rewrite /array. iInduction n as [|n'] "IH" forall (l); simpl.
  { done. }
  iIntros "[$ Hl]". rewrite -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc. iApply "IH". done.
Qed.

Lemma twp_allocN s E v n :
  0 < n →
  [[{ True }]] AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  [[{ l, RET LitV (LitLoc l); l ↦∗ replicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }]].
Proof.
  iIntros (Hzs Φ) "_ HΦ". iApply twp_allocN_seq; [done..|].
  iIntros (l) "Hlm". iApply "HΦ".
  iDestruct (big_sepL_sep with "Hlm") as "[Hl $]".
  by iApply mapsto_seq_array.
Qed.
Lemma wp_allocN s E v n :
  0 < n →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); l ↦∗ replicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (? Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_allocN; [auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_allocN_vec s E v n :
  0 < n →
  [[{ True }]]
    AllocN #n v @ s ; E
  [[{ l, RET #l; l ↦∗ vreplicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }]].
Proof.
  iIntros (Hzs Φ) "_ HΦ". iApply twp_allocN; [ lia | done | .. ].
  iIntros (l) "[Hl Hm]". iApply "HΦ". rewrite vec_to_list_replicate. iFrame.
Qed.
Lemma wp_allocN_vec s E v n :
  0 < n →
  {{{ True }}}
    AllocN #n v @ s ; E
  {{{ l, RET #l; l ↦∗ vreplicate (Z.to_nat n) v ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (? Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_allocN_vec; [auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

(** * Rules for accessing array elements *)
Lemma twp_load_offset s E l q off vs v :
  vs !! off = Some v →
  [[{ l ↦∗{q} vs }]] ! #(l +ₗ off) @ s; E [[{ RET v; l ↦∗{q} vs }]].
Proof.
  iIntros (Hlookup Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_load with "Hl1"). iIntros "Hl1". iApply "HΦ".
  iDestruct ("Hl2" $! v) as "Hl2". rewrite list_insert_id; last done.
  iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_load_offset s E l q off vs v :
  vs !! off = Some v →
  {{{ ▷ l ↦∗{q} vs }}} ! #(l +ₗ off) @ s; E {{{ RET v; l ↦∗{q} vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_load_offset with "H"); [eauto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_load_offset_vec s E l q sz (off : fin sz) (vs : vec val sz) :
  [[{ l ↦∗{q} vs }]] ! #(l +ₗ off) @ s; E [[{ RET vs !!! off; l ↦∗{q} vs }]].
Proof. apply twp_load_offset. by apply vlookup_lookup. Qed.
Lemma wp_load_offset_vec s E l q sz (off : fin sz) (vs : vec val sz) :
  {{{ ▷ l ↦∗{q} vs }}} ! #(l +ₗ off) @ s; E {{{ RET vs !!! off; l ↦∗{q} vs }}}.
Proof. apply wp_load_offset. by apply vlookup_lookup. Qed.

Lemma twp_store_offset s E l off vs v :
  is_Some (vs !! off) →
  [[{ l ↦∗ vs }]] #(l +ₗ off) <- v @ s; E [[{ RET #(); l ↦∗ <[off:=v]> vs }]].
Proof.
  iIntros ([w Hlookup] Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_store with "Hl1"). iIntros "Hl1".
  iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_store_offset s E l off vs v :
  is_Some (vs !! off) →
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ <[off:=v]> vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_store_offset with "H"); [eauto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_store_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
  [[{ l ↦∗ vs }]] #(l +ₗ off) <- v @ s; E [[{ RET #(); l ↦∗ vinsert off v vs }]].
Proof.
  setoid_rewrite vec_to_list_insert. apply twp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.
Lemma wp_store_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ vinsert off v vs }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_store_offset_vec with "H"); [eauto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_suc_offset s E l off vs v' v1 v2 :
  vs !! off = Some v' →
  v' = v1 →
  vals_compare_safe v' v1 →
  [[{ l ↦∗ vs }]]
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  [[{ RET (v', #true); l ↦∗ <[off:=v2]> vs }]].
Proof.
  iIntros (Hlookup ?? Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_cmpxchg_suc with "Hl1"); [done..|].
  iIntros "Hl1". iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_cmpxchg_suc_offset s E l off vs v' v1 v2 :
  vs !! off = Some v' →
  v' = v1 →
  vals_compare_safe v' v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (v', #true); l ↦∗ <[off:=v2]> vs }}}.
Proof.
  iIntros (??? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_suc_offset with "H"); [eauto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_suc_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off = v1 →
  vals_compare_safe (vs !!! off) v1 →
  [[{ l ↦∗ vs }]]
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  [[{ RET (vs !!! off, #true); l ↦∗ vinsert off v2 vs }]].
Proof.
  intros. setoid_rewrite vec_to_list_insert. eapply twp_cmpxchg_suc_offset=> //.
  by apply vlookup_lookup.
Qed.
Lemma wp_cmpxchg_suc_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off = v1 →
  vals_compare_safe (vs !!! off) v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (vs !!! off, #true); l ↦∗ vinsert off v2 vs }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_suc_offset_vec with "H"); [eauto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_fail_offset s E l q off vs v0 v1 v2 :
  vs !! off = Some v0 →
  v0 ≠ v1 →
  vals_compare_safe v0 v1 →
  [[{ l ↦∗{q} vs }]]
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  [[{ RET (v0, #false); l ↦∗{q} vs }]].
Proof.
  iIntros (Hlookup HNEq Hcmp Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_cmpxchg_fail with "Hl1"); first done.
  { destruct Hcmp; by [ left | right ]. }
  iIntros "Hl1". iApply "HΦ". iDestruct ("Hl2" $! v0) as "Hl2".
  rewrite list_insert_id; last done. iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_cmpxchg_fail_offset s E l q off vs v0 v1 v2 :
  vs !! off = Some v0 →
  v0 ≠ v1 →
  vals_compare_safe v0 v1 →
  {{{ ▷ l ↦∗{q} vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (v0, #false); l ↦∗{q} vs }}}.
Proof.
  iIntros (??? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_fail_offset with "H"); [eauto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_fail_offset_vec s E l q sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off ≠ v1 →
  vals_compare_safe (vs !!! off) v1 →
  [[{ l ↦∗{q} vs }]]
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  [[{ RET (vs !!! off, #false); l ↦∗{q} vs }]].
Proof. intros. eapply twp_cmpxchg_fail_offset=> //. by apply vlookup_lookup. Qed.
Lemma wp_cmpxchg_fail_offset_vec s E l q sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off ≠ v1 →
  vals_compare_safe (vs !!! off) v1 →
  {{{ ▷ l ↦∗{q} vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (vs !!! off, #false); l ↦∗{q} vs }}}.
Proof. intros. eapply wp_cmpxchg_fail_offset=> //. by apply vlookup_lookup. Qed.

Lemma twp_faa_offset s E l off vs (i1 i2 : Z) :
  vs !! off = Some #i1 →
  [[{ l ↦∗ vs }]] FAA #(l +ₗ off) #i2 @ s; E
  [[{ RET LitV (LitInt i1); l ↦∗ <[off:=#(i1 + i2)]> vs }]].
Proof.
  iIntros (Hlookup Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_faa with "Hl1").
  iIntros "Hl1". iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_faa_offset s E l off vs (i1 i2 : Z) :
  vs !! off = Some #i1 →
  {{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #i2 @ s; E
  {{{ RET LitV (LitInt i1); l ↦∗ <[off:=#(i1 + i2)]> vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_faa_offset with "H"); [eauto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_faa_offset_vec s E l sz (off : fin sz) (vs : vec val sz) (i1 i2 : Z) :
  vs !!! off = #i1 →
  [[{ l ↦∗ vs }]] FAA #(l +ₗ off) #i2 @ s; E
  [[{ RET LitV (LitInt i1); l ↦∗ vinsert off #(i1 + i2) vs }]].
Proof.
  intros. setoid_rewrite vec_to_list_insert. apply twp_faa_offset=> //.
  by apply vlookup_lookup.
Qed.
Lemma wp_faa_offset_vec s E l sz (off : fin sz) (vs : vec val sz) (i1 i2 : Z) :
  vs !!! off = #i1 →
  {{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #i2 @ s; E
  {{{ RET LitV (LitInt i1); l ↦∗ vinsert off #(i1 + i2) vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_faa_offset_vec with "H"); [eauto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.
End lifting.

Typeclasses Opaque array.
