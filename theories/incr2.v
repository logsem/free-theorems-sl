From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import par.
From iris.program_logic Require Import adequacy.

Definition incr2 : val :=
  rec: "loop" "l" :=
    (("l" <- !"l" + #2) ||| ("l" <- !"l" + #2)) ;;
    "loop" "l".

Lemma Zeven_add_2 n : Z.even n -> Z.even (n + 2).
Proof.
  rewrite (ltac:(lia): n + 2 = Z.succ (Z.succ n))
          Z.even_succ_succ //.
Qed.

Section S.
  Context `{!heapG Σ} `{!spawnG Σ} (N : namespace).

  Lemma incr2_spec (ℓ: loc) :
    {{{ inv N (∃ (x:Z), ℓ ↦ #x ∗ ⌜Z.even x⌝)%I }}}
      incr2 #ℓ
    {{{ RET #(); True }}}.
  Proof.
    iIntros (φ) "#Hi Hφ". iLöb as "IH".
    wp_lam. wp_bind (_ ||| _)%E. wp_pures.
    (* specification for the two threads *)
    iAssert (WP #ℓ <- ! #ℓ + #2 {{ _, True }})%I with "[Hi]" as "Ht".
    { wp_bind (!#ℓ)%E. iInv N as (x) ">[Hℓ %]" "Hclose". wp_load.
      iMod ("Hclose" with "[Hℓ]"). now eauto.
      iModIntro. wp_pures.
      iInv N as (x') ">[Hℓ %]" "Hclose". wp_store.
      iMod ("Hclose" with "[Hℓ]"); eauto.
      iNext. iExists (x+2). iFrame. eauto using Zeven_add_2. }
    iApply (wp_par (fun _ => ⌜True⌝)%I (fun _ => ⌜True⌝)%I);
      [ iApply "Ht" .. |].
    iIntros. iNext. wp_pures. iApply "IH". eauto.
  Qed.
End S.

Class heapPreG Σ := HeapPreG {
  heap_preG_iris :> invPreG Σ;
  heap_preG_heap :> gen_heapPreG loc val Σ;
  heap_preG_proph :> proph_mapPreG proph_id (val * val) Σ;
}.

Section S.
  Context (N: namespace).
  Context `{!spawnG Σ}.
  Context `{heapPreG Σ}.

  Lemma invariant_adequacy :
    forall (ℓ : loc) (σ1 σ2 : state) (es: list expr),
      let φ := (fun (σ: state) => ∃ (x:Z),
                  heap σ !! ℓ = Some (#x) ∧ Z.even x) in
      rtc erased_step ([incr2 #ℓ], σ1) (es, σ2) →
      φ σ1 →
      φ σ2.
  Proof.
    intros * Hstep Hσ1.
    pose proof (@incr2_spec Σ) as S.

    pose proof (wp_invariance Σ heap_lang NotStuck) as L. cbn in L.
    specialize (L (incr2 #ℓ) σ1 es σ2 (φ σ2)).
    eapply L; eauto. intros Hinv κs. clear L.

    (* Allocate heap resources corresponding to (heap σ1) *)
    iDestruct (gen_heap_init (delete ℓ (heap σ1))) as ">H".
    iDestruct "H" as (Hheap) "Hσ1".
    (* Also allocate the prophecy-related resources, that appear in the standard
       state interpretation in heapG_irisG (this is needed for things to match
       later on). *)
    iDestruct (proph_map_init κs (used_proph_id σ1)) as ">H".
    iDestruct "H" as (Hproph) "Hpr1".

    (* /!\ do not use 'pose proof', as [heapG_invG HeapΣ] needs to
       stay convertible to Hinv for things to typecheck later on. *)
    set (HeapΣ := HeapG Σ Hinv Hheap Hproph).

    (* Add ℓ back to the heap, so that we get a corresponding pointsto *)
    destruct Hσ1 as [v1 [Hσ1 E1]].
    iMod (gen_heap_alloc (delete ℓ (heap σ1)) ℓ (#v1) with "Hσ1")
      as "(Hσ1 & Hℓ & ?)".
    by rewrite lookup_delete.

    (* Allocate the same invariant as in [incr2_spec], so that we can feed it to
       [S] *)
    iPoseProof (@inv_alloc Σ Hinv N ⊤
      (∃ (x:Z), ℓ ↦ #x ∗ ⌜Z.even x⌝)%I with "[Hℓ]") as ">#HI".
    by iExists v1; eauto.

    rewrite insert_delete insert_id //.
    specialize (S HeapΣ spawnG0 N ℓ (fun _ => True%I)).
    iPoseProof (S with "HI") as "S".

    iModIntro.

    (* /!\ this has to match exactly the state_interp of heapG_irisG *)
    iExists (fun σ 𝜅s _ =>
      gen_heap_ctx (heap σ) ∗ proph_map_ctx 𝜅s (used_proph_id σ))%I.
    iExists (fun _ => True%I).
    iSplitL "Hσ1 Hpr1"; [ by iFrame |].
    iSplitL "S". by iApply "S".
    iIntros "[Hheap ?]". iExists (⊤ ∖ ↑N).
    iInv N as (x) ">[Hℓ %]" "Hclose".
    iDestruct (gen_heap_valid with "Hheap Hℓ") as "%".
    iModIntro. iPureIntro. unfold φ. eauto.
  Qed.
End S.

Theorem invariant_adequacy' (ℓ : loc) (σ1 σ2 : state) (es: list expr) :
    let φ := (fun (σ: state) =>
              ∃ (x:Z), heap σ !! ℓ = Some (#x) ∧ Z.even x) in
    φ σ1 →
    rtc erased_step ([incr2 #ℓ], σ1) (es, σ2) →
    φ σ2.
Proof.
  set (Σ := #[invΣ; gen_heapΣ loc val; spawnΣ; proph_mapΣ proph_id (val * val)]).
  set (HG := HeapPreG Σ _ _ _).
  intros. eapply (@invariant_adequacy nroot Σ); eauto.
  typeclasses eauto.
Qed.

