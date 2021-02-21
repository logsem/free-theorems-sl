From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import proph_map.
From iris.program_logic Require Export weakestpre adequacy.
From intensional Require Import proofmode notation.
Set Default Proof Using "Type".

Class heapPreG Σ := HeapPreG {
  heap_preG_iris :> invPreG Σ;
  heap_preG_heap :> gen_heapPreG loc val Σ;
  heap_preG_proph :> proph_mapPreG proph_id (val * val) Σ;
  heap_preG_trace :> trace_preG Σ;
}.

Definition heapΣ : gFunctors := #[invΣ; gen_heapΣ loc val; proph_mapΣ proph_id (val * val); traceΣ].
Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapPreG Σ.
Proof. solve_inG. Qed.

Definition heap_adequacy Σ `{!heapPreG Σ} s e σ φ :
  (∀ `{!heapG Σ}, ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (??) "".
  iMod (gen_heap_init σ.(heap)) as (?) "Hh".
  iMod (proph_map_init κs σ.(used_proph_id)) as (?) "Hp".
  iMod (trace_auth_init σ.(trace)) as (?) "(Ht & _ & _)".
  iModIntro. iExists
    (λ σ κs, (gen_heap_ctx σ.(heap) ∗ trace_auth σ.(trace) ∗ proph_map_ctx κs σ.(used_proph_id))%I),
    (λ _, True%I).
  iFrame. iApply (Hwp (HeapG _ _ _ _ _)).
Qed.

Definition heap_invariance Σ `{!heapPreG Σ} (N: namespace) (I: list val → Prop) s e σ :
  I (trace σ) →
  (∀ `{!heapG Σ}, ⊢ trace_inv N I -∗ trace_is (trace σ) -∗ WP e @ s; ⊤ {{ _, True }}) →
  ∀ σ' t,
    rtc erased_step ([e], σ) (t, σ') →
    I (trace σ').
Proof.
  intros HI Hwp σ' t.
  eapply (wp_invariance Σ _ s _ _ _ _ (I (trace σ'))). iIntros (Hinv κs) "".
  iMod (gen_heap_init σ.(heap)) as (?) "Hh".
  iMod (proph_map_init κs σ.(used_proph_id)) as (?) "Hp".
  iMod (trace_auth_init σ.(trace)) as (?) "(Hta & Ht & Hth)".
  iDestruct (inv_alloc N _ (∃ t, trace_half_frag t ∗ ⌜I t⌝) with "[Hth]") as ">#HI".
  { iNext. eauto. }
  iModIntro. iExists
    (λ σ κs _, (gen_heap_ctx σ.(heap) ∗ trace_auth σ.(trace) ∗ proph_map_ctx κs σ.(used_proph_id))%I),
    (λ _, True%I).
  iFrame. iSplitL.
  { iDestruct (Hwp (HeapG _ _ _ _ _)) as "Hwp". iApply ("Hwp" with "HI Ht"). }
  iIntros "(_ & Hta & _)". iExists _.
  iInv "HI" as ">Ht'" "_". iDestruct "Ht'" as (t') "(Ht' & %)".
  iDestruct (trace_auth_half_frag_agree with "Hta Ht'") as %->. iModIntro. eauto.
Qed.

Require Import iris.program_logic.hoare.

Lemma module_invariance {Σ} `{heapPreG Σ} (N: namespace)
  (Φ: ∀ `{heapG Σ}, iProp Σ → val → iProp Σ)  (* Module specification *)
  (P0: iProp Σ) (* Initial resources required by the module *)
  (e: val → expr) (* Context program, parameterized by the module *)
  (e_init: expr) (* Initialization code, used to allocate resources for P0 *)
  (imimpl: val) (* Implementation of the module (instrumented) *)
  (good_trace: list val → Prop) (* Trace property *)
  (σ: state) (* Initial state *)
:
  (* The initial trace must satisfy the property *)
  good_trace (trace σ) →
  (* The context must be safe, given a module satisfying the specification Φ *)
  (⊢ ∀ `{heapG Σ} P m, Φ P m -∗ {{{ P }}} e m {{{ v, RET v; True }}}) →
  (* The initialization code must provide P0 *)
  (⊢ ∀ `{heapG Σ}, {{ True }} e_init {{ _, P0 }}) →
  (* The implementation provided for the module (iops) must satisfy the specification Φ.
     On top of P0 it is given SL resources for the trace. *)
  (⊢ ∀ `{heapG Σ}, Φ (P0 ∗ trace_is (trace σ) ∗ trace_inv N good_trace)%I imimpl) →
  (* Then the trace remains good at every step *)
  ∀ σ' e',
    rtc erased_step ([(e_init;; e imimpl)%E], σ) (e', σ') →
    good_trace (trace σ').
Proof.
  intros Htrσ Hctx Hinit Himpl σ' e' Hsteps.
  eapply heap_invariance. done. by apply Htrσ. 2: eapply Hsteps.
  iIntros (?) "HI Htr". wp_bind e_init.
  iApply wp_wand. by iApply Hinit.
  iIntros (v) "H0". wp_pures.
  iApply (Hctx with "[] [H0 Htr HI]").
  - iApply Himpl.
  - iFrame.
  - eauto.
Qed.

