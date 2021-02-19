From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl excl_auth.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From intensional.heap_lang Require Import lifting proofmode notation.
From intensional.heap_lang Require Import adequacy.
From intensional Require Import stdpp_extra tactics.
Set Default Proof Using "Type".
Implicit Types t : list val.

Class model := {
  S :> Type;
  s_init : S;
  f : S → val → S;
  r : S → val → val;
}.

Section Specs.
Context `{!heapG Σ}.
Context `{model}.
Context (E: coPset).
Context (Pinit: iProp Σ)
        (is_P: gname → val → iProp Σ)
        (P_content: gname → S → iProp Σ).

Definition init_spec (init: val) : iProp Σ :=
  {{{ Pinit }}} init {{{ γ r, RET r; is_P γ r ∗ P_content γ s_init }}}.

Definition op_spec (op: val) : iProp Σ :=
  ∀ γ (x y: val),
    is_P γ x -∗
    <<< ∀ s, P_content γ s >>>
      op x y @ ⊤∖E
    <<< P_content γ (f s y), RET (r s y) >>>.

Definition lib_spec (lib: val) : iProp Σ :=
  ⌜∀ γ x, Persistent (is_P γ x)⌝ ∗
  ⌜∀ γ s, Timeless (P_content γ s)⌝ ∗
  ⌜∀ γ s1 s2, P_content γ s1 -∗ P_content γ s2 -∗ False⌝ ∗
  match lib with
  | (init, op)%V => init_spec init ∗ op_spec op
  | _ => False
  end.

End Specs.

Section Trace.

(* Inductive concurrent_trace : list val → Prop := *)
(*   | concurrent_trace_nil : *)
(*       concurrent_trace [] *)
(*   | concurrent_trace_call (tag: string) (v: val) t : *)
(*       concurrent_trace t → *)
(*       concurrent_trace (t ++ [(#tag, (#"call", v))%V]) *)
(*   | concurrent_trace_ret (tag: string) (v v': val) t : *)
(*       concurrent_trace t → *)
(*       concurrent_trace (t ++ [(#tag, (#"ret", (v, v')))%V]). *)

Inductive linearization_trace : list val → Prop :=
  | linearization_trace_nil :
      linearization_trace []
  | linearization_trace_call (tag: string) (v: val) t :
      linearization_trace t →
      linearization_trace (t ++ [(#tag, (#"call", v))%V])
  | linearization_trace_lin (tag: string) (v v': val) t :
      linearization_trace t →
      linearization_trace (t ++ [(#tag, (#"lin", (v, v')))%V])
  | linearization_trace_ret (tag: string) (v v': val) t :
      linearization_trace t →
      linearization_trace (t ++ [(#tag, (#"ret", (v, v')))%V]).

Inductive linearized_trace_for (tag: string) : list val → Prop :=
  | linearized_trace_for_nil :
      linearized_trace_for tag []
  | linearized_trace_for_call t (v v': val) :
      linearized_trace_for tag t →
      linearized_trace_for tag (t ++ [(#tag, (#"call", v)); (#tag, (#"lin", (v, v'))); (#tag, (#"ret", (v, v')))]%V).

Inductive linearized_sound `{model} : list val → S → S → Prop :=
  (* administrative steps. calls and rets are ignored. *)
  | linearized_sound_nil s :
      linearized_sound [] s s
  | linearized_sound_call_ret s0 s (tag op: string) arg t :
      linearized_sound t s0 s →
      op = "call" ∨ op = "ret" →
      linearized_sound (t ++ [(#tag, (#op, arg))%V]) s0 s
  (* lin events must be sound wrt the model *)
  | linearized_sound_lin s0 s (tag:string) v v' t :
      linearized_sound t s0 s →
      v' = r s v →
      linearized_sound (t ++ [(#tag, (#"lin", (v, v')))%V]) s0 (f s v).

Inductive matching_call_ret : list val → list val → Prop :=
  | matching_call_ret_nil t' :
      matching_call_ret [] t'
  | matching_call_ret_lin t t' (tag: string) v v':
      matching_call_ret t t' →
      matching_call_ret t (t' ++ [(#tag, (#"lin", (v, v')))%V])
  | matching_call_ret_call t t' (tag: string) v :
      matching_call_ret t t' →
      matching_call_ret (t ++ [(#tag, (#"call", v))%V]) (t' ++ [(#tag, (#"call", v))%V])
  | matching_call_ret_ret t t' (tag: string) v v' :
      matching_call_ret t t' →
      matching_call_ret (t ++ [(#tag, (#"ret", (v, v')))%V]) (t' ++ [(#tag, (#"ret", (v, v')))%V])
.

Definition check_tag (tag: string) (v: val) :=
  match v with
  | (# (LitTag tag'), _)%V => String.eqb tag tag'
  | _ => false
  end.

Definition linearizable `{model} t :=
  ∃ t', linearization_trace t'
        ∧ (∀ tag, linearized_trace_for tag (filter (check_tag tag) t'))
        ∧ matching_call_ret t t'
        ∧ ∃ s', linearized_sound t' s_init s'.

End Trace.

Module Wrap.
Section S.
Context {Σ: gFunctors}.
Context `{heapG Σ}.
Context (N N': namespace) (HNN': N ## N').
Context `{model}.
Context `{inG Σ (excl_authR (leibnizO S))}
        `{inG Σ (excl_authR (leibnizO (gname * gname)))}.

Local Notation SO := (leibnizO S).

Context (Pinit_impl: iProp Σ)
        (is_P_impl: gname → val → iProp Σ)
        (P_content_impl: gname → S → iProp Σ).
Context (HPP: ∀ γ x, Persistent (is_P_impl γ x)).
Context (HPT: ∀ γ s, Timeless (P_content_impl γ s)).

Context (init_impl op_impl : val).

Definition init : val :=
  init_impl.

Definition op : val :=
  λ: "x" "y",
    let: "t" := Fresh (#"call", "y") in
    let: "r" := op_impl "x" "y" in
    Emit ("t", (#"ret", ("y", "r"))) ;;
    "r".

Definition Pinit : iProp Σ :=
  Pinit_impl ∗ trace_is [].

Definition is_call_return (v: val) :=
  match v with
  | (#_, (#"call", _))%V | (#_, (#"ret", _))%V => true
  | _ => false
  end.

Definition trace_inv (γ γi γw: gname) (s: S) : iProp Σ :=
  own γw (●E (s:SO)) ∗
  own γ (●E ((γi, γw) : leibnizO (gname * gname))) ∗
  ∃ (β: list val),
    ⌜linearization_trace β⌝ ∗
    ⌜linearized_sound β s_init s⌝ ∗
    trace_is (filter is_call_return β).

Definition is_P γ x : iProp Σ :=
  ∃ γi γw,
    is_P_impl γi x ∗
    inv N' (∃ s, trace_inv γ γi γw s).

Definition P_content γ s : iProp Σ :=
  ∃ γi γw,
    P_content_impl γi s ∗
    own γw (◯E (s:SO)) ∗
    own γ (◯E ((γi, γw) : leibnizO (gname * gname))).

Lemma excl_agree_eq A `{inG Σ (excl_authR (leibnizO A))} γ (x y: A):
  own γ (◯E (x:leibnizO A)) -∗ own γ (●E (y:leibnizO A)) -∗ ⌜x = y⌝.
Proof.
  iIntros "H1 H2". iDestruct (own_op with "[$H1 $H2]") as "H".
  iDestruct (own_valid with "H") as %HH%excl_auth_agree. done.
Qed.

Lemma excl_auth_upd A `{inG Σ (excl_authR (leibnizO A))} γ (x y z: A):
  own γ (◯E (x:leibnizO A)) -∗ own γ (●E (y:leibnizO A)) ==∗
  own γ (◯E (z:leibnizO A)) ∗ own γ (●E (z:leibnizO A)).
Proof.
  iIntros "H1 H2". SearchAbout own "_2".
  iDestruct (own_update_2 with "H1 H2") as ">[? ?]".
  apply excl_auth_update. iModIntro. iFrame.
Qed.

(* Lemma init_correct : *)
(*   init_spec Pinit_impl is_P_impl P_content_impl init_impl -∗ *)
(*   init_spec Pinit is_P P_content init. *)
(* Proof. *)
(*   iIntros "#spec" (φ) "!> (Hi & Ht) Hφ". unfold init. *)
(*   iApply ("spec" with "Hi"). iIntros "!>" (γ x) "(Hi & Hc)". *)
(*   iApply "Hφ". iFrame. *)


Lemma op_correct :
  op_spec (↑N) is_P_impl P_content_impl op_impl -∗
  op_spec (↑N ∪ ↑N') is_P P_content op.
Proof using HPT HPP HNN'.
  iIntros "spec" (γ x y) "His".
  iDestruct "His" as (γi γw) "(#HPimpl & #?)".
  iIntros (φ) "HAU".
  unfold op. wp_pures. wp_bind (Fresh _). unfold op_spec.
  iInv N' as ">Ht" "Hclose".
  iDestruct "Ht" as (s) "(Hγw & Hγ & Ht)".
  iDestruct "Ht" as (β) "(% & % & Ht)".
  iApply (wp_fresh with "Ht"). iNext. iIntros (tag) "(Ht & %)".
  iMod ("Hclose" with "[Ht Hγw Hγ]") as "_".
  { iNext. iExists s. unfold trace_inv at 2. iFrame. 
    iExists (β ++ [(#tag, (#"call", y))%V]).
    iSplitR. iPureIntro; by constructor.
    iSplitR. iPureIntro; by constructor; eauto.
    rewrite filter_app //=. }
  iModIntro. wp_pures. clear dependent s β.

  iSpecialize ("spec" $! _ _ y with "HPimpl").
  awp_apply "spec".

  rewrite /atomic_acc /=.
  iInv N' as ">HI" "Hclose". iDestruct "HI" as (s) "HI".
  iMod "HAU" as (s') "(HH & Hnext)". by set_solver.
  iDestruct "HH" as (γi' γw') "(HHi & HHf & Hγf)".
  iDestruct "HI" as "(HHa & Hγa & HI)".
  iDestruct (excl_agree_eq with "Hγf Hγa") as %?. simplify_eq.
  iDestruct (excl_agree_eq with "HHf HHa") as %->.
  iModIntro. iExists _. iFrame "HHi".
  iSplit.
  { (* abort case *)
    iIntros "HHi". iDestruct "Hnext" as "[Hnext _]".
    iSpecialize ("Hnext" with "[HHi HHf Hγf]").
    { iExists γi, γw. iFrame. }
    iMod "Hnext". iMod ("Hclose" with "[HI HHa Hγa]") as "_"; eauto; [].
    iNext. iExists _. iFrame. }

  (* continue case *)
  iIntros "HHi". iDestruct "Hnext" as "[_ Hnext]".
  iDestruct "HI" as (β) "(% & % & Ht)".
  iDestruct (excl_auth_upd _ _ _ _ (f s y) with "HHf HHa") as ">[HHf HHa]".
  iSpecialize ("Hnext" with "[HHi HHf Hγf]").
  { iExists γi, γw. iFrame. }
  iMod "Hnext". iMod ("Hclose" with "[Ht HHa Hγa]") as "_".
  { iNext. iExists _. unfold trace_inv at 2. iFrame.
    iExists (β ++ [(#tag, (#"lin", (y, r s y)))%V]).
    rewrite filter_app app_nil_r. iFrame. iPureIntro. split.
    { by constructor. }
    { by eapply linearized_sound_lin. } }

  iModIntro. wp_pures. wp_bind (Emit _).
  iInv N' as ">HI" "Hclose".
  iDestruct "HI" as (s') "(HHa & Hγa & HI)".
  iDestruct "HI" as (β') "(% & % & Ht)".
  iApply (wp_emit with "Ht"). iIntros "!> Ht".
  iMod ("Hclose" with "[HHa Hγa Ht]").
  { iNext. iExists _. unfold trace_inv at 2. iFrame.
    iExists (β' ++ [(#tag, (#"ret", (y, r s y)))%V]).
    rewrite filter_app. iFrame. iPureIntro. split.
    { by constructor. }
    { by constructor; eauto. } }

  iModIntro. wp_pures. eauto.
Qed.

