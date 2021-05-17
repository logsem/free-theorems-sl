From intensional.heap_lang Require Import lang.
From intensional.examples Require Import stdpp_extra.

Inductive Learnt {A: Type} (a: A) :=
| AlreadyKnown : Learnt a.

Ltac learnHyp fact :=
  lazymatch goal with
  | [ H: Learnt fact |- _ ] =>
    fail 0 "fact" fact "has already been learnt"
  | _ => let type := type of fact in
         lazymatch goal with
         | [ H: @Learnt type _ |- _ ] =>
           fail 0 "fact" fact "of type" type "was already learnt through" H
         | _ => pose proof (AlreadyKnown fact)
         end
  end.

Ltac learn fact :=
  let X := fresh in pose proof fact as X; learnHyp X.

Ltac clear_learnt :=
  repeat match goal with
  | H : Learnt _ |- _ => clear H
  end.

Create HintDb eassumpp.
Hint Resolve or_introl : eassumpp.
Hint Resolve or_intror : eassumpp.
Hint Resolve conj : eassumpp.
Hint Resolve Z.lt_le_incl : eassumpp.
Ltac eassumpp := typeclasses eauto with eassumpp.

Ltac go_step :=
  progress repeat match goal with
  | H : ((_ ++ [_]) !! _ = Some _) |- _ => apply lookup_snoc_Some in H
  | H : context [ (_ ++ [_]) !! _ = Some _ ] |- _ => rewrite -> lookup_snoc_Some in H
  | |- ((_ ++ [_]) !! _ = Some _) => apply lookup_snoc_Some
  | H : (_ !! _ = Some _) |- _ => learn (lookup_lt_Some _ _ _ H)

  | |- context [ length (_ ++ _) ] => rewrite app_length
  | H : context [ length (_ ++ _) ] |- _ => rewrite -> app_length in H

  | H1 : ?t `prefix_of` _, H2 : ?t !! _ = Some _ |- _ =>
    learn (prefix_lookup _ _ _ _ H2 H1)

  (* these are useful to be picked up by [eassumpp] when instantiating lemmas *)
  | H1: Z.lt ?a ?b, H2: Z.lt ?b ?c |- _ => learn (Z.lt_trans _ _ _ H1 H2)
  | H1: Z.le ?a ?b, H2: Z.lt ?b ?c |- _ => learn (Z.le_lt_trans _ _ _ H1 H2)
  | H1: Z.lt ?a ?b, H2: Z.le ?b ?c |- _ => learn (Z.lt_le_trans _ _ _ H1 H2)
  | H1: Z.le ?a ?b, H2: Z.le ?b ?c |- _ => learn (Z.le_trans _ _ _ H1 H2)

  | |- ¬ _ => intro
  | H : ∃ _, _ |- _ => destruct H
  | H : ∀ _, _ |- _ =>
    let Hty := type of H in
    let HTy := type of Hty in
    match HTy with
    | Prop =>
      let X := fresh in
      unshelve (efeed pose proof H as X; [
                  clear dependent H (* avoid looping *); eassumpp ..
                | learnHyp X ]); []
    end
  end.

Ltac go :=
  repeat first [
     progress intros
    | progress cbn
    | eassumption
    | progress simplify_eq/=
    | destruct_and!
    | go_step
    | destruct_or!
    | solve [ eauto ]
    | clear_learnt; lia ].

Ltac go_trysolve_step :=
  match goal with
  | |- ∃ _, _ => eexists
  | |- _ ∧ _ => split
  end.

Tactic Notation "go*" :=
  (* the [repeat repeat] is a hack; need: truly multigoal repeat *)
  solve [ repeat (repeat (go; repeat go_trysolve_step)) ].

Goal forall A B (f : A → B) (a: A), True. intros. Fail go_step. Abort.
Goal forall A B (f : ∀ (x: A), B x), True. intros. Fail go_step. Abort.
Goal forall A B (f : ∀ (x: A), B x) (a: A), True. intros. Fail go_step. Abort.

Goal forall A B (C: _ → _ → Prop) (f : ∀ (x y: A), B x y → C x y) a b (H: B a b), False.
  intros. go_step. Abort.

Goal forall A B C (D: _ → _ → _ → Prop) (f : ∀ (x y z: A), B x y → C y z → D x y z) a b c (H: B a b) (H': C b c), False.
  intros. go_step. Abort.
