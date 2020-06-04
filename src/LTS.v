Require Import Coq.Sets.Constructive_sets.
Require Coq.Lists.List.

Require Import Causality.Utils.

Set Implicit Arguments.

Record LTS s x :=
  mkLTS { t : x -> Ensemble (x * s);
          start : x }.

Definition par_lts S A B (X:LTS S A) (Y:LTS S B) :=
  let t '(x,y) :=
      (fun '((x',y'),a) =>
         (y=y' /\ In _ (X.(t) x) (x',a)) \/ (x=x' /\ In _ (Y.(t) y) (y',a))) in
  let start := (X.(start), Y.(start)) in
  mkLTS t start.

Definition prefixing_lts S A (a:S) (X:LTS S A) : LTS S (option A) :=
  let t x :=
      fun '(x',a') =>
        match x with
        | None => maybe False (fun x' => x'=X.(start) /\ a'=a) x'
        | Some x => maybe False (fun x' => X.(t) x (x',a')) x' end in
  mkLTS  t None.

Definition Trans S A (X:LTS S A) (p p':A) (a:S) : Prop := In _ (X.(t) p) (p',a).

Definition Simulation S A B (X:LTS S A) (Y:LTS S B) (R :A -> B -> Prop) :=
  forall p q, R p q ->
  forall p' a, Trans X p p' a -> exists q', Trans Y q q' a /\ R p' q'.

Definition Bisimulation S A B (X:LTS S A) (Y:LTS S B) (R:A->B->Prop) : Prop :=
  Simulation X Y R /\ Simulation Y X (fun x y => R y x) /\ R X.(start) Y.(start).

Definition Bisimilar S A B (X:LTS S A) (Y:LTS S B) : Prop :=
  exists R, Bisimulation X Y R.
