Require Import Coq.Sets.Constructive_sets.

Require Import Causality.Utils.

Record LTS s x :=
  mkLTS { t : x -> Ensemble (x * s);
          start : x }.

Arguments t {s x}.
Arguments start {s x}.

Definition par_lts {s x y} (X:LTS s x) (Y:LTS s y) :=
  let t '(x,y) :=
      (fun '((x',y'),a) =>
         (y=y' /\ In _ (X.(t) x) (x',a)) \/ (x=x' /\ In _ (Y.(t) y) (y',a))) in
  let start := (X.(start), Y.(start)) in
  mkLTS _ _ t start.

Definition prefixing_lts {S A} (a:S) (X:LTS S A) : LTS S (option A) :=
  let t x :=
      fun '(x',a') =>
        match x with
        | None => maybe False (fun x' => x'=X.(start) /\ a'=a) x'
        | Some x => maybe False (fun x' => X.(t) x (x',a')) x' end in
  mkLTS _ _ t None.

Definition Trans {S A} (X:LTS S A) (p p':A) (a:S) : Prop := In _ (X.(t) p) (p',a).

Definition Simulation {S A B} (X:LTS S A) (Y:LTS S B) (R :A -> B -> Prop) :=
  forall p q, R p q ->
  forall p' a, Trans X p p' a -> exists q', Trans Y q q' a /\ R p' q'.

Definition Bisimulation {S A B} (X:LTS S A) (Y:LTS S B) (R:A->B->Prop) : Prop :=
  Simulation X Y R /\ Simulation Y X (fun x y => R y x).

Definition Bisimilar {S A B} (X:LTS S A) (Y:LTS S B) : Prop :=
  exists R, Bisimulation X Y R.
