Require Import Coq.Sets.Constructive_sets.
Require Coq.Vectors.Vector.

Require Import Causality.Utils.

Set Implicit Arguments.

Record LTS s x :=
  mkLTS { t : x -> Ensemble (x * s);
          start : x }.

Definition prefixing_lts S A (a:S) (X:LTS S A) : LTS S (option A) :=
  let t x :=
      fun '(x',a') =>
        match x with
        | None => maybe False (fun x' => x'=X.(start) /\ a'=a) x'
        | Some x => maybe False (fun x' => X.(t) x (x',a')) x' end in
  mkLTS t None.

Definition par_lts S A B (X:LTS S A) (Y:LTS S B) :=
  let t '(x,y) :=
      (fun '((x',y'),a) =>
         (y=y' /\ In _ (X.(t) x) (x',a)) \/ (x=x' /\ In _ (Y.(t) y) (y',a))) in
  let start := (X.(start), Y.(start)) in
  mkLTS t start.

(* Arbitrary tuple *)
Definition ATuple (A:Type) : nat -> Type :=
  fix vec n :=
    match n return Type with
    | O   => unit
    | S n => prod A (vec n)
    end.

Definition unit_lts S :=
  @mkLTS S unit (fun _ => Empty_set _) tt.

Fixpoint par_multiple_lts S A n (xs:Vector.t (LTS S A) n) : LTS S (ATuple A n) :=
  match xs in Vector.t _ n return LTS S (ATuple A n) with
  | Vector.nil _ => unit_lts _
  | Vector.cons _ x n xs =>
    par_lts x (par_multiple_lts xs) end.

Definition Trans S A (X:LTS S A) (p p':A) (a:S) : Prop := In _ (X.(t) p) (p',a).

Definition Simulation S A B (X:LTS S A) (Y:LTS S B) (R :A -> B -> Prop) :=
  forall p q, R p q ->
  forall p' a, Trans X p p' a -> exists q', Trans Y q q' a /\ R p' q'.

Definition Bisimulation S A B (X:LTS S A) (Y:LTS S B) (R:A->B->Prop) : Prop :=
  Simulation X Y R /\ Simulation Y X (fun x y => R y x) /\ R X.(start) Y.(start).

Definition Bisimilar S A B (X:LTS S A) (Y:LTS S B) : Prop :=
  exists R, Bisimulation X Y R.
