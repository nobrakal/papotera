Require Import Coq.Sets.Constructive_sets.
Require Coq.Vectors.Vector.

Require Import Causality.Utils.

Set Implicit Arguments.

Record LTS (Lbl:Set) :=
  mkLTS { State : Type;
          trans : State -> Ensemble (State * Lbl);
          start : State }.

Definition prefixing_lts Lbl (X:LTS Lbl) (a:Lbl) : LTS Lbl :=
  let trans x :=
      fun '(x',a') =>
        match x with
        | None => maybe False (fun x' => x'=X.(start) /\ a'=a) x'
        | Some x => maybe False (fun x' => X.(trans) x (x',a')) x' end in
  mkLTS trans None.

Definition par_lts Lbl (X:LTS Lbl) (Y:LTS Lbl) :=
  let trans '(x,y) :=
      (fun '((x',y'),a) =>
         (y=y' /\ In _ (X.(trans) x) (x',a)) \/ (x=x' /\ In _ (Y.(trans) y) (y',a))) in
  let start := (X.(start), Y.(start)) in
  mkLTS trans start.

Definition trans_par_arbitrary (Lbl I : Set) (Family : I -> LTS Lbl) :
  (forall i:I, State (Family i)) -> Ensemble ((forall i:I, State (Family i)) * Lbl) :=
  fun x =>
    fun '(x',a) =>
      exists i, In _ (trans (Family i) (x i)) (x' i, a)
        /\ forall j, i<>j -> (x j) = (x' j).

Definition par_arbitrary_lts (Lbl I : Set) (Family : I -> LTS Lbl) : LTS Lbl :=
  let start := fun i => start (Family i) in
  mkLTS (trans_par_arbitrary Family) start.

Definition StateOf (Lbl I:Set) (Family : I -> LTS Lbl) := fun i => State (Family i).

Definition trans_sum_arbitrary (Lbl I : Set) (Family : I -> LTS Lbl) :
  (option (sigT (StateOf Family))) -> Ensemble (option (sigT (StateOf Family)) * Lbl) :=
  fun x =>
    fun '(x',a) =>
      match x' with
      | None => False
      | Some (existT _ j x') =>
        match x with
        | None =>
          In _ (trans (Family j) (start (Family j))) (x',a)
        | Some (existT _ i x) =>
          exists (H:j=i),
          In _ (trans (Family i) x) (cast H (StateOf Family) x',a) end
      end.

Definition sum_arbitrary (Lbl I : Set) (Family : I -> LTS Lbl) : LTS Lbl :=
  mkLTS (@trans_sum_arbitrary _ _ Family) None.

Definition Trans S (X:LTS S) p p' a : Prop := In _ (X.(trans) p) (p',a).

Definition Simulation S (X:LTS S) (Y:LTS S) (R: X.(State) -> Y.(State) -> Prop) :=
  forall p q, R p q ->
  forall p' a, Trans X p p' a -> exists q', Trans Y q q' a /\ R p' q'.

Definition Bisimulation S (X:LTS S) (Y:LTS S) (R: X.(State) -> Y.(State) -> Prop) : Prop :=
  Simulation X Y R /\ Simulation Y X (fun x y => R y x) /\ R X.(start) Y.(start).

Definition Bisimilar S (X:LTS S) (Y:LTS S) : Prop :=
  exists R, Bisimulation X Y R.
