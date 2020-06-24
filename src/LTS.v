Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Classes.RelationClasses.

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

Definition sum_arbitrary_lts (Lbl I : Set) (Family : I -> LTS Lbl) : LTS Lbl :=
  mkLTS (@trans_sum_arbitrary _ _ Family) None.

Definition empty_lts Lbl : LTS Lbl :=
  let trans _ := Empty_set _ in
  let start := False in
  mkLTS trans start.

Definition Trans S (X:LTS S) p p' a : Prop := In _ (X.(trans) p) (p',a).

Definition Simulation S (X:LTS S) (Y:LTS S) (R: X.(State) -> Y.(State) -> Prop) :=
  forall p q, R p q ->
  forall p' a, Trans X p p' a -> exists q', Trans Y q q' a /\ R p' q'.

Definition Bisimulation S (X:LTS S) (Y:LTS S) (R: X.(State) -> Y.(State) -> Prop) : Prop :=
  Simulation X Y R /\ Simulation Y X (fun x y => R y x) /\ R X.(start) Y.(start).

Definition Bisimilar S (X:LTS S) (Y:LTS S) :=
  sig (Bisimulation X Y).

Lemma bisim_refl S (X:LTS S) : Bisimilar X X.
Proof.
  split with (x:=fun x y => x=y);
    split; try split; try easy;
      intros p q rpq p' a tpp';
      exists p'; [rewrite <- rpq | rewrite rpq]; intuition.
Qed.

Lemma bisim_sym S (X Y:LTS S) : Bisimilar X Y -> Bisimilar Y X.
Proof.
  intros (R,(S1,(S2,E))).
  split with (x:=fun x y => R y x).
  split; try split; try easy.
Qed.

Lemma bisim_trans S (X Y Z:LTS S) : Bisimilar X Y -> Bisimilar Y Z -> Bisimilar X Z.
Proof.
  intros (R1,(S11,(S12,E1))) (R2,(S21,(S22,E2))).
  split with (x:=fun x z => exists y, R1 x y /\ R2 y z).
  split; try split.
  - intros p q (y,(R1y,R2y)) p' a tpp'.
    unfold Simulation in S11,S21.
    apply S11 with (p':=p') (a:=a) in R1y; try easy.
    destruct R1y as (y', (tyy', R')).
    apply S21 with (p':=y') (a:=a) in R2y; try easy.
    destruct R2y as (q', (ty'q, R'')).
    exists q'.
    split; try easy.
    exists y'; easy.
  - intros p q (y,(R1y,R2y)) p' a tpp'.
    unfold Simulation in S12,S22.
    apply S22 with (p':=p') (a:=a) in R2y; try easy.
    destruct R2y as (y', (tyy', R')).
    apply S12 with (p':=y') (a:=a) in R1y; try easy.
    destruct R1y as (q', (ty'q, R'')).
    exists q'.
    split; try easy.
    exists y'; easy.
  - now exists (Y.(start)).
Qed.

Require Import Coq.Logic.Eqdep_dec.

Module ArbitraryLTS(M:DecidableSet).

  Module DEqDep := DecidableEqDepSet(M).

  Import M.

  Theorem par_bisim_morphism (Lbl: Set) (F1 F2 : U -> LTS Lbl) :
    (forall i, Bisimilar (F1 i) (F2 i)) -> Bisimilar (par_arbitrary_lts F1) (par_arbitrary_lts F2).
  Proof.
    intros H.
    unfold Bisimilar in H.
    exists (fun x y => forall i, proj1_sig (H i) (x i) (y i)).
    split; try split.
    3:intros i;now destruct (H i) as (R,(S1,(S2,Hi))).
    all:intros p q rpq p' a (i,(H1,H2));
      generalize rpq; intros rpq'; specialize rpq with i;
        destruct (H i) as (R,(S1,(S2,S3))) eqn:eq ; simpl in *;
          unfold Simulation in S1,S2.
    1:apply S1 with (q:=q i) in H1; try easy.
    2:apply S2 with (q:=q i) in H1; try easy.
    all:destruct H1 as (q',H1).
    1:exists (fun j => match eq_dec i j with | left H => cast H (StateOf F2) q' | right _ => q j end).
    2:exists (fun j => match eq_dec i j with | left H => cast H (StateOf F1) q' | right _ => q j end).
    all:split.
    1,3:
      exists i;
      split ; [ destruct (eq_dec i i); try congruence; rewrite (DEqDep.UIP_refl _ e); intuition
              | intros j n; destruct (eq_dec i j); congruence].
    all:
      intros j; destruct (eq_dec i j);
      [ destruct e; rewrite eq; simpl; intuition
      | apply H2 in n; rewrite <- n; apply rpq'].
  Qed.

End ArbitraryLTS.

Definition par_opt A B (R: A -> B -> Prop) (x: option A) (y:option B) :=
  match x,y with
  | None, None => True
  | Some x, Some y => R x y
  | _,_ => False end.

Theorem prefixing_bisim_morphism (Lbl:Set) (X Y:LTS Lbl) (a:Lbl) :
  Bisimilar X Y -> Bisimilar (prefixing_lts X a) (prefixing_lts Y a).
Proof.
  intros (R,(SR1,(SR2,SR3))).
  unfold Simulation in SR1,SR2.
  exists (par_opt R).
  split; try split; try easy.
  all:intros p q rpq p' a' tpp';
    destruct p as [p|],q as [q|],p' as [p'|]; try easy.
  1:apply SR1 with (q:=q) in tpp'; try easy.
  3:apply SR2 with (q:=q) in tpp'; try easy.
  1,3:destruct tpp' as (q',(H1,H2)); exists (Some q'); intuition.
  all:destruct tpp' as (H1,H2).
  1:exists (Some (start Y)).
  2:exists (Some (start X)).
  all: split; [now rewrite H2|now rewrite H1].
Qed.
