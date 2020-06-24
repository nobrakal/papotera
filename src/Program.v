Require Import Coq.Lists.List.

Set Implicit Arguments.

Inductive mem_op (N:Set) : Set :=
| Read : N -> nat -> mem_op N
| Write : N -> nat -> mem_op N.

Inductive instruction N :=
| Assign : N -> nat -> instruction N
| Store : N -> N -> instruction N.

Definition thread N := list (instruction N).

Definition program N := list (thread N).

Definition interp_thread_aux A N (prefixing : A -> mem_op N -> A) sum (i: instruction N) cont :=
  match i with
  | Assign x k => prefixing cont (Write x k)
  | Store r x => sum (fun n => prefixing cont (Read x n)) end.

Definition interp_thread A (N:Set) prefixing sum (empty : A) : thread N -> A :=
  fold_right (interp_thread_aux prefixing sum) empty.

Definition interp A (N:Set) parallel (interp_thread : thread N -> A) (p : program N) : A :=
  parallel (fun i => interp_thread (nth i p nil)).

Require Import Causality.LTS.

Definition interp_thread_lts (N:Set) : thread N -> LTS (mem_op N) :=
  interp_thread (@prefixing_lts _) (@sum_arbitrary_lts _ _) (empty_lts _).

Definition interp_lts (N:Set) : program N -> LTS (mem_op N) :=
  interp (@par_arbitrary_lts _ _) (@interp_thread_lts N).

Require Import Causality.ES.Definition.
Require Import Causality.ES.Prefixing.
Require Import Causality.ES.Parallel.
Require Import Causality.ES.Sum.

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.PeanoNat.

Module NatDecSet.
  Definition U := nat.
  Definition eq_dec : forall x y:U, {x = y} + {x <> y} := Nat.eq_dec.
End NatDecSet.

Module Par := ArbitraryParallel(NatDecSet).
Module Sum := ArbitrarySum(NatDecSet).

Definition interp_thread_es (N:Set) : thread N -> ES (mem_op N) :=
  interp_thread (@prefixing_es _) (@Sum.sum_arbitrary_es _) (empty_es _).

Definition interp_es (N:Set) : program N -> ES (mem_op N) :=
  interp (@Par.par_arbitrary_es _) (@interp_thread_es N).

Module ALTS := ArbitraryLTS(NatDecSet).

Theorem interp_ok (N:Set) (p:program N) : Bisimilar (interp_lts p) (lts_of_es (interp_es p)).
Proof.
  apply bisim_trans with
    (Y:=(@par_arbitrary_lts _ _) (fun i => lts_of_es (interp_thread_es  (nth i p nil))));
    try apply Par.par_arbitrary_bisim.
  apply ALTS.par_bisim_morphism.
  intros i.
Admitted.
