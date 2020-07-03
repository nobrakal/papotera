Set Implicit Arguments.

Definition mem_state (N:Set) := N -> nat.

Require Import Causality.LTS.
Require Import Causality.Program.

Definition next_candidate (N:Set) (x:N) (n:nat) : nat -> mem_op N -> Prop :=
  fun k a =>
    match a with
    | Write x' k' => x=x' /\ k=k'
    | Read x' k' => x=x' /\ k=n /\ k=k' end.

Definition interp_val_lts (N:Set) (x:N) (mu:nat) : LTS (mem_op N) :=
  let trans n := fun '(k,a) => next_candidate x n k a in
  mkLTS trans mu.

Definition interp_mem_lts (N:Set) (mu:mem_state N) : LTS (mem_op N) :=
  par_arbitrary_lts (fun x => interp_val_lts x (mu x)).
