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

Require Import Coq.Lists.List.
Import ListNotations.

Definition trace (N:Set) := list (mem_op N).

Definition nat_of_mem_op (N:Set) (x:mem_op N) :=
  match x with
  | Write _ k | Read _ k => k end.

Fixpoint trace_ok (N:Set) (x:N) (n:nat) (ts:trace N) :=
  match ts with
  | [] => True
  | t::ts =>
    match t with
    | Write x' k => x = x' /\ trace_ok x k ts
    | Read x' k => x = x' /\ k = n /\ trace_ok x n ts end end.

Require Import Coq.Relations.Relation_Definitions.
Require Import Causality.ES.Definition.

Fixpoint prefix A (xs ys:list A) :=
  match xs,ys with
  | [],_ => True
  | x::xs,y::ys => x=y /\ prefix xs ys
  | _,[] => False end.

Lemma prefix_order A : order _ (@prefix A).
Proof.
  split.
  - intros x; induction x; firstorder.
  - intros x.
    induction x; intros y; destruct y; try easy.
    intros z H1 H2.
    destruct z; simpl in *; try easy.
    destruct H1 as (E1,H1), H2 as (E2,H2).
    split.
    + now rewrite E1.
    + now apply IHx with y.
  - unfold antisymmetric.
    intros x; induction x; simpl in *.
    + intros y; destruct y; easy.
    + intros y Hy; destruct y; try easy; simpl in *.
      intros H.
      destruct Hy as (Ey,Hy).
      f_equal; try easy.
      now apply IHx.
Qed.

Definition lift_rel A (R:relation A) (P:A -> Prop) : relation (sig P) :=
  fun x y => R (proj1_sig x) (proj1_sig y).

Lemma restrict_order A (R:relation A) (ord : order _ R) (P:A -> Prop) : order _ (@lift_rel _ R P).
Proof.
  destruct ord as (O1,O2,O3).
  split.
  - firstorder.
  - intros (x,Px) (y,Py) (z,Pz); apply O2.
  - intros (x,Px) (y,Py) R1 R2; apply specif_eq; now apply O3.
Qed.

Definition noprefix A (xs ys:list A) := not (prefix xs ys) /\ not (prefix ys xs).

Lemma noprefix_cons A (x y:A) (xs ys:list A) : x=y -> noprefix (x::xs) (y::ys) <-> noprefix xs ys.
Proof. firstorder. Qed.

Lemma noprefix_cons' A (x y:A) (xs ys:list A) : x<>y -> noprefix xs ys -> noprefix (x::xs) (y::ys).
Proof. intros n; split; intros (H1,H2); congruence. Qed.

Lemma noprefix_cfl A : conflict (list A) (@noprefix A).
Proof.
  split.
  - firstorder.
  - intros x (C1,C2).
    destruct C2; induction x; firstorder.
Qed.

Lemma restrict_cfl A (R:relation A) (ord : conflict _ R) (P:A -> Prop) : conflict _ (@lift_rel _ R P).
Proof. firstorder. Qed.

Lemma prefix_propagate A (x y z:list A) : prefix x z -> prefix y z -> prefix x y \/ prefix y x.
Proof.
  revert y z.
  induction x.
  - intuition.
  - intros y z XZ YZ.
    destruct z,y; intuition.
    destruct XZ as (E1,XZ), YZ as (E2,YZ).
    assert (prefix x y \/ prefix y x) as H by (now apply IHx with z).
    destruct H; [left | right]; rewrite E1, <- E2; now split.
Qed.

Lemma prefix_noprefix_inherit A: conflict_inherit (@prefix A) (@noprefix A).
Proof.
  intros x y z (N1,N2) P1.
  split; intros P2.
  - assert (prefix x y \/ prefix y x) as H by (now apply prefix_propagate with z).
    now destruct H.
  - destruct (prefix_order A) as (R,T,An).
    unfold transitive in T.
    now apply N2, T with z.
Qed.

Lemma restrict_inherit  A (R1 R2:relation A) (inherit : conflict_inherit R1 R2) (P:A -> Prop) :
  conflict_inherit (@lift_rel _ R1 P) (@lift_rel _ R2 P).
Proof.
  intros (x,Px) (y,Py) (z,Pz) H1 H2; firstorder.
Qed.

Definition interp_val_es (N:Set) (x:N) (mu:nat) : ES (mem_op N) :=
  let lbl '(exist _ l H) := proj1_sig (projT2 (@exists_last _ l (proj1 H))) in
  @mkES _ {xs | xs <> nil /\ trace_ok x mu xs} _
    (restrict_order (@prefix_order _) _) _
    (restrict_cfl (@noprefix_cfl _) _)
    (@restrict_inherit _ _ _ (@prefix_noprefix_inherit _) _) lbl.

Require Import Coq.Logic.Eqdep_dec.
Require Import Causality.ES.Parallel.

Module InterpMemES(NS:DecidableSet).

End InterpMemES.

Require Import Coq.Sets.Constructive_sets.

Module InterpMemOK(NS:DecidableSet).
  Import NS.

  Module Par := ArbitraryParallel(NS).

  Definition interp_mem_es (mu:mem_state U) : ES (mem_op U) :=
    Par.par_arbitrary_es (fun i => interp_val_es i (mu i)).

  Module ALTS := ArbitraryLTS(NS).

  Lemma interp_val_ok (x:U) (mu:nat) :
    Bisimilar (interp_val_lts x mu) (lts_of_es (interp_val_es x mu)).
  Proof.
  Admitted.

  Theorem interp_mem_ok (mu:mem_state U) :
    Bisimilar (interp_mem_lts mu) (lts_of_es (interp_mem_es mu)).
  Proof.
    apply bisim_trans with (Y:=par_arbitrary_lts (fun i => lts_of_es (interp_val_es i (mu i)))).
    - apply ALTS.par_bisim_morphism.
      intros i.
      apply interp_val_ok.
    - apply Par.par_arbitrary_ok.
  Qed.

End InterpMemOK.
