Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Constructive_sets.

Require Import Causality.Utils.

Definition irreflexive A R: Prop := forall x:A, not (R x x).

(** Conflict relation *)
Record conflict A R := { conflict_sym : symmetric A R;
                         conflict_irfl : irreflexive A R}.

Definition conflict_inherit {A} (cmp cfl : relation A) :=
  forall x y z, cfl x y -> cmp y z -> cfl x z.

Set Implicit Arguments.

Record ES (Lbl : Set) :=
  mkES { Event: Type;
         cmp : relation Event; cmp_ord : order Event cmp;
         cfl : relation Event; cfl_conflict : conflict Event cfl;
         inherit : conflict_inherit cmp cfl;
         lbl : Event -> Lbl}.

Require Import LTS.

Definition downclosed a (cmp : relation a) (X: Ensemble a) :=
  forall x, In _ X x -> forall y, cmp y x -> In _ X y.

Definition conflict_free a (cfl : relation a) (X: Ensemble a) :=
  forall x y, In _ X x -> In _ X y -> not (cfl x y).

Definition Configuration (S:Set) (E: ES S) x := downclosed E.(cmp) x /\ conflict_free E.(cfl) x.

(* ProofIrrelevance will be used to prove the equality of two sig negleting the equality of the proof. *)
Require Coq.Logic.ProofIrrelevance.

Lemma specif_eq' A (P:A -> Prop) (x y : A) (px: P x) (py: P y) : x = y -> exist P x px = exist P y py.
Proof.
  intros exy.
  apply eq_sig_hprop.
  - intros z; apply Coq.Logic.ProofIrrelevance.proof_irrelevance.
  - easy.
Qed.

Lemma specif_eq A (P:A->Prop) (x:sig P) (y:sig P) : proj1_sig x = proj1_sig y -> x = y.
Proof. destruct x as (x,hx), y as (y,hy); apply specif_eq'. Qed.

Lemma empty (Lbl:Set) (E:ES Lbl) : sig (Configuration E).
Proof.
  split with (x:=Empty_set _).
  split; [intros x ix | intros x y ix];
    now apply Noone_in_empty in ix.
Defined.

Definition lts_of_es (Lbl:Set) (E:ES Lbl) : LTS Lbl :=
  let t x :=
      let x := proj1_sig x in
      fun '(c,a) =>
        let x' := proj1_sig c in
        exists e, (x'=Add _ x e /\ Configuration E (Add _ x e) /\ not (In _ x e) /\ E.(lbl) e = a) in
  mkLTS t (empty _).
