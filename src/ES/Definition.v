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

Definition union_rel A (R1 R2 : relation A) := fun x y => R1 x y \/ R2 x y.

Lemma conflict_union A (R1 R2 : relation A) (cR1 : conflict _ R1) (cR2 : conflict _ R2) :
  conflict _ (union_rel R1 R2).
Proof. firstorder. Qed.

Record ES (Lbl : Set) :=
  mkES { Event: Type;
         cmp : relation Event; cmp_ord : order Event cmp;
         cfl : relation Event; cfl_conflict : conflict Event cfl;
         inherit : conflict_inherit cmp cfl;
         lbl : Event -> Lbl}.

Definition empty_rel A : A -> A -> Prop := fun _ _ => False.

Lemma empty_order : order _ (@empty_rel False).
Proof. split; intuition; intros x; intuition. Qed.

Lemma empty_conflict : conflict _ (@empty_rel False).
Proof. split; intuition; intros x hx; intuition. Qed.

Lemma empty_inherit : conflict_inherit (@empty_rel False) (@empty_rel False).
Proof. firstorder. Qed.

Lemma false_all S : False -> S. Proof. intuition. Qed.

Definition empty_es S : ES S :=
  mkES empty_order empty_conflict empty_inherit (@false_all S).

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

Theorem empty_bisim (Lbl:Set) : Bisimilar (empty_lts Lbl) (lts_of_es (empty_es Lbl)).
Proof.
  unfold Bisimilar.
  exists (fun _ _ => True).
  split; try split; try easy.
  intros p q rpq p' a (false,tpp').
  easy.
Qed.

Definition minimum A (R:relation A) a := forall b, R b a -> b = a.

Theorem config_singl_minimum Lbl (E:ES Lbl) a : minimum (cmp E) a -> Configuration E (Singleton _ a).
Proof.
  intros M.
  split.
  - intros x ix y cxy.
    apply Singleton_inv in ix.
    destruct ix.
    unfold minimum in M; apply M in cxy.
    rewrite cxy; intuition.
  - intros x y ix iy cxy.
    apply Singleton_inv in ix.
    apply Singleton_inv in iy.
    destruct ix,iy.
    destruct (cfl_conflict E) as (R1,R2).
    unfold irreflexive,not in R2; now apply R2 with a.
Qed.
