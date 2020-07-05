Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Require Import Causality.ES.Definition.

Set Implicit Arguments.

Definition lift_rel A (R:relation A) (P:A -> Prop) : relation (sig P) :=
  fun x y => R (proj1_sig x) (proj1_sig y).

Instance lift_refl {A R P} `{Reflexive A R} : Reflexive (@lift_rel A R P).
Proof. firstorder. Qed.

Instance lift_trans {A R P} `{Transitive A R} : Transitive (@lift_rel A R P).
Proof. intros (x,Px) (y,Py) (z,Pz); firstorder. Qed.

Lemma lift_order A (R:relation A) (ord : order _ R) (P:A -> Prop) : order _ (@lift_rel _ R P).
Proof.
  destruct ord as (O1,O2,O3).
  split.
  - firstorder.
  - intros (x,Px) (y,Py) (z,Pz); apply O2.
  - intros (x,Px) (y,Py) R1 R2; apply specif_eq; now apply O3.
Qed.

Lemma lift_cfl A (R:relation A) (ord : conflict _ R) (P:A -> Prop) : conflict _ (@lift_rel _ R P).
Proof. firstorder. Qed.

Lemma lift_inherit  A (R1 R2:relation A) (inherit : conflict_inherit R1 R2) (P:A -> Prop) :
  conflict_inherit (@lift_rel _ R1 P) (@lift_rel _ R2 P).
Proof.
  intros (x,Px) (y,Py) (z,Pz) H1 H2; firstorder.
Qed.
