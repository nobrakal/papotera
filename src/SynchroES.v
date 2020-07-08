Require Import Coq.Logic.FinFun.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Sets.Constructive_sets.

Require Import Causality.LTS.
Require Import Causality.ES.Definition.

Set Implicit Arguments.

Definition Bijective A B (f:A -> B) := Injective f /\ Surjective f.

Definition Acyclic A (R : relation A) := irreflexive _ (clos_trans A R).

Instance clos_refl_trans_1n_refl A (R : relation A) : Reflexive (clos_refl_trans_1n _ R).
Proof.
  intros x; now apply rt1n_refl.
Qed.

Instance clos_refl_trans_1n_trans A (R : relation A) : Transitive (clos_refl_trans_1n _ R).
Proof.
  intros x y z Hxy Hyz.
  apply clos_rt1n_rt in Hxy; apply clos_rt1n_rt in Hyz.
  apply clos_rt_rt1n.
  now apply rt_trans with y.
Qed.

Lemma acyclic_clos_refl_antisym A (R:relation A) :
  Acyclic R -> antisymmetric _ (clos_refl_trans_1n _ R).
Proof.
  intros acyclic x y Hxy Hyx.
  induction Hxy,Hyx; try easy.
  assert (y=z) as T.
  - apply IHHxy.
    transitivity y0.
    now apply clos_rt1n_step.
    transitivity z0; try easy.
    now apply clos_rt1n_step.
  - destruct T.
    exfalso.
    unfold Acyclic, irreflexive,not in acyclic.
    apply acyclic with (x:=y).
    apply t_trans with (y:=y0); try now apply t_step.
    apply clos_rt_t with (y:=z0).
    + now apply clos_rt1n_rt in Hyx.
    + now apply t_step.
Qed.

Section Synchro.

  Variables (Lbl:Set) (E F:ES Lbl) (X:sig (Configuration E)) (Y:sig (Configuration F)).

  Definition synchro :=
    {x| In _ (proj1_sig X) x} -> {y| In _ (proj1_sig Y) y}.

  Definition is_point (f:synchro) : {x| In _ (proj1_sig X) x} -> {y| In _ (proj1_sig Y) y} -> Prop :=
    fun x y => proj1_sig (f x) = proj1_sig y.

  Definition graph_point (f:synchro) := {'(x,y) | is_point f x y}.

  Definition preserve_lbl (f:synchro) : Prop :=
    forall (p:graph_point f),
      match p with
      | exist _ (x,y) _ => lbl E (proj1_sig x) = lbl F (proj1_sig y) end.

  Definition synchro_ok (f:synchro) :=
    Bijective f /\ preserve_lbl f.

  Definition one_step (f:synchro) : relation (graph_point f) :=
    fun '(exist _ (a,b) _) '(exist _ (a',b') _) =>
      cmp E (proj1_sig a) (proj1_sig a') \/ cmp F (proj1_sig b) (proj1_sig b').

  Definition reachable (f:synchro) := clos_refl_trans_1n _ (@one_step f).

  Lemma reachable_order (f:synchro) : order _ (@reachable f).
  Proof.
    split.
    - apply clos_refl_trans_1n_refl.
    - apply clos_refl_trans_1n_trans.
    - apply acyclic_clos_refl_antisym.
      admit.
  Admitted.

End Synchro.
