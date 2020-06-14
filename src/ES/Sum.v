Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Constructive_sets.

Require Import Coq.Logic.Eqdep_dec.

Require Import Causality.Utils.
Require Import Causality.LTS.
Require Import Causality.ES.Definition.
Require Import Causality.ES.Parallel.

Set Implicit Arguments.

Module ArbitraryParallel(M:DecidableSet).

  Module DEqDep := DecidableEqDepSet(M).
  Module Par := Parallel.ArbitraryParallel(M).

  Import M.

  Definition orth_arbitrary_rel I (famt : I -> Type) (fam : forall i, relation (famt i))
    : relation (sigT famt) :=
    fun '(existT _ i x) '(existT _ j y) => i <> j.

  Lemma orth_arbitrary_conflict (famt : U -> Type) (fam : forall u:U, relation (famt u))
        (famc : forall u, conflict _ (fam u))
    : conflict _ (orth_arbitrary_rel fam).
  Proof.
    split.
    - intros (i,x) (j,y) cxy; now apply not_eq_sym.
    - intros (i,x); intuition.
  Qed.

  Definition sum_arbitrary_rel I (famt : I -> Type) (fam : forall i, relation (famt i))
    : relation (sigT famt) :=
    union_rel (Par.par_arbitrary_rel fam) (orth_arbitrary_rel fam).

  Lemma sum_arbitrary_conflict (famt : U -> Type) (fam : forall u:U, relation (famt u))
        (famc : forall u, conflict _ (fam u))
    : conflict _ (sum_arbitrary_rel fam).
  Proof.
    apply conflict_union; [now apply Par.par_arbitrary_conflict | now apply orth_arbitrary_conflict].
  Qed.

  Lemma sum_arbitrary_inherit I
        (famt : I -> Type) (famo famc : forall i:I, relation (famt i))
        (famoo : forall i, order _ (famo i)) (famcc : forall i, conflict _ (famc i))
        (famii: forall i, conflict_inherit (famo i) (famc i))
    :
    conflict_inherit (Par.par_arbitrary_rel famo) (sum_arbitrary_rel famc).
  Proof.
    intros x y z sxy pyz.
    destruct sxy.
    - left.
      pose (E:=Par.par_arbitrary_inherit famo famc famoo famcc famii).
      unfold conflict_inherit in E; specialize E with x y z.
      now apply E.
    - right.
      destruct x as (i,x),y as (j,y), z as (k,z), pyz as (E,pyz).
      destruct E; intuition.
      Qed.

  Definition arbitrary_sum_es (Lbl:Set) (Family: U -> ES Lbl) : ES Lbl :=
    let famo i := cmp_ord (Family i) in
    let famc i := cfl_conflict (Family i) in
    let fami i := inherit (Family i) in
    let cmp_order := Par.par_arbitrary_order _ _ famo in
    let cfl_conflict := sum_arbitrary_conflict _ _ famc in
    let inherit := sum_arbitrary_inherit _ famo famc fami in
    let lbl := fun '(existT _ i x) => lbl (Family i) x in
    mkES cmp_order cfl_conflict inherit lbl.

End ArbitraryParallel.
