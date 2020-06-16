Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Constructive_sets.

Require Import Coq.Program.Basics.

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
    union_rel (par_arbitrary_rel fam) (orth_arbitrary_rel fam).

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
    conflict_inherit (par_arbitrary_rel famo) (sum_arbitrary_rel famc).
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

  Definition sum_arbitrary_es (Lbl:Set) (Family: U -> ES Lbl) : ES Lbl :=
    let famo i := cmp_ord (Family i) in
    let famc i := cfl_conflict (Family i) in
    let fami i := inherit (Family i) in
    let cmp_order := Par.par_arbitrary_order _ _ famo in
    let cfl_conflict := sum_arbitrary_conflict _ _ famc in
    let inherit := sum_arbitrary_inherit _ famo famc fami in
    let lbl := fun '(existT _ i x) => lbl (Family i) x in
    mkES cmp_order cfl_conflict inherit lbl.

  Section WithFamily.
    Variables (Lbl:Set) (Family : U -> ES Lbl).

    Program Definition select_arbitrary_ens
            (X : option (sigT (StateOf (compose (@lts_of_es Lbl) Family)))) :
      sig (Configuration (sum_arbitrary_es Family)) :=
      match X with
      | None => empty _
      | Some (existT _ i X) =>
        exist
          _
          (fun '(existT _ j y) =>
             exists (H:j=i), proj1_sig X (cast H (fun i => Event (Family i)) y)) _ end.

    Next Obligation.
      destruct X as (X,H); simpl in *.
      split.
      - intros (j,x) (E,ix) (k,y) (E',cxy); destruct E,E'; unfold In in *; simpl in *.
        exists (eq_refl j); firstorder.
      - intros (j,x) (k,y) (E,ix) (E',iy) cxy.
        destruct E,E'.
        destruct cxy; simpl in *.
        + destruct H0 as (E,H0).
          rewrite (Eqdep.EqdepTheory.UIP_refl _ _ E) in H0; simpl in *.
          destruct H as (D,C).
          apply C with (x:=x)(y:=y); intuition.
        + congruence.
    Defined.

    Lemma sum_arbitrary_sim1 :
      Simulation
        (sum_arbitrary_lts (compose (lts_of_es (Lbl:=Lbl)) Family))
        (lts_of_es (sum_arbitrary_es Family))
        (fun x y => y = select_arbitrary_ens x).
    Proof.
      intros p q rpq p' a tpp'.
      exists (select_arbitrary_ens p'); intuition.
      rewrite rpq.
      destruct p as [(i,p)|],p' as [(j,p')|]; intuition.
      - destruct tpp' as (E,(e,(H2,(H3,(H4,H5))))).
        destruct E.
        exists (existT _ j e); intuition.
        + simpl; simpl in H2; rewrite H2.
          apply Extensionality_Ensembles; split; intros (i,x) ix; unfold In in *.
          * destruct ix as (E,ix).
            destruct E; simpl in *.
            apply Add_inv in ix; destruct ix.
            -- apply Add_intro1; unfold In; exists (eq_refl i); intuition.
            -- rewrite H; apply Add_intro2.
          * apply Add_inv in ix; unfold In in ix; destruct ix.
            -- destruct H as (E,H); destruct E; exists (eq_refl i); apply Add_intro1; intuition.
            -- generalize H; intros H'.
               apply projT1_eq in H; simpl in H; destruct H; apply DEqDep.inj_pairT2 in H'.
               rewrite H'; exists (eq_refl j); apply Add_intro2.
        + admit.
        + unfold In in H; simpl in H.
          destruct H as (E,H).
          rewrite (Eqdep.EqdepTheory.UIP_refl _ _ E) in H; simpl in *.
          firstorder.
      - destruct tpp' as (e,(H2,(H3,(H4,H5)))).
        exists (existT _ j e); intuition.
        + simpl in H2; simpl; rewrite H2.
          apply Extensionality_Ensembles; split; intros (i,x) ix; unfold In in *.
          * destruct ix as (E,H); destruct E.
            apply Add_inv in H; destruct H.
            -- now apply Noone_in_empty in H.
            -- rewrite H; apply Add_intro2.
          * apply Add_inv in ix; destruct ix.
            -- now apply Noone_in_empty in H.
            -- generalize H; intros H'.
               apply projT1_eq in H; simpl in H; destruct H; apply DEqDep.inj_pairT2 in H'.
               rewrite H'; exists (eq_refl j); apply Add_intro2.
        + admit.
        + now apply Noone_in_empty in H.
    Admitted.

    Lemma sum_arbitrary_sim2 :
      Simulation
        (lts_of_es (sum_arbitrary_es Family))
        (sum_arbitrary_lts (compose (lts_of_es (Lbl:=Lbl)) Family))
        (fun y x => y = select_arbitrary_ens x).
    Proof.
    Admitted.

    Theorem sum_arbitrary_bisim :
      Bisimilar (sum_arbitrary_lts (compose (@lts_of_es Lbl) Family)) (lts_of_es (sum_arbitrary_es Family)).
    Proof.
      exists (fun x y => y = select_arbitrary_ens x).
      split; try split.
      - apply sum_arbitrary_sim1.
      - apply sum_arbitrary_sim2.
      - intuition.
    Qed.

  End WithFamily.
End ArbitraryParallel.
