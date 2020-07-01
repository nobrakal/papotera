Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Constructive_sets.

Require Import Coq.Program.Basics.

Require Import Coq.Logic.Eqdep_dec.

Require Import Causality.Utils.
Require Import Causality.LTS.
Require Import Causality.ES.Definition.
Require Import Causality.ES.Parallel.

Set Implicit Arguments.

Module ArbitrarySum(M:DecidableSet).

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
    split; [intros (i,x) (j,y) cxy | intros (i,x)]; firstorder.
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
      now apply (Par.par_arbitrary_inherit famo famc famoo famcc famii) with (x:=x) (y:=y) (z:=z).
    - right.
      destruct x as (i,x),y as (j,y), z as (k,z), pyz as (E,pyz), E.
      intuition.
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
            (X : sigT (StateOf (compose (@lts_of_es Lbl) Family))) :
      sig (Configuration (sum_arbitrary_es Family)) :=
      match X with
      | existT _ i X =>
        exist
          _
          (fun '(existT _ j y) =>
             exists (H:j=i), proj1_sig X (cast H (fun i => Event (Family i)) y)) _ end.

    Next Obligation.
      destruct X as (X,H); simpl in *.
      split; [intros (j,x) (E,ix) (k,y) (E',cxy)| intros (j,x) (k,y) (E,ix) (E',iy) cxy]; destruct E,E'.
      - unfold In in *; simpl in *.
        exists (eq_refl j); firstorder.
      - destruct cxy; simpl in *.
        + destruct H0 as (E,H0).
          rewrite (Eqdep.EqdepTheory.UIP_refl _ _ E) in H0; simpl in *.
          destruct H as (D,C).
          apply C with (x:=x)(y:=y); intuition.
        + congruence.
    Defined.

    Definition EventOf i := Event (Family i).

    Lemma sigT_eq (z k : U) (e:Event (Family z)) (y:Event(Family k)):
      existT EventOf z e = existT EventOf k y ->
      exists (H:k = z), e = cast H EventOf y.
    Proof.
      intros H.
      generalize H; intros H'.
      apply projT1_eq in H; simpl in H.
      symmetry in H; exists H.
      destruct H; now apply DEqDep.inj_pairT2 in H'.
    Qed.

    Definition therel
      (x : option (sigT (StateOf (compose (@lts_of_es Lbl) Family))))
      (y : sig (Configuration (sum_arbitrary_es Family))) :=
      maybe (proj1_sig y=Empty_set _)
            (fun x => Inhabited _ (proj1_sig (projT2 x)) /\ y = select_arbitrary_ens x)
            x.

    Lemma config_sim_1 j (p:StateOf (compose (@lts_of_es Lbl) Family) j) e :
      Configuration _ (Add _ (proj1_sig p) e) ->
      Configuration
        _ (Add _
               (proj1_sig
                  (select_arbitrary_ens
                     (existT (StateOf (compose (@lts_of_es Lbl) Family)) j p)))
               (existT EventOf j e)).
    Proof.
      intros (D,C).
      split.
      - intros (i,x) ix (z,y) (H,cxy).
        destruct H.
        apply Add_inv in ix; destruct ix.
        + simpl in H; unfold In in H.
          destruct H as (H1,H),H1; simpl in *.
          assert (In _ (Add _ (proj1_sig p) e) y) as A by (apply D with (x:=x) (y:=y); intuition).
          apply Add_inv in A; destruct A.
          * apply Add_intro1; exists (eq_refl i); intuition.
          * rewrite H0; apply Add_intro2.
        + destruct (sigT_eq H) as (H1,H2),H1.
          assert (In _ (Add _ (proj1_sig p) e) y) as A
              by (apply D with (x:=x) (y:=y); intuition; rewrite H2; intuition).
          apply Add_inv in A; destruct A.
          * apply Add_intro1; exists (eq_refl i); intuition.
          * rewrite H0; apply Add_intro2; intuition.
      - intros (z,x) (k,y) ix iy cxy.
        apply Add_inv in ix.
        apply Add_inv in iy.
        destruct ix as [(Ex,Hx)|Hx],iy as [(Ey,Hy)|Hy].
        1,2: destruct Ex.
        1,3: destruct Ey.
        3,4: destruct (sigT_eq Hy) as (Ey1,Ey2), Ey1; simpl in Ey2.
        2,4: destruct (sigT_eq Hx) as (Ex1,Ex2), Ex1; simpl in Ex2.
        1,2,3,4: destruct cxy as [(E,H)|H]; try congruence;
          rewrite (Eqdep.EqdepTheory.UIP_refl _ _ E) in H.
        + apply C with x y; intuition.
        + apply C with x y; intuition; rewrite Ex2; intuition.
        + rewrite <- Ex2, <- Ey2 in H.
          destruct (sum_arbitrary_conflict _ _ (fun i => cfl_conflict (Family i))) as (S,I).
          unfold irreflexive in I.
          specialize I with ((existT EventOf z e)).
          apply I; left; exists (eq_refl z); easy.
        + apply C with x y; intuition; rewrite Ey2; intuition.
    Qed.

    Lemma sum_arbitrary_sim1 :
      Simulation
        (sum_arbitrary_lts (compose (lts_of_es (Lbl:=Lbl)) Family))
        (lts_of_es (sum_arbitrary_es Family))
        therel.
    Proof.
      intros p q rpq p' a tpp'.
      destruct p as [p|],p' as [p'|]; intuition; exists (select_arbitrary_ens p'); simpl; intuition.
      1,2: destruct p as (i,p), p' as (j,p'), rpq as (IH,rpq), tpp' as (E,(e,(H2,(H3,(H4,H5))))),E.
      3,4:destruct p' as (j,p'), tpp' as (e,(H2,(H3,(H4,H5)))).
      all:simpl in H2; simpl; rewrite H2.
      2,4:apply Inhabited_add.
      - rewrite rpq.
        exists (existT _ j e); intuition.
        + apply Extensionality_Ensembles; split; intros (i,x) ix; unfold In in *.
          * destruct ix as (E,ix).
            destruct E; simpl in *.
            apply Add_inv in ix; destruct ix.
            -- apply Add_intro1; unfold In; exists (eq_refl i); intuition.
            -- rewrite H; apply Add_intro2.
          * apply Add_inv in ix; unfold In in ix; destruct ix.
            -- destruct H as (E,H); destruct E; exists (eq_refl i); apply Add_intro1; intuition.
            -- destruct (sigT_eq H) as (E1,E2); destruct E1.
               rewrite E2; exists (eq_refl i); apply Add_intro2.
        + now apply config_sim_1.
        + unfold In in H; simpl in H.
          destruct H as (E,H).
          rewrite (Eqdep.EqdepTheory.UIP_refl _ _ E) in H; simpl in *.
          firstorder.
      - exists (existT _ j e); try rewrite rpq; repeat rewrite Add_empty in *; intuition.
        + apply Extensionality_Ensembles; split; intros (i,x) ix; unfold In in *.
          * destruct ix as (E,H); destruct E.
            apply Singleton_inv in H.
            simpl in H; now rewrite H.
          * apply Singleton_inv in ix.
            destruct (sigT_eq ix) as (E1,E2); destruct E1.
            exists (eq_refl i); simpl; rewrite E2; apply In_singleton.
        + destruct H3 as (D,C).
          split.
          * intros (z,x) ix (k,y) (E,cxy).
            destruct E.
            apply Singleton_inv in ix.
            destruct (sigT_eq ix) as (E1,E2),E1.
            unfold downclosed in D; specialize D with x y.
            apply Singleton_intro.
            assert (e=y) as H by (apply Singleton_inv,D; intuition).
            now rewrite H.
          * intros (z,x) (k,y) ix iy H.
            apply Singleton_inv in ix.
            apply Singleton_inv in iy.
            destruct (sigT_eq ix) as (E1x,E2x); destruct E1x.
            destruct (sigT_eq iy) as (E1y,E2y); destruct E1y.
            simpl in E2x, E2y; rewrite <- E2x, <- E2y in H.
            destruct (sum_arbitrary_conflict _ _ (fun i => cfl_conflict (Family i))) as (S,I).
            unfold irreflexive in I.
            specialize I with (existT EventOf k e).
            intuition.
        + now apply Noone_in_empty in H.
    Qed.

    Program Definition unselect_arbitrary_ens
            (X : sig (Configuration (sum_arbitrary_es Family))) :
      forall i:U, StateOf (compose (@lts_of_es Lbl) Family) i :=
      fun i => exist _ (fun x => In _ (proj1_sig X) (existT _ i x)) _.

    Next Obligation.
      destruct H as (D,C).
      split.
      - intros x ix y cxy.
        apply D with (x:=existT EventOf i x) (y:=existT EventOf i y); intuition.
        exists (eq_refl i); intuition.
      - intros x y ix iy cxy.
        apply C with (x:=existT EventOf i x) (y:=existT EventOf i y); intuition.
        left.
        exists (eq_refl i); intuition.
    Defined.

    Lemma config_sim2 i e (p:sig (Configuration (sum_arbitrary_es Family))) (q:StateOf (compose (lts_of_es (Lbl:=Lbl)) Family) i) :
      proj1_sig p =
      proj1_sig (select_arbitrary_ens (existT (StateOf (compose (lts_of_es (Lbl:=Lbl)) Family)) i q))
      -> Configuration (sum_arbitrary_es Family)
                       (Add {i : U & Event (Family i)} (proj1_sig p)
                            (existT (fun i : U => Event (Family i)) i e))
      -> Configuration (Family i) (Add (Event (Family i)) (proj1_sig q) e).
    Proof.
      intros rpq (D,C).
      split.
      - intros x ix y cxy.
        assert (In _ (Add _ (proj1_sig p) (existT _ i e)) (existT EventOf i y)) as P.
        + apply Add_inv in ix; destruct ix; apply D with (x:= existT EventOf i x) (y:= existT EventOf i y).
          1:apply Add_intro1; rewrite rpq; exists (eq_refl i); easy.
          2:rewrite rpq,H; apply Add_intro2.
          all: exists (eq_refl i); easy.
        + apply Add_inv in P; destruct P.
          * rewrite rpq in H; destruct H as (E,H0).
            rewrite (Eqdep.EqdepTheory.UIP_refl _ _ E) in H0; now apply Add_intro1.
          * apply DEqDep.inj_pairT2 in H.
            rewrite H; apply Add_intro2.
      -  intros x y ix iy cxy.
         apply Add_inv in ix.
         apply Add_inv in iy.
         destruct ix as [H0|H0],iy as [H1|H1];
           apply C with (x:= existT EventOf i x) (y:= existT EventOf i y); try rewrite rpq.
         1,2,4,8: apply Add_intro1; exists (eq_refl i); easy.
         1,3,5:left; exists (eq_refl i); easy.
         1:rewrite H1; apply Add_intro2.
         1,2:rewrite H0; apply Add_intro2.
         all:
           rewrite <- H0, <- H1 in cxy;
           destruct (cfl_conflict (Family i));
           unfold irreflexive in conflict_irfl;
           specialize conflict_irfl with e; congruence.
    Qed.

    Lemma sum_arbitrary_sim2 :
      Simulation
        (lts_of_es (sum_arbitrary_es Family))
        (sum_arbitrary_lts (compose (lts_of_es (Lbl:=Lbl)) Family))
        (fun y x => therel x y).
    Proof.
      intros p q rpq p' a tpp'.
      simpl in *.
      destruct tpp' as ((i,e),(H1,(H2,(H3,H4)))).
      exists (Some (existT _ i (unselect_arbitrary_ens p' i))).
      destruct q as [(j,q)|].
      - destruct rpq as (IH,rpq).
        apply proj1_sig_eq in rpq.
        generalize rpq; intros rpq'; apply Extension in rpq'; destruct rpq' as (R1,R2).
        assert (i=j) as H.
        + destruct IH as (x,Hx).
          destruct p' as (p',(Dp',Cp')); simpl in *.
          destruct (eq_dec i j); try easy.
          exfalso.
          apply Cp' with (x:=existT EventOf j x) (y:=existT EventOf i e); try rewrite H1.
          * apply Add_intro1,R2.
            exists (eq_refl j); easy.
          * apply Add_intro2.
          * right; simpl; intuition.
        + split.
          * exists H; destruct H; exists e; intuition.
            -- simpl.
               apply Extensionality_Ensembles; split; intros x ix.
               ++ rewrite H1 in ix.
                  apply Add_inv in ix; destruct ix.
                  ** apply R1 in H; destruct H as (E,H).
                     rewrite (Eqdep.EqdepTheory.UIP_refl _ _ E) in H.
                     now apply Add_intro1.
                  ** apply  DEqDep.inj_pairT2 in H.
                     rewrite H; apply Add_intro2.
               ++ rewrite H1.
                  apply Add_inv in ix; destruct ix.
                  ** apply Add_intro1, R2.
                     exists (eq_refl i); easy.
                  ** rewrite H; apply Add_intro2.
            -- now apply config_sim2 with p.
            -- apply H3,R2.
               exists (eq_refl i); intuition.
          * destruct H; split.
            -- apply Inhabited_intro with (x:=e).
               apply Extension in H1; destruct H1 as (H11,H12); apply H12, Add_intro2.
            -- apply specif_eq. simpl. repeat rewrite H1.
               apply Extensionality_Ensembles; split; intros (j,x) ix.
               ++ apply Add_inv in ix; destruct ix.
                  ** apply R1 in H.
                     destruct H as (E,H).
                     exists E; destruct E; apply Add_intro1, R2; exists (eq_refl j); easy.
                  ** destruct (sigT_eq H) as (E1,E2),E1.
                     rewrite E2.
                     exists (eq_refl j); apply Add_intro2.
               ++ destruct ix as (E,ix),E; intuition.
      - simpl in rpq.
        split.
        + exists e; intuition; simpl.
          * rewrite H1,rpq.
            repeat rewrite Add_empty.
            apply Extensionality_Ensembles; split; intros x ix; apply Singleton_inv in ix;
              [apply DEqDep.inj_pairT2 in ix|]; now rewrite ix.
          * rewrite Add_empty.
            rewrite rpq,Add_empty in H2.
            destruct H2 as (D,C).
            split.
            -- intros x ix y cxy.
               apply Singleton_inv in ix.
               assert (In _ (Singleton _ (existT EventOf i e)) (existT EventOf i y)) as H.
               ++ apply D with (x:=existT EventOf i x) (y:=existT EventOf i y); intuition.
                  now rewrite ix.
                  exists (eq_refl i); intuition.
               ++ apply Singleton_inv in H.
                  apply DEqDep.inj_pairT2 in H; now rewrite H.
            -- intros x y ix iy cxy.
               destruct (sum_arbitrary_conflict _ _ (fun i => cfl_conflict (Family i))) as (S,I).
               apply I with (x:= existT EventOf i e).
               apply Singleton_inv in ix.
               apply Singleton_inv in iy.
               rewrite <- ix, <- iy in cxy.
               left; exists (eq_refl i); intuition.
          * now apply Noone_in_empty in H.
        + split.
          * apply Inhabited_intro with (x:=e).
            apply Extension in H1; destruct H1 as (H11,H12); apply H12, Add_intro2.
          * apply specif_eq, Extensionality_Ensembles; simpl.
            rewrite H1,rpq,Add_empty.
            split; intros (z,x) ix.
            -- apply Singleton_inv in ix.
               generalize ix; intros ix'.
               apply projT1_eq in ix; simpl in ix.
               symmetry in ix; exists ix.
               destruct ix; apply DEqDep.inj_pairT2 in ix'.
               rewrite ix'; intuition.
            -- destruct ix as (E,ix).
               destruct E; intuition.
    Qed.

    Theorem sum_arbitrary_ok :
      Bisimilar (sum_arbitrary_lts (compose (@lts_of_es Lbl) Family)) (lts_of_es (sum_arbitrary_es Family)).
    Proof.
      exists therel.
      split; try split.
      - apply sum_arbitrary_sim1.
      - apply sum_arbitrary_sim2.
      - simpl; intuition.
    Qed.

  End WithFamily.
End ArbitrarySum.
