Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Constructive_sets.

Require Import Coq.Program.Basics.

Require Import Coq.Classes.EquivDec.

Require Import Causality.Utils.
Require Import Causality.LTS.
Require Import Causality.ES.Definition.

Set Implicit Arguments.

Definition par_rel A B (ra : relation A) (rb : relation B) : relation (A + B) :=
  fun x y =>
    match x,y with
    | inl x, inl y => ra x y
    | inr x, inr y => rb x y
    | _,_ => False end.

Lemma par_order A B (ra : relation A) (ra_o:order A ra) (rb : relation B) (rb_o:order B rb) :
  order (A + B) (par_rel ra rb).
Proof.
  split.
  - intros x; case x; firstorder.
  - intros x y z rxy ryz; case x,y,z; firstorder.
  - intros x y rxy ryx.
    case x,y; simpl in *; try easy; f_equal; firstorder.
Qed.

Lemma par_conflict A B (ra : relation A) (ra_o:conflict A ra) (rb : relation B) (rb_o:conflict B rb) :
  conflict (A + B) (par_rel ra rb).
Proof.
  split.
  - intros x y rxy; case x,y; firstorder.
  - intros x; case x; firstorder.
Qed.

Lemma par_inherit a b
      (ra ca : relation a) (ai : conflict_inherit ra ca) (rb cb : relation b) (bi : conflict_inherit rb cb) :
  conflict_inherit (par_rel ra rb) (par_rel ca cb).
Proof.
  intros x y z h1 h2; case x,y,z; firstorder.
Qed.

(* Parallel composition of two ES *)
Definition par_es Lbl (E:ES Lbl) (F:ES Lbl) :=
  let cmp_order := par_order E.(cmp_ord) F.(cmp_ord) in
  let cfl_conflict := par_conflict E.(cfl_conflict) F.(cfl_conflict) in
  let inherit := par_inherit E.(inherit)  F.(inherit) in
  let lbl := either E.(lbl) F.(lbl) in
  mkES cmp_order cfl_conflict inherit lbl.

Section ParallelCorrect.

  Variables (Lbl: Set) (E F:ES Lbl).

  Lemma union_ens (P : sig (Configuration E) * sig (Configuration F)) : sig (Configuration (par_es E F)).
  Proof.
    split with (x:=either (fun x => In _ (proj1_sig (fst P)) x) (fun y => In _ (proj1_sig (snd P)) y)).
    destruct P as (X,Y).
    destruct X as (X,(dcx,cfx)), Y as (Y,(dcy,cfy)).
    split.
    - intros x ix y c; destruct y,x; simpl in *; firstorder.
    - intros x y ix iy.
      unfold cfl, par_es,par_rel.
      destruct x,y; firstorder.
  Defined.

  Lemma split_ens (X:sig (Configuration (par_es E F))) : sig (Configuration E) * sig (Configuration F).
  Proof.
    split;
      [split with (x:=left_part (proj1_sig X)) | split with (x:=right_part (proj1_sig X)) ];
      destruct X as (X,HX); simpl in *; firstorder.
  Defined.

  Lemma union_split (X:sig (Configuration (par_es E F))) : union_ens (split_ens X) = X.
    apply specif_eq, Extensionality_Ensembles.
    split; intros x; destruct x; intuition.
  Qed.

  Lemma split_union (X : sig (Configuration E) * sig (Configuration F)) : split_ens (union_ens X) = X.
    destruct X as ((X1,HX1),(X2,HX2)).
    unfold split_ens;
      apply f_equal2;
      apply specif_eq, Extensionality_Ensembles;
      split; intuition.
  Qed.

  Lemma par_Configuration X :
    Configuration (par_es E F) X -> Configuration E (left_part X) /\ Configuration F (right_part X).
  Proof. firstorder. Qed.

  Lemma Configuration_either_l X Y e:
    Configuration E (Add _ X e) -> Configuration F Y ->
    Configuration (par_es E F)
                  (Add _ (disjoint_union X Y) (inl e)).
  Proof.
    destruct (add_either X Y) as (HL,HR).
    rewrite HL; intros ce cf.
    split; [intros x hx y| intros x y]; destruct x,y; firstorder.
  Qed.

  Lemma Configuration_either_r X Y e:
    Configuration E X -> Configuration F (Add _ Y e) ->
    Configuration (par_es E F)
                  (Add _ (disjoint_union X Y) (inr e)).
  Proof.
    destruct (add_either X Y) as (HL,HR).
    rewrite HR; intros ce cf.
    split; [intros x hx y| intros x y]; destruct x,y; firstorder.
  Qed.

  Lemma par_sim1 :
    Simulation (par_lts (lts_of_es E) (lts_of_es F)) (lts_of_es (par_es E F))
               (fun x y => y=union_ens x).
  Proof.
    intros p q rpq p' a tpp'.
    exists (union_ens p'); intuition.
    destruct p as ((p1,Hp1),(p2,Hp2)), p' as (p'1,p'2).
    simpl.
    rewrite rpq in *.
    destruct tpp' as [H|H]; destruct H as (H1,(e,He)).
    - exists (inl e); simpl; intuition.
      + apply Extension in H; simpl.
        destruct (add_either p1 p2) as (P1,P2); rewrite P1.
        apply Extensionality_Ensembles; split; rewrite <- H1; intros x ix; destruct x; firstorder.
      + now apply Configuration_either_l.
    - exists (inr e); simpl; intuition.
      + apply Extension in H; simpl.
        destruct (add_either p1 p2) as (P1,P2); rewrite P2.
        apply Extensionality_Ensembles; split; rewrite <- H1; intros x ix; destruct x; firstorder.
      + now apply Configuration_either_r.
  Qed.

  Lemma par_sim2 :
    Simulation (lts_of_es (par_es E F)) (par_lts (lts_of_es E) (lts_of_es F))
               (fun y x => y=union_ens x).
  Proof.
    intros q p rqp q' a tqq'.
    destruct p as (p1,p2).
    exists (split_ens q').
    rewrite union_split.
    destruct tqq' as (e,He).
    split; intuition.
    apply (f_equal split_ens) in rqp; rewrite split_union in rqp.
    injection rqp as eqp'1 eqp'2; destruct eqp'1, eqp'2.
    apply eihter_set in H; destruct H as (Hl,Hr).
    destruct e.
    - left; split; simpl.
      + apply specif_eq; simpl.
        now rewrite wrong_add2 in Hr.
      + exists e; rewrite add_left; intuition; simpl.
        now destruct (par_Configuration H1).
    - right; split; simpl.
      + apply specif_eq; simpl.
        now rewrite wrong_add1 in Hl.
      + exists e; rewrite add_right; intuition; simpl.
        now destruct (par_Configuration H1).
  Qed.

  Theorem par_bisim :
    Bisimilar (par_lts (lts_of_es E) (lts_of_es F)) (lts_of_es (par_es E F)).
  Proof.
    exists (fun x y => y=union_ens x).
    split; try split.
    - apply par_sim1.
    - apply par_sim2.
    - apply specif_eq; simpl.
      apply Extensionality_Ensembles; split; intros x ix; destruct x; apply Noone_in_empty in ix; intuition.
  Qed.

End ParallelCorrect.

Require Import Coq.Logic.Eqdep_dec.

Module ArbitraryParallel(M:DecidableSet).

  Module DEqDep := DecidableEqDepSet(M).

  Import M.

  Definition cast {T : Type} {T1 T2 : T} (H : T1 = T2) (f : T -> Type) (x : f T1) :=
    match H with
    | eq_refl => x end.

  Definition par_arbitrary_rel I (famt : I -> Type) (fam : forall i, relation (famt i)) : relation (sigT famt) :=
    fun '(existT _ i x) '(existT _ j y) =>
      exists H, fam i x (cast H famt y).

  (* This proof requires UIP but in the theorem, we need decidable equality over I,
     so we just require Decidable equality here to get UIP without any axiom *)
  Lemma arbitrary_par_order
        (famt : U -> Type) (fam : forall u:U, relation (famt u)) (famo : forall u, order _ (fam u)) :
    order _ (par_arbitrary_rel fam).
  Proof.
    split.
    - intros (i,x).
      exists (eq_refl i); firstorder.
    - intros (i,x) (j,y) (k,z) (eqij,rxy) (eqjk,ryz).
      destruct eqij,eqjk; simpl in *.
      exists (eq_refl k).
      firstorder.
    - intros (i,x) (j,y) (eqxy,rxy) (eqyx,ry).
      destruct eqyx; simpl in *.
      rewrite (Eqdep.EqdepTheory.UIP_refl _ _ eqxy) in rxy.
      assert (x=y) by firstorder.
      now rewrite H.
  Qed.

  (* This require UIP *)
  Lemma arbitrary_par_conflict
        (famt : U -> Type) (fam : forall u:U, relation (famt u)) (famc : forall u, conflict _ (fam u)) :
    conflict _ (par_arbitrary_rel fam).
  Proof.
    split.
    - intros (i,x) (j,y) (eqij,rxy).
      destruct eqij; exists (eq_refl j); firstorder.
    - intros (i,x) (eqij,rxy).
      rewrite (Eqdep.EqdepTheory.UIP_refl _ _ eqij) in rxy.
      firstorder.
  Qed.

  Lemma arbitrary_par_inherit I
        (famt : I -> Type) (famo famc : forall i:I, relation (famt i))
        (famoo : forall i, order _ (famo i)) (famcc : forall i, conflict _ (famc i))
        (famii: forall i, conflict_inherit (famo i) (famc i))
    :
    conflict_inherit (par_arbitrary_rel famo) (par_arbitrary_rel famc).
  Proof.
    intros (i,x) (j,y) (k,z) (eqij,rxy) (eqjk,ryz).
    destruct eqij, eqjk.
    exists (eq_refl k); firstorder.
  Qed.

  Definition arbitrary_par_es (Lbl:Set) (Family: U -> ES Lbl) : ES Lbl :=
    let famo i := cmp_ord (Family i) in
    let famc i := cfl_conflict (Family i) in
    let fami i := inherit (Family i) in
    let cmp_order := arbitrary_par_order _ _ famo in
    let cfl_conflict := arbitrary_par_conflict _ _ famc in
    let inherit := arbitrary_par_inherit _ _ famo famc fami in
    let lbl := fun '(existT _ i x) => lbl (Family i) x in
    mkES cmp_order cfl_conflict inherit lbl.

  Section WithFamily.
    Variables (Lbl:Set) (Family : U -> ES Lbl).

    Definition union_arbitrary_ens (X:forall u:U, sig (Configuration (Family u))) :
      sig (Configuration (arbitrary_par_es Family)).
    Proof.
      split with (x:=fun '(existT _ i x) => In _ (proj1_sig (X i)) x).
      split.
      - intros (i,x) ix (j,y) (H,cxy).
        destruct H.
        unfold In in *.
        destruct (X i) as (Xi,HXi); simpl in *.
        firstorder.
      - intros (i,x) (j,y) ix iy (H,cxy).
        destruct H.
        unfold In in *.
        destruct (X j) as (Xi,HXi); simpl in *.
        firstorder.
    Defined.

    Definition split_arbitrary_ens (X:sig (Configuration (arbitrary_par_es Family))) :
      forall u:U, sig (Configuration (Family u)).
    Proof.
      intro u.
      split with (x:=fun (x:Event (Family u)) => In _ (proj1_sig X) ((existT _ u x)) ).
      destruct X as (X,(D,C)).
      split.
      - intros x ix y cxy.
        simpl in *.
        unfold downclosed in D.
        specialize D with
            (existT (fun u => Event (Family u)) u x) (existT (fun u => Event (Family u)) u y).
        apply D; intuition.
        exists (eq_refl u); intuition.
      - intros x y ix iy cxy.
        simpl in *.
        unfold conflict_free in C.
        specialize C with
            (existT (fun u => Event (Family u)) u x) (existT (fun u => Event (Family u)) u y).
        apply C; intuition.
        exists (eq_refl u); intuition.
    Defined.

    Lemma union_split_arbitrary (X:sig (Configuration (arbitrary_par_es Family))) :
      union_arbitrary_ens (split_arbitrary_ens X) = X.
    Proof.
      destruct X as (X,HX).
      apply specif_eq; simpl; apply Extensionality_Ensembles.
      split; intros (i,x) ix; unfold In in *; intuition.
    Qed.

     Lemma split_union_arbitrary (X:forall u:U, sig (Configuration (Family u))) u :
      split_arbitrary_ens (union_arbitrary_ens X) u = X u.
    Proof.
      apply specif_eq; simpl; apply Extensionality_Ensembles;
        split; intros x ix; unfold In in *; intuition.
    Qed.

    Lemma config_sim1 p i e:
          Configuration (Family i) (Add _ (proj1_sig (p i)) e) ->
          Configuration (arbitrary_par_es Family)
                        (Add _ (proj1_sig (union_arbitrary_ens p))
                             (existT (fun i0 : U => Event (Family i0)) i e)).
    Proof.
      intros H3.
      destruct (proj2_sig (union_arbitrary_ens p)) as (DP,CP).
      destruct H3 as (D,C).
      split.
      + intros x ix z cxz.
        apply Add_inv in ix.
        unfold downclosed in *.
        destruct ix.
        * specialize DP with x z.
          apply Add_intro1,DP; intuition.
        * destruct x as (j,x), z as (k,z), cxz as (E,cxz); destruct E.
          generalize H; intro H'.
          apply projT1_eq in H; simpl in H; destruct H; apply DEqDep.inj_pairT2 in H'.
          unfold downclosed in D.
          specialize D with x z.
          rewrite H' in *.
          assert (In (Event (Family i)) (Add (Event (Family i)) (proj1_sig (p i)) x) z) by intuition.
          apply Add_inv in H; destruct H.
          -- apply Add_intro1; intuition.
          -- rewrite H; intuition.
      + intros x y ix iy cxy.
        unfold conflict_free in *.
        apply Add_inv in ix; apply Add_inv in iy.
        destruct ix as [HX|HX],iy as [HY|HY].
        1: specialize CP with x y; now apply CP.
        all:destruct x as (j,x), y as (k,y), cxy as (E,cxy); destruct E.
        2-3: generalize HX; intros HX';
          apply projT1_eq in HX; simpl in HX; destruct HX; apply DEqDep.inj_pairT2 in HX';
            rewrite HX' in *.
        1,3: generalize HY; intros HY';
          apply projT1_eq in HY; simpl in HY; destruct HY; apply DEqDep.inj_pairT2 in HY';
            rewrite HY' in *.
        all:specialize C with x y; apply C; intuition;
          rewrite HY'; intuition.
    Qed.

    (* This need decidable equality over I *)
    Lemma par_arbitrary_sim1 :
      Simulation (par_arbitrary_lts (compose (@lts_of_es Lbl) Family)) (lts_of_es (arbitrary_par_es Family))
                 (fun x y => y=union_arbitrary_ens x).
    Proof.
      intros p q rpq p' a tpp'.
      exists (union_arbitrary_ens p'); intuition.
      destruct tpp' as (i,((H1,(H2,(H3,H4))),H5)).
      exists (existT _ i H1); rewrite rpq; intuition.
      - apply Extensionality_Ensembles; simpl; split; intros (j,Ej) jx; unfold In in jx.
        + destruct (eq_dec i j).
          * destruct e.
            rewrite H2 in jx.
            apply Add_inv in jx.
            destruct jx; intuition.
            rewrite H4; intuition.
          * apply Add_intro1.
            apply H5 in n.
            rewrite <- n in jx; intuition.
        + apply Add_inv in jx.
          destruct (eq_dec i j).
          * destruct e.
            destruct jx; unfold In; rewrite H2.
            -- apply Add_intro1; intuition.
            -- apply DEqDep.inj_pair2 in H4.
               rewrite H4; now apply Add_intro2.
          * generalize n; intros n'.
            apply H5 in n; unfold In; rewrite <- n; intuition.
            apply projT1_eq in H4; intuition.
      - now apply config_sim1.
    Qed.

    Definition EventsOf i := Event (Family i).

    Lemma config_sim2 p i e :
      Configuration (arbitrary_par_es Family)
                    (Add _ (proj1_sig p) (existT EventsOf i e))
      -> Configuration (Family i) (Add _ (proj1_sig (split_arbitrary_ens p i)) e).
    Proof.
      intros H2.
      destruct H2 as (D,C).
      destruct (proj2_sig (split_arbitrary_ens p i)) as (DP,CP).
      split.
      - intros x ix y cxy.
        apply Add_inv in ix.
        destruct ix.
        + now apply Add_intro1,DP with x.
        + rewrite H in *.
           pose (x' := (existT EventsOf i x)).
           pose (y' := (existT EventsOf i y)).
           assert (In _ (Add _ (proj1_sig p) (existT EventsOf i x)) y').
           * unfold downclosed in D; apply D with x'; intuition.
              exists (eq_refl i); intuition.
           * apply Add_inv in H0.
              destruct H0; intuition.
              apply DEqDep.inj_pairT2 in H0; rewrite H0; intuition.
     - intros x y ix iy cxy.
        apply Add_inv in ix; apply Add_inv in iy.
        pose (x' := (existT EventsOf i x)).
        pose (y' := (existT EventsOf i y)).
        unfold conflict_free,not in C.
        destruct ix,iy.
        1:now apply CP with x y.
        1:rewrite H0 in *.
        2:rewrite H in *.
        1-2:apply C with x' y'; intuition;
          exists (eq_refl i); intuition.
        rewrite H0 in *.
        apply C with x' y'; intuition.
        rewrite H; intuition.
        exists (eq_refl i); intuition.
    Qed.

    Lemma par_arbitrary_sim2 :
      Simulation (lts_of_es (arbitrary_par_es Family)) (par_arbitrary_lts (compose (@lts_of_es Lbl) Family))
                 (fun y x => y=union_arbitrary_ens x).
    Proof.
      intros p q rpq p' a tpp'.
      exists (split_arbitrary_ens p').
      rewrite union_split_arbitrary; intuition.
      simpl in *.
      destruct tpp' as ((i,e),(H1,(H2,(H3,H4)))).
      exists i; intuition.
      - assert (q i = split_arbitrary_ens p i) by now rewrite rpq, split_union_arbitrary.
        rewrite H in *.
        unfold In in *.
        exists e; intuition.
        + apply Extensionality_Ensembles; simpl; split; intros x ix.
          * unfold In in ix.
            rewrite H1 in ix.
            apply Add_inv in ix.
            destruct ix; intuition.
            apply DEqDep.inj_pairT2 in H0; rewrite H0; intuition.
          * unfold In; rewrite H1.
            apply Add_inv in ix.
            destruct ix; intuition.
            -- apply Add_intro1; intuition.
            -- rewrite H0;apply Add_intro2.
        + now apply config_sim2.
      - apply specif_eq.
        apply (f_equal split_arbitrary_ens) in rpq.
        assert (q j = split_arbitrary_ens p j) by now rewrite rpq, split_union_arbitrary.
        rewrite H0;simpl;rewrite H1.
        apply Extensionality_Ensembles; split; intros x ix.
        + apply Add_intro1; intuition.
        + apply Add_inv in ix.
          destruct ix; try apply projT1_eq in H5; intuition.
    Qed.

    Lemma empty_union_arbitrary :
      empty (arbitrary_par_es Family) = union_arbitrary_ens (fun u : U => empty (Family u)).
    Proof.
      apply specif_eq, Extensionality_Ensembles; simpl.
      split; [intros i ix | intros (H,i) ix]; now apply Noone_in_empty in ix.
    Qed.

    Theorem par_arbitrary_bisim :
      Bisimilar (par_arbitrary_lts (compose (@lts_of_es Lbl) Family)) (lts_of_es (arbitrary_par_es Family)).
    Proof.
      exists (fun x y => y = union_arbitrary_ens x).
      split; try split.
      - apply par_arbitrary_sim1.
      - apply par_arbitrary_sim2.
      - apply empty_union_arbitrary.
    Qed.

  End WithFamily.

End ArbitraryParallel.
