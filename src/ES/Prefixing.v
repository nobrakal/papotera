Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Constructive_sets.

Require Import Causality.Utils.
Require Import Causality.LTS.
Require Import Causality.ES.Definition.

Set Implicit Arguments.

Definition lift_rel A (R:relation A) : relation (option A) :=
  maybe (fun _ => False) (fun x => maybe False (R x)).

Lemma lift_rel_cfl A (R:relation A) (cR : conflict _ R) : conflict _ (lift_rel R).
Proof.
  split.
  - intros x y; destruct x,y; firstorder.
  - intros x; destruct x; firstorder.
Qed.

Definition prefix_opt A (R:relation A) : relation (option A) :=
  maybe (fun _ => True) (fun x => maybe False (R x)).

Lemma prefix_opt_order A (R:relation A) (or :order _ R) : order _ (prefix_opt R).
Proof.
  unfold prefix_opt,maybe.
  split.
  - intros x; destruct x; firstorder.
  - intros x y z; destruct x,y,z; firstorder.
  - intros x y rxy ryx. destruct x,y; firstorder.
    assert (a=a0) by firstorder.
    now rewrite H.
Qed.

Lemma prefix_opt_inherit a (ra rb : relation a) (ai : conflict_inherit ra rb) :
  conflict_inherit (prefix_opt ra) (lift_rel rb).
Proof.
  intros x y z cxy ryz; destruct x,y,z; firstorder.
Qed.

(* Prefixing for ES *)
Definition prefixing_es Lbl (E:ES Lbl) (a:Lbl) : ES Lbl :=
  let cmp := prefix_opt E.(cmp) in
  let cmp_order := prefix_opt_order E.(cmp_ord) in
  let cfl := lift_rel E.(cfl) in
  let cfl_conflict := lift_rel_cfl E.(cfl_conflict) in
  let inherit := prefix_opt_inherit E.(inherit) in
  let lbl := maybe a E.(lbl) in
  mkES cmp_order cfl_conflict inherit lbl.

Section PrefixingCorrect.

  Variables (Lbl: Set) (E:ES Lbl) (a:Lbl).

  Definition add_none_sig (X:sig (Configuration E)) : sig (Configuration (prefixing_es E a)).
    split with (x:=add_none (proj1_sig X)).
    split; [intros y iy z | intros y z iy];
      destruct X,y,z; unfold In,maybe in *; simpl in *; firstorder.
  Defined.

  Definition remove_none_sig (X:sig (Configuration (prefixing_es E a))) : sig (Configuration E).
    split with (x:=ens_of_opt (proj1_sig X)).
    destruct X as (X,HX).
    split; [intros y iy z | intros y z iy];
      unfold In,maybe in *; simpl in *; firstorder.
  Defined.

  Lemma remove_add_none (X:sig (Configuration E)) : remove_none_sig (add_none_sig X) = X.
  Proof. now apply specif_eq. Qed.

  Lemma add_remove_none (X:sig (Configuration (prefixing_es E a))) (H:Inhabited _ (proj1_sig X)) :
    add_none_sig (remove_none_sig X) = X.
  Proof.
    apply specif_eq, Extensionality_Ensembles; simpl.
    split; intros x ix; destruct x; unfold In in *; simpl in *; intuition.
    destruct X as (X,(HX1,HX2)); simpl in *.
    destruct H.
    unfold downclosed in HX1.
    specialize HX1 with x None; firstorder.
  Qed.

  Definition therel : option (sig (Configuration E)) -> sig (Configuration (prefixing_es E a)) -> Prop :=
    fun x y => maybe (proj1_sig y=Empty_set _) (fun x => y = add_none_sig x) x.

  Lemma Configuration_add_none X :
    Configuration E X -> Configuration (prefixing_es E a) (add_none X).
  Proof.
    intros H.
    split.
    - intros x ix y cxy; destruct x,y; firstorder.
    - intros x y R cxy; destruct x,y; firstorder.
  Qed.

  Lemma pref_sim1 :
    Simulation (prefixing_lts (lts_of_es E) a) (lts_of_es (prefixing_es E a)) therel.
  Proof.
    intros p q rpq p' b tpp'.
    destruct p' as [p'|]; simpl in *.
    - destruct p as [p|]; simpl in *.
      + exists (add_none_sig p'); simpl in *; intuition.
        destruct tpp' as (e,(H1,(H2,(H3,H4)))).
        rewrite rpq; simpl.
        exists (Some e); simpl; rewrite add_none_add_eq; intuition.
        * now apply f_equal.
        * now apply Configuration_add_none.
      + exists (add_none_sig (empty _)); simpl in *; intuition.
        * destruct q as (q,Hq); rewrite rpq.
          exists None; simpl in *; intuition.
          -- now rewrite Add_none_empty.
          -- rewrite <- H0, <- Add_none_empty.
             now apply Configuration_add_none.
          -- now apply Noone_in_empty in H1.
        * now rewrite H.
    - exfalso; destruct p; intuition.
  Qed.

  Lemma Add_opt A X x e:
    In A (Add _ (fun x : A => X (Some x)) e) x <-> In (option A) (Add _ X (Some e)) (Some x).
  Proof.
    split; intros H; apply Add_inv in H; destruct H; intuition.
    - rewrite H; apply Add_intro2.
    - injection H as h; rewrite h; apply Add_intro2.
  Qed.

  Lemma Configuration_prefixing_add X e :
    Configuration (prefixing_es E a) (Add _ X (Some e)) -> Configuration E (Add _ (ens_of_opt X) e).
  Proof.
    intros (C1,C2).
    split.
    - intros x ix y cxy.
      unfold downclosed in C1; specialize C1 with (Some x) (Some y).
      apply Add_inv in ix; destruct ix.
      + apply Add_intro1 with (x:=e), Add_opt,C1,Add_inv in H; intuition.
        injection H0 as h; rewrite h; intuition.
      + assert (In _ (Add _ X (Some e)) (Some x)).
        rewrite H; intuition.
        apply C1,Add_inv in H0; intuition.
        injection H1 as h; rewrite h; intuition.
    - intros x y H cxy; unfold not; intros C.
      unfold conflict_free in C2; specialize C2 with (Some x) (Some y).
      apply C2; intuition.
      + apply Add_inv in H; destruct H; intuition.
        rewrite H; intuition.
      + apply Add_inv in cxy; destruct cxy; intuition.
        rewrite H0; intuition.
  Qed.

  Lemma pref_sim2 :
    Simulation (lts_of_es (prefixing_es E a)) (prefixing_lts (lts_of_es E) a) (fun x y => therel y x).
  Proof.
    intros q p rqp q' b tqq'.
    destruct tqq' as (e,(H1,(H2,(H3,H4)))).
    destruct p as [p|]; simpl in *.
    - destruct e as [e|].
      + exists (Some (remove_none_sig q')); simpl in *.
        destruct q as (q,Hq); apply (f_equal remove_none_sig),proj1_sig_eq in rqp; simpl in *.
        destruct p as (p,Hp); simpl in *.
        split.
        * rewrite ens_of_opt_add_none in rqp.
          exists e; rewrite <- rqp; intuition.
          -- now rewrite H1,ens_of_opt_add,rqp.
          -- now apply Configuration_prefixing_add.
        * assert (Inhabited _ (proj1_sig q')).
          -- rewrite H1.
             apply (Inhabited_intro _ _ (Some e)), Add_intro2.
          -- now rewrite add_remove_none.
      + exfalso.
        apply H3.
        apply proj1_sig_eq in rqp.
        destruct q as (q,(Hq1,Hq2)); simpl in *.
        now rewrite rqp.
    - (* start *)
      destruct e.
      + apply Extension in rqp; destruct rqp as (R1,R2).
        exfalso.
        assert (~ (In _ (Add _ (proj1_sig q) (Some e)) None)).
        * unfold not; intros H.
          apply Add_inv in H; destruct H; try congruence; firstorder.
        * apply H.
          destruct H2 as (H21,H22).
          unfold downclosed,cmp,prefixing_es in H21.
          specialize H21 with (Some e) None.
          apply H21; simpl; intuition.
      + exists (Some (empty _)); simpl in *; intuition.
        apply specif_eq; simpl.
        now rewrite H1, Add_none_empty, rqp.
  Qed.

  Theorem prefixing_bisim :
    Bisimilar (prefixing_lts (lts_of_es E) a) (lts_of_es (prefixing_es E a)).
  Proof.
    exists therel.
    split; try split.
    - apply pref_sim1.
    - apply pref_sim2.
    - easy.
  Qed.

End PrefixingCorrect.
