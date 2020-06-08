Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Constructive_sets.
Require Coq.Vectors.Vector.

Require Import Causality.Utils.

Definition irreflexive A R: Prop := forall x:A, not (R x x).

(** Conflict relation *)
Record conflict A R := { conflict_sym : symmetric A R;
                         conflict_irfl : irreflexive A R}.

Definition conflict_inherit {A} (cmp cfl : relation A) :=
  forall x y z, cfl x y -> cmp y z -> cfl x z.

Set Implicit Arguments.

Record ES (Lbl : Set) :=
  mkES { Event: Set;
         cmp : relation Event; cmp_ord : order Event cmp;
         cfl : relation Event; cfl_conflict : conflict Event cfl;
         inherit : conflict_inherit cmp cfl;
         lbl : Event -> Lbl}.

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
  let cmp := par_rel E.(cmp) F.(cmp) in
  let cmp_order := par_order  E.(cmp_ord) F.(cmp_ord) in
  let cfl := par_rel E.(cfl) F.(cfl) in
  let cfl_conflict := par_conflict E.(cfl_conflict) F.(cfl_conflict) in
  let inherit := par_inherit  E.(inherit)  F.(inherit) in
  let lbl := either E.(lbl) F.(lbl) in
  mkES cmp_order cfl_conflict inherit lbl.

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

Require Import LTS.

Definition downclosed a (cmp : relation a) (X: Ensemble a) :=
  forall x, In _ X x -> forall y, cmp y x -> In _ X y.

Definition conflict_free a (cfl : relation a) (X: Ensemble a) :=
  forall x y, In _ X x -> In _ X y -> not (cfl x y).

Definition Configuration (S:Set) (E: ES S) x := downclosed E.(cmp) x /\ conflict_free E.(cfl) x.

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

Section ParBisim.

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

End ParBisim.

Require Import Coq.Classes.RelationClasses.

Instance transitive_same_set A : Transitive (Same_set A).
Proof. firstorder. Qed.

Instance symmetric_same_set A : Symmetric (Same_set A).
Proof. firstorder. Qed.

Section PrefixingBisim.

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

End PrefixingBisim.
