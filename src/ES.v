Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Constructive_sets.
Require Coq.Vectors.Vector.

Require Import Causality.Utils.

Definition irreflexive A R: Prop := forall x:A, not (R x x).

(** Conflict relation *)
Record conflict t c := { conflict_sym : symmetric t c;
                         conflict_irfl : irreflexive t c}.

Definition conflict_inherit {t} cmp cfl :=
  forall x y z:t, cfl x y -> cmp y z -> cfl x z.

Set Implicit Arguments.

Record ES s t :=
  mkES { cmp : relation t; cmp_ord : order t cmp;
         cfl : relation t; cfl_conflict : conflict t cfl;
         inherit : conflict_inherit cmp cfl;
         lbl : t -> s}.

Definition par_rel a b (ra : relation a) (rb : relation b) : relation (a + b) :=
  fun x y =>
    match x,y with
    | inl x, inl y => ra x y
    | inr x, inr y => rb x y
    | _,_ => False end.

Lemma par_order a b (ra : relation a) (ra_o:order a ra) (rb : relation b) (rb_o:order b rb) :
  order (a + b) (par_rel ra rb).
Proof.
  split.
  - intro x; case x; firstorder.
  - intros x y z rxy ryz; case x,y,z; firstorder.
  - intros x y rxy ryx.
    case x,y; simpl in *; try easy; f_equal; firstorder.
Qed.

Lemma par_conflict a b (ra : relation a) (ra_o:conflict a ra) (rb : relation b) (rb_o:conflict b rb) :
  conflict (a + b) (par_rel ra rb).
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
Definition par_es S A B (E:ES S A) (F:ES S B) :=
  let cmp := par_rel E.(cmp) F.(cmp) in
  let cmp_order := par_order  E.(cmp_ord) F.(cmp_ord) in
  let cfl := par_rel E.(cfl) F.(cfl) in
  let cfl_conflict := par_conflict E.(cfl_conflict) F.(cfl_conflict) in
  let inherit := par_inherit  E.(inherit)  F.(inherit) in
  let lbl := either E.(lbl) F.(lbl) in
  mkES cmp_order cfl_conflict inherit lbl.

(* Arbitrary sum *)
Definition ASum (A:Type) : nat -> Type :=
  fix vec n :=
    match n return Type with
    | O   => False
    | S n => sum A (vec n)
    end.

Definition empty_rel A : A -> A -> Prop := fun _ _ => False.

Lemma empty_order : order _ (@empty_rel False).
Proof. split; intuition; intros x; intuition. Qed.

Lemma empty_conflict : conflict _ (@empty_rel False).
Proof. split; intuition; intros x hx; intuition. Qed.

Lemma empty_inherit : conflict_inherit (@empty_rel False) (@empty_rel False).
Proof. firstorder. Qed.

Lemma false_all S : False -> S . Proof. intuition. Qed.

Definition empty_es S : ES S False :=
  mkES empty_order empty_conflict empty_inherit (@false_all S).

Fixpoint par_multiple_es S A n (xs:Vector.t (ES S A) n) : ES S (ASum A n) :=
  match xs in Vector.t _ n return ES S (ASum A n) with
  | Vector.nil _ => empty_es _
  | Vector.cons _ x n xs =>
    par_es x (par_multiple_es xs) end.

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
Definition prefixing_es S A (a:S) (E:ES S A) : ES S (option A) :=
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

Definition Configuration S A (E: ES S A) x := downclosed E.(cmp) x /\ conflict_free E.(cfl) x.

Lemma empty S A (E:ES S A) : sig (Configuration E).
Proof.
  split with (x:=Empty_set _).
  split; [intros x ix | intros x y ix];
    now apply Noone_in_empty in ix.
Defined.

Definition lts_of_es S A (E:ES S A) : LTS S (sig (Configuration E)) :=
  let t x :=
      let x := proj1_sig x in
      fun '(c,a) =>
        let x' := proj1_sig c in
        exists e, (x'=Add _ x e /\ Configuration E (Add _ x e) /\ not (In _ x e) /\ E.(lbl) e = a) in
  mkLTS t (empty _).

(* ProofIrrelevance will be used to prove the equality of two sig negleting the equality of the proof. *)
Require Coq.Logic.ProofIrrelevance.

Lemma specif_eq' {A} (P:A -> Prop) (x y : A) (px: P x) (py: P y) : x = y -> exist P x px = exist P y py.
Proof.
  intros exy.
  apply eq_sig_hprop.
  - intros z; apply Coq.Logic.ProofIrrelevance.proof_irrelevance.
  - easy.
Qed.

Lemma specif_eq A (P:A->Prop) (x:sig P) (y:sig P) : proj1_sig x = proj1_sig y -> x = y.
Proof. destruct x as (x,hx), y as (y,hy); apply specif_eq'. Qed.

Section ParBisim.

  Lemma union_ens S A B (E:ES S A) (F:ES S B) (P : {x : Ensemble A | Configuration E x} * {x : Ensemble B | Configuration F x}) :
    {x:Ensemble (A + B) | Configuration (par_es E F) x}.
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

  Lemma split_ens {S A B} (E:ES S A) (F:ES S B) (X:{x:Ensemble (A + B) | Configuration (par_es E F) x}):
    {x : Ensemble A | Configuration E x}*{x : Ensemble B | Configuration F x}.
  Proof.
    split;
      [split with (x:=left_part (proj1_sig X)) | split with (x:=right_part (proj1_sig X)) ];
      destruct X as (X,HX); simpl in *; firstorder.
  Defined.

  Lemma union_split S A B (E:ES S A) (F:ES S B) X : @union_ens _ _ _ E F (split_ens X) = X.
    apply specif_eq, Extensionality_Ensembles.
    split; intros x; destruct x; intuition.
  Qed.

  Lemma split_union S A B (E:ES S A) (F:ES S B) X : @split_ens _ _ _ E F (union_ens X) = X.
    destruct X as ((X1,HX1),(X2,HX2)).
    unfold split_ens;
      apply f_equal2;
      apply specif_eq, Extensionality_Ensembles;
      split; intuition.
  Qed.

  Lemma par_Configuration S A B (E:ES S A) (F:ES S B) X :
    Configuration (par_es E F) X -> Configuration E (left_part X) /\ Configuration F (right_part X).
  Proof. firstorder. Qed.

  Lemma Configuration_either_l S A B (E:ES S A) (F:ES S B) X Y e:
    Configuration E (Add A X e) -> Configuration F Y ->
    Configuration (par_es E F)
          (Add (A + B) (disjoint_union X Y) (inl e)).
  Proof.
    destruct (add_either X Y) as (HL,HR).
    rewrite HL; intros ce cf.
    split; [intros x hx y| intros x y]; destruct x,y; firstorder.
  Qed.

  Lemma Configuration_either_r S A B (E:ES S A) (F:ES S B) X Y e:
    Configuration E X -> Configuration F (Add B Y e) ->
    Configuration (par_es E F)
          (Add (A + B) (disjoint_union X Y) (inr e)).
  Proof.
    destruct (add_either X Y) as (HL,HR).
    rewrite HR; intros ce cf.
    split; [intros x hx y| intros x y]; destruct x,y; firstorder.
  Qed.

  Lemma par_sim1 {S A B} (E:ES S A) (F:ES S B) :
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

  Lemma par_sim2 {S A B} (E:ES S A) (F:ES S B) :
    Simulation (lts_of_es (par_es E F)) (par_lts (lts_of_es E) (lts_of_es F))
               (fun y x => y=union_ens x).
  Proof.
    intros q p rqp q' a tqq'.
    destruct p as (p1,p2).
    exists (split_ens q').
    rewrite union_split.
    destruct tqq' as (e,He).
    split; intuition.
    apply (f_equal (@split_ens _ _ _ E F)) in rqp; rewrite split_union in rqp.
    injection rqp as eqp'1 eqp'2; destruct eqp'1, eqp'2.
    apply eihter_set in H; destruct H as (Hl,Hr).
    destruct e.
    - left; split; simpl.
      + apply specif_eq; simpl.
        now rewrite wrong_add2 in Hr.
      + exists a0; rewrite add_left; intuition; simpl.
        now destruct (par_Configuration H1).
    - right; split; simpl.
      + apply specif_eq; simpl.
        now rewrite wrong_add1 in Hl.
      + exists b; rewrite add_right; intuition; simpl.
        now destruct (par_Configuration H1).
  Qed.

  Theorem par_bisim S A B (E:ES S A) (F:ES S B) :
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

  Definition add_none_sig S A (E:ES S A) (a:S)  (x:{x : Ensemble A | Configuration E x}) : {x : Ensemble (option A) | Configuration (prefixing_es a E) x}.
    split with (x:=add_none (proj1_sig x)).
    split; [intros y iy z | intros y z iy];
      destruct x,y,z; unfold In,maybe in *; simpl in *; firstorder.
  Defined.

  Definition remove_none_sig S A (E:ES S A) (a:S) (X:{x : Ensemble (option A) | Configuration (prefixing_es a E) x}) : {x : Ensemble A | Configuration E x}.
    split with (x:=fun x => proj1_sig X (Some x)).
    destruct X as (X,HX).
    split; [intros y iy z | intros y z iy];
      unfold In,maybe in *; simpl in *; firstorder.
  Defined.

  Lemma remove_add_none S A (a:S) (E:ES S A) (X:{x : Ensemble A | Configuration E x}) :
    remove_none_sig (add_none_sig a X) = X.
  Proof. now apply specif_eq. Qed.

  Lemma add_remove_none S A (a:S) (E:ES S A)
        (X:{x : Ensemble (option A) | Configuration (prefixing_es a E) x})
        (H:Inhabited _ (proj1_sig X)) : add_none_sig a (remove_none_sig X) = X.
  Proof.
    apply specif_eq, Extensionality_Ensembles; simpl.
    split; intros x ix; destruct x; unfold In in *; simpl in *; intuition.
    destruct X as (X,(HX1,HX2)); simpl in *.
    destruct H.
    unfold downclosed in HX1.
    specialize HX1 with x None; firstorder.
  Qed.

  Definition therel S A (E:ES S A) (a:S) :
    option {x : Ensemble A | Configuration E x} -> {x : Ensemble (option A) | Configuration (prefixing_es a E) x} -> Prop :=
    fun x y => maybe (proj1_sig y=Empty_set _) (fun x => y = add_none_sig a x) x.

  Lemma Configuration_add_none S A (E:ES S A) (a:S) X : Configuration E X -> Configuration (prefixing_es a E) (add_none X).
  Proof.
    intros H.
    split.
    - intros x ix y cxy; destruct x,y; firstorder.
    - intros x y R cxy; destruct x,y; firstorder.
  Qed.

  Lemma pref_sim1 S A (E:ES S A) (a:S) :
    Simulation (prefixing_lts a (lts_of_es E)) (lts_of_es (prefixing_es a E)) (@therel _ _ E a).
  Proof.
    intros p q rpq p' b tpp'.
    destruct p' as [p'|]; simpl in *.
    - destruct p as [p|]; simpl in *.
      + exists (add_none_sig a p'); simpl in *; intuition.
        destruct tpp' as (e,(H1,(H2,(H3,H4)))).
        rewrite rpq; simpl.
        exists (Some e); simpl; rewrite add_none_add_eq; intuition.
        * now apply f_equal.
        * now apply Configuration_add_none.
      + exists (add_none_sig a (empty _)); simpl in *; intuition.
        * destruct q as (q,Hq).
          assert (add_none (Empty_set A) = Add (option A) q None).
          -- apply Extensionality_Ensembles; split; intros x ix; destruct x; unfold In in *; simpl in *;
               firstorder using Add_intro2.
             apply Add_inv in ix; destruct ix; simpl; try congruence.
             rewrite rpq in H3; now apply Noone_in_empty in H3.
          -- exists None; simpl;intuition.
             ++ rewrite <- H1.
                now apply Configuration_add_none.
             ++ apply Extension in rpq.
                now apply rpq, Noone_in_empty in H2.
        * now rewrite H.
    - exfalso; destruct p; intuition.
  Qed.

  Lemma Add_opt A q x e: In A (Add A (fun x : A => q (Some x)) e) x <-> In (option A) (Add (option A) q (Some e)) (Some x).
  Proof.
    split; intros H; apply Add_inv in H; destruct H; intuition.
    - rewrite H; apply Add_intro2.
    - injection H as h; rewrite h; apply Add_intro2.
  Qed.

  Lemma Configuration_add S A (E:ES S A) (a:S) q e :
    Configuration (prefixing_es a E) (Add (option A) q (Some e)) -> Configuration E (Add A (fun x : A => q (Some x)) e).
  Proof.
    intros (C1,C2).
    split.
    - intros x ix y cxy.
      unfold downclosed in C1.
      specialize C1 with (Some x) (Some y).
      apply Add_inv in ix; destruct ix.
      + apply Add_intro1 with (x:=e), Add_opt,C1,Add_inv in H; intuition.
        injection H0 as h; rewrite h; intuition.
      + assert (In (option A) (Add (option A) q (Some e)) (Some x)).
        rewrite H; intuition.
        apply C1,Add_inv in H0; intuition.
        injection H1 as h; rewrite h; intuition.
    - intros x y H cxy; unfold not; intros C.
      unfold conflict_free in C2.
      specialize C2 with (Some x) (Some y).
      apply C2; intuition.
      + apply Add_inv in H; destruct H; intuition.
        rewrite H; intuition.
      + apply Add_inv in cxy; destruct cxy; intuition.
        rewrite H0; intuition.
  Qed.

  Lemma pref_sim2 S A (E:ES S A) (a:S) :
    Simulation (lts_of_es (prefixing_es a E)) (prefixing_lts a (lts_of_es E)) (fun x y => @therel _ _ E a y x).
  Proof.
    intros q p rqp q' b tqq'.
    destruct tqq' as (e,(H1,(H2,(H3,H4)))).
    apply Extension in H1.
    destruct p as [p|]; simpl in *.
    - destruct e as [e|].
      + exists (Some (remove_none_sig q')); simpl in *.
        destruct q as (q,Hq); apply (f_equal (@remove_none_sig _ _ E a)),proj1_sig_eq in rqp; simpl in *.
        destruct p as (p,Hp); simpl in *.
        split.
        * assert ((Add A p e) = Add A (fun x => p x) e) by intuition.
          exists e; rewrite H, <- rqp; intuition.
          -- apply Extensionality_Ensembles; split; intros x ix.
             ++ apply H1,Add_inv in ix; destruct ix; intuition.
                injection H0 as h; rewrite h; intuition.
             ++ apply H1; apply Add_inv in ix; destruct ix; intuition.
                rewrite H0; intuition.
          -- now apply Configuration_add with a.
          -- apply H3; apply Extension in rqp; now apply rqp.
        * assert (Inhabited _ (proj1_sig q')).
          -- apply (Inhabited_intro _ _ (Some e)).
             apply H1, Add_intro2.
          -- now rewrite add_remove_none.
      + exfalso.
        apply H3.
        apply proj1_sig_eq in rqp.
        destruct q as (q,(Hq1,Hq2)); simpl in *.
        now rewrite rqp.
    - (* start *)
      apply Extension in rqp; destruct rqp as (R1,R2).
      destruct e.
      + exfalso.
        assert (~ (In _ (Add _ (proj1_sig q) (Some a0)) None)).
        * unfold not; intros H.
          apply Add_inv in H; destruct H; try congruence; firstorder.
        * apply H.
          destruct H2 as (H21,H22).
          unfold downclosed,cmp,prefixing_es in H21.
          specialize H21 with (Some a0) None.
          apply H21; simpl; intuition.
      + exists (Some (empty _)); simpl in *; intuition.
        apply specif_eq,Extensionality_Ensembles; simpl.
        symmetry in H1.
        transitivity (Add (option A) (proj1_sig q) None); intuition.
        split; intros x ix; destruct x; unfold In in *; simpl in *; intuition.
        * apply Add_inv in ix.
          destruct ix; try congruence.
          now apply R1,Noone_in_empty in H.
        * apply Add_intro2.
  Qed.

  Theorem prefixing_bisim S A (E:ES S A) (a:S) :
    Bisimilar (prefixing_lts a (lts_of_es E)) (lts_of_es (prefixing_es a E)).
  Proof.
    exists (@therel _ _ E a).
    split; try split.
    - apply pref_sim1.
    - apply pref_sim2.
    - easy.
  Qed.

End PrefixingBisim.
