Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Constructive_sets.

Require Import Causality.Utils.

Definition irreflexive A R: Prop := forall x:A, not (R x x).

(** Conflict relation *)
Record conflict t c := { conflict_sym : symmetric t c;
                         conflict_irfl : irreflexive t c}.

Definition conflict_inherit {t} cmp cfl :=
  forall x y z:t, cfl x y -> cmp y z -> cfl x z.

Record ES s t :=
  mkES { cmp : relation t; cmp_ord : order t cmp;
         cfl : relation t; cfl_conflict : conflict t cfl;
         inherit : conflict_inherit cmp cfl;
         lbl : t -> s}.

Arguments cmp {s t}.
Arguments cmp_ord {s t}.
Arguments cfl {s t}.
Arguments cfl_conflict {s t}.
Arguments inherit {s t}.
Arguments lbl {s t}.

Definition par_rel {a b} (ra : relation a) (rb : relation b) : relation (a + b) :=
  fun x y =>
    match x,y with
    | inl x, inl y => ra x y
    | inr x, inr y => rb x y
    | _,_ => False end.

Lemma par_order {a b} (ra : relation a) (ra_o:order a ra) (rb : relation b) (rb_o:order b rb) :
  order (a + b) (par_rel ra rb).
Proof.
  split.
  - unfold reflexive; intro x; case x; firstorder.
  - unfold transitive; intros x y z rxy ryz; case x,y,z; firstorder.
  - unfold antisymmetric; intros x y rxy ryx.
    case x,y; simpl in *; try easy; f_equal; firstorder.
Qed.

Lemma par_conflict {a b} (ra : relation a) (ra_o:conflict a ra) (rb : relation b) (rb_o:conflict b rb) :
  conflict (a + b) (par_rel ra rb).
Proof.
  split.
  - unfold symmetric; intros x y rxy; case x,y; firstorder.
  - unfold irreflexive; intros x; case x; firstorder.
Qed.

Lemma par_inherit {a b}
      (ra ca : relation a) (ai : conflict_inherit ra ca) (rb cb : relation b) (bi : conflict_inherit rb cb) :
  conflict_inherit (par_rel ra rb) (par_rel ca cb).
Proof.
  unfold conflict_inherit; intros x y z h1 h2; case x,y,z; firstorder.
Qed.

(* Parallel composition of two ES *)
Definition par_es {S A B} (E:ES S A) (F:ES S B) :=
  let cmp := par_rel E.(cmp) F.(cmp) in
  let cmp_order := par_order _ E.(cmp_ord) _ F.(cmp_ord) in
  let cfl := par_rel E.(cfl) F.(cfl) in
  let cfl_conflict := par_conflict _ E.(cfl_conflict) _ F.(cfl_conflict) in
  let inherit := par_inherit _ _ E.(inherit) _ _ F.(inherit) in
  let lbl := either E.(lbl) F.(lbl) in
  mkES S _ cmp cmp_order cfl cfl_conflict inherit lbl.

Definition lift_rel {A} (R:relation A) : relation (option A) :=
  maybe (fun _ => False) (fun x => maybe False (R x)).

Lemma lift_rel_cfl {A} (R:relation A) (cR : conflict _ R) : conflict _ (lift_rel R).
Proof.
  split.
  - unfold symmetric, lift_rel, maybe; intros x y; destruct x,y; firstorder.
  - unfold irreflexive, lift_rel, maybe; intros x; destruct x; firstorder.
Qed.

Definition prefix_opt {A} (R:relation A) : relation (option A) :=
  maybe (fun _ => True) (fun x => maybe False (R x)).

Lemma prefix_opt_order {A} (R:relation A) (or :order _ R) : order _ (prefix_opt R).
Proof.
  unfold prefix_opt,maybe.
  split.
  - unfold reflexive; intros x; destruct x; firstorder.
  - unfold transitive; intros x y z; destruct x,y,z; firstorder.
  - unfold antisymmetric; intros x y rxy ryx. destruct x,y; firstorder.
    assert (a=a0) by firstorder.
    now rewrite H.
Qed.

Lemma prefix_opt_inherit {a} (ra rb : relation a) (ai : conflict_inherit ra rb) :
  conflict_inherit (prefix_opt ra) (lift_rel rb).
Proof.
  unfold conflict_inherit; intros x y z cxy ryz.
  destruct x,y,z; unfold lift_rel, prefix_opt in *; firstorder.
Qed.

(* Prefixing for ES *)
Definition prefixing_es {S A} (a:S) (E:ES S A) : ES S (option A) :=
  let cmp := prefix_opt E.(cmp) in
  let cmp_order := prefix_opt_order _ E.(cmp_ord) in
  let cfl := lift_rel E.(cfl) in
  let cfl_conflict := lift_rel_cfl _ E.(cfl_conflict) in
  let inherit := prefix_opt_inherit _ _ E.(inherit) in
  let lbl := maybe a E.(lbl) in
  mkES S _ cmp cmp_order cfl cfl_conflict inherit lbl.

Require Import LTS.

Definition downclosed {a} (cmp : relation a) (X: Ensemble a) :=
  forall x, In _ X x -> forall y, cmp y x -> In _ X y.

Definition conflict_free {a} (cfl : relation a) (X: Ensemble a) :=
  forall x y, In _ X x -> In _ X y -> not (cfl x y).

Definition ctype {s a} (E: ES s a) x := downclosed E.(cmp) x /\ conflict_free E.(cfl) x.

Lemma empty {s A} (E:ES s A) : sig (ctype E).
Proof.
  split with (x:=Empty_set _).
  split; [intros x ix | intros x y ix];
    now apply Noone_in_empty in ix.
Defined.

Definition lts_of_es {s A} (E:ES s A) : LTS s (sig (ctype E)) :=
  let t x :=
      let x := proj1_sig x in
      fun '(c,a) =>
        let x' := proj1_sig c in
        exists e, (x'=Add _ x e /\ ctype E (Add _ x e) /\ not (In _ x e) /\ E.(lbl) e = a) in
  mkLTS _ (sig (ctype E)) t (empty _).

Lemma f {S A B} (E:ES S A) (F:ES S B) (P : {x : Ensemble A | ctype E x} * {x : Ensemble B | ctype F x}) :
  {x:Ensemble (A + B) | ctype (par_es E F) x}.
Proof.
  split with (x:=either (fun x => In _ (proj1_sig (fst P)) x) (fun y => In _ (proj1_sig (snd P)) y)).
  destruct P as (X,Y).
  destruct X as (X,(dcx,cfx)), Y as (Y,(dcy,cfy)).
  unfold ctype, downclosed, conflict_free; split.
  - unfold In; intros x ix y c.
    unfold par_es,cmp,par_rel in c.
    destruct y,x; simpl either in *; firstorder.
  - intros x y ix iy.
    unfold cfl, par_es,par_rel.
    destruct x,y; firstorder.
Defined.

Lemma unf {S A B} (E:ES S A) (F:ES S B) (X:{x:Ensemble (A + B) | ctype (par_es E F) x}):
  {x : Ensemble A | ctype E x}*{x : Ensemble B | ctype F x}.
Proof.
  split;
    [split with (x:=fun x => In _ (proj1_sig X) (inl x)) | split with (x:=fun x => In _ (proj1_sig X) (inr x)) ];
    destruct X as (X,HX); simpl in *; firstorder.
Defined.

(* ProofIrrelevance will be use to prove the equality of two sig negleting the equality of the proof. *)
Require Coq.Logic.ProofIrrelevance.

Lemma specif_eq {A} (P:A -> Prop) (x y : A) (px: P x) (py: P y) : x = y -> exist P x px = exist P y py.
Proof.
  intros exy.
  apply eq_sig_hprop.
  - intros z; apply Coq.Logic.ProofIrrelevance.proof_irrelevance.
  - easy.
Qed.

Lemma funf {S A B} (E:ES S A) (F:ES S B) X : f E F (unf E F X) = X.
  destruct X as (X,HX).
  apply specif_eq, Extensionality_Ensembles.
  split; intros x; destruct x; intuition.
Qed.

Lemma unff {S A B} (E:ES S A) (F:ES S B) X : unf E F (f E F X) = X.
  destruct X as ((X1,HX1),(X2,HX2)).
  unfold f,unf.
  apply f_equal2;
    apply specif_eq, Extensionality_Ensembles;
    split; intuition.
Qed.

Lemma par_ctype {S A B} (E:ES S A) (F:ES S B) X :
  ctype (par_es E F) X -> ctype E (fun x => X (inl x)) /\ ctype F (fun x => X (inr x)).
Proof. firstorder. Qed.

Lemma add_either {A B} X Y :
  (forall e,
    Add (A + B) (either (fun x : A => In A X x) (fun y : B => In B Y y)) (inr e) =
    either (fun x : A => In A X x) (Add _ Y e)) /\
  (forall e,
      Add (A + B) (either (fun x : A => In A X x) (fun y : B => In B Y y)) (inl e) =
      either (Add _ X e) (fun y : B => In B Y y)).
Proof.
  split; intros e;
    apply Extensionality_Ensembles;
    split; intros x ix; destruct x; intuition; apply Add_inv in ix; destruct ix; intuition (try congruence).
  1,3,5,7:now apply Union_introl.
  1,3:injection H as h; rewrite h; apply Add_intro2.
  all:rewrite H; now apply Union_intror.
Qed.

Lemma ctype_either_l {S A B} (E:ES S A) (F:ES S B) X Y e:
  ctype E (Add A X e) -> ctype F Y ->
  ctype (par_es E F)
        (Add (A + B) (either (fun x : A => In A X x) (fun y : B => In B Y y)) (inl e)).
Proof.
  destruct (add_either X Y) as (HR,HL).
  rewrite HL; intros ce cf.
  split; [intros x hx y| intros x y]; destruct x,y; firstorder.
Qed.

Lemma ctype_either_r {S A B} (E:ES S A) (F:ES S B) X Y e:
  ctype E X -> ctype F (Add B Y e) ->
  ctype (par_es E F)
        (Add (A + B) (either (fun x : A => In A X x) (fun y : B => In B Y y)) (inr e)).
Proof.
  destruct (add_either X Y) as (HR,HL).
  rewrite HR; intros ce cf.
  split; [intros x hx y| intros x y]; destruct x,y; firstorder.
Qed.

Lemma add_a {A B} X:
  (forall a, (fun x => Add (A + B) X (inl a) (inl x)) = Add A (fun x : A => X (inl x)) a) /\
  (forall a, (fun x => Add (A + B) X (inr a) (inr x)) = Add B (fun x : B => X (inr x)) a).
Proof.
  split; intros a;
    apply Extensionality_Ensembles; split; intros x ix; apply Add_inv in ix; destruct ix; intuition.
  1,4:injection H as h; rewrite h; apply Add_intro2.
  1,3:now apply Add_intro1.
  1,2:rewrite H; now apply Add_intro2.
Qed.

Lemma par_sim1 {S A B} (E:ES S A) (F:ES S B) :
  Simulation (par_lts (lts_of_es E) (lts_of_es F)) (lts_of_es (par_es E F))
             (fun x y => y=f E F x).
Proof.
  intros p q rpq p' a tpp'.
  exists (f E F p'); intuition.
  destruct p as ((p1,Hp1),(p2,Hp2)), p' as (p'1,p'2).
  simpl.
  rewrite rpq in *.
  destruct tpp'; destruct H as (H1,H2).
  - destruct H2 as (e,He).
    exists (inl e); simpl; intuition.
    + apply Extension in H; destruct H as (Hr,Hl); simpl.
      apply Extensionality_Ensembles; split; intros x ix; destruct x.
      * apply Hr in ix.
        destruct ix; intuition.
        apply Singleton_inv in H; rewrite H; intuition.
      * rewrite <- H1 in ix. intuition.
      * apply Hl.
        apply Add_inv in ix.
        destruct ix; intuition.
        injection H as re; rewrite re; intuition.
      * apply Add_inv in ix.
        rewrite <- H1; intuition congruence.
    + now apply ctype_either_l.
  - destruct H2 as (e,He).
    exists (inr e); simpl; intuition.
    + apply Extension in H; destruct H as (Hr,Hl); simpl.
      apply Extensionality_Ensembles; split; intros x ix; destruct x.
      * rewrite <- H1 in ix. intuition.
      * apply Hr in ix.
        destruct ix; intuition.
        apply Singleton_inv in H; rewrite H; intuition.
      * apply Add_inv in ix; rewrite <- H1; intuition congruence.
      * apply Hl.
        apply Add_inv in ix.
        destruct ix; intuition.
        injection H as re; rewrite re; intuition.
    + now apply ctype_either_r.
Qed.

Lemma par_sim2 {S A B} (E:ES S A) (F:ES S B) :
  Simulation (lts_of_es (par_es E F)) (par_lts (lts_of_es E) (lts_of_es F))
             (fun y x => y=f E F x).
Proof.
  intros q p rqp q' a tqq'.
  destruct p as (p1,p2).
  exists (unf E F q').
  rewrite funf.
  destruct (unf E F q') as (p'1,p'2) eqn:eqp'.
  destruct tqq' as (e,He).
  split; intuition.
  (* Rewrite for specif *)
  destruct p2 as (p2,Hp2), p'2 as (p'2,Hp'2).
  unfold unf in eqp'; injection eqp' as eqp'1 eqp'2.
  destruct eqp'1, eqp'2.
  apply (f_equal (unf E F)) in rqp.
  rewrite unff in rqp; injection rqp as eqp'1 eqp'2.
  destruct eqp'1, eqp'2.
  simpl.
  apply Extension in H.
  destruct H as (Hl,Hr).
  destruct e; [left | right]; split; simpl.
  1,3:
    apply specif_eq, Extensionality_Ensembles;
    split; intros x ix;
      try apply Hr; intuition;
        try apply Hl,Add_inv in ix; destruct ix; try congruence; intuition.
  - unfold In,t.
    exists a0; intuition; simpl.
    + apply Extensionality_Ensembles; split; intros x ix; [apply Hl in ix| apply Hr];
        apply Add_inv in ix; destruct ix; intuition.
      * injection H as h; rewrite <- h; intuition.
      * rewrite H; intuition.
    + destruct (par_ctype E F _ H1).
      now rewrite <- (proj1 (add_a _)).
  - unfold In,t.
    exists b; intuition; simpl.
    + apply Extensionality_Ensembles; split; intros x ix; [apply Hl in ix| apply Hr];
        apply Add_inv in ix; destruct ix; intuition.
      * injection H as h; rewrite <- h; intuition.
      * rewrite H; intuition.
    + destruct (par_ctype E F _ H1).
      now rewrite <- (proj2 (add_a _)).
Qed.

Theorem par_bisim {S A B} (E:ES S A) (F:ES S B) :
  Bisimilar (par_lts (lts_of_es E) (lts_of_es F)) (lts_of_es (par_es E F)).
Proof.
  exists (fun x y => y=f E F x).
  split; try split.
  - apply par_sim1.
  - apply par_sim2.
  - unfold start,lts_of_es,par_es,par_lts,empty,f.
    apply specif_eq; simpl.
    apply Extensionality_Ensembles; split; intros x ix; destruct x; apply Noone_in_empty in ix; intuition.
Qed.
