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
  split.
  - intros x ix y c; destruct y,x; simpl in *; firstorder.
  - intros x y ix iy.
    unfold cfl, par_es,par_rel.
    destruct x,y; firstorder.
Defined.

Lemma unf {S A B} (E:ES S A) (F:ES S B) (X:{x:Ensemble (A + B) | ctype (par_es E F) x}):
  {x : Ensemble A | ctype E x}*{x : Ensemble B | ctype F x}.
Proof.
  split;
    [split with (x:=left_part (proj1_sig X)) | split with (x:=right_part (proj1_sig X)) ];
    destruct X as (X,HX); simpl in *; firstorder.
Defined.

(* ProofIrrelevance will be used to prove the equality of two sig negleting the equality of the proof. *)
Require Coq.Logic.ProofIrrelevance.

Lemma specif_eq' {A} (P:A -> Prop) (x y : A) (px: P x) (py: P y) : x = y -> exist P x px = exist P y py.
Proof.
  intros exy.
  apply eq_sig_hprop.
  - intros z; apply Coq.Logic.ProofIrrelevance.proof_irrelevance.
  - easy.
Qed.

Lemma specif_eq {A} (P:A->Prop) (x:sig P) (y:sig P) : proj1_sig x = proj1_sig y -> x = y.
Proof. destruct x as (x,hx), y as (y,hy); apply specif_eq'. Qed.

Lemma funf {S A B} (E:ES S A) (F:ES S B) X : f E F (unf E F X) = X.
  apply specif_eq, Extensionality_Ensembles.
  split; intros x; destruct x; intuition.
Qed.

Lemma unff {S A B} (E:ES S A) (F:ES S B) X : unf E F (f E F X) = X.
  destruct X as ((X1,HX1),(X2,HX2)).
  unfold f,unf;
    apply f_equal2;
    apply specif_eq, Extensionality_Ensembles;
    split; intuition.
Qed.

Lemma par_ctype {S A B} (E:ES S A) (F:ES S B) X :
  ctype (par_es E F) X -> ctype E (left_part X) /\ ctype F (right_part X).
Proof. firstorder. Qed.

Lemma ctype_either_l {S A B} (E:ES S A) (F:ES S B) X Y e:
  ctype E (Add A X e) -> ctype F Y ->
  ctype (par_es E F)
        (Add (A + B) (either (In A X) (In B Y)) (inl e)).
Proof.
  destruct (add_either X Y) as (HL,HR).
  rewrite HL; intros ce cf.
  split; [intros x hx y| intros x y]; destruct x,y; firstorder.
Qed.

Lemma ctype_either_r {S A B} (E:ES S A) (F:ES S B) X Y e:
  ctype E X -> ctype F (Add B Y e) ->
  ctype (par_es E F)
        (Add (A + B) (either (In A X) (In B Y)) (inr e)).
Proof.
  destruct (add_either X Y) as (HL,HR).
  rewrite HR; intros ce cf.
  split; [intros x hx y| intros x y]; destruct x,y; firstorder.
Qed.

Lemma par_sim1 {S A B} (E:ES S A) (F:ES S B) :
  Simulation (par_lts (lts_of_es E) (lts_of_es F)) (lts_of_es (par_es E F))
             (fun x y => y=f E F x).
Proof.
  unfold Simulation.
  intros p q rpq p' a tpp'.
  exists (f E F p'); intuition.
  destruct p as ((p1,Hp1),(p2,Hp2)), p' as (p'1,p'2).
  simpl.
  rewrite rpq in *.
  destruct tpp' as [H|H]; destruct H as (H1,(e,He)).
  - exists (inl e); simpl; intuition.
    + apply Extension in H; destruct H as (Hr,Hl); simpl.
      destruct (add_either p1 p2) as (P1,P2); rewrite P1.
      apply Extensionality_Ensembles; split; rewrite <- H1; intros x ix; destruct x; firstorder.
    + now apply ctype_either_l.
  - exists (inr e); simpl; intuition.
    + apply Extension in H; destruct H as (Hr,Hl); simpl.
      destruct (add_either p1 p2) as (P1,P2); rewrite P2.
      apply Extensionality_Ensembles; split; rewrite <- H1; intros x ix; destruct x; firstorder.
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
  destruct tqq' as (e,He).
  split; intuition.
  apply (f_equal (unf E F)) in rqp; rewrite unff in rqp.
  injection rqp as eqp'1 eqp'2; destruct eqp'1, eqp'2.
  apply eihter_set in H; destruct H as (Hl,Hr).
  destruct e.
  - left; split; simpl.
    + apply specif_eq; simpl.
      now rewrite wrong_add2 in Hr.
    + unfold In,t.
      exists a0; rewrite add_left; intuition; simpl.
      now destruct (par_ctype E F _ H1).
  - right; split; simpl.
    + apply specif_eq; simpl.
      now rewrite wrong_add1 in Hl.
    + unfold In,t.
      exists b; rewrite add_right; intuition; simpl.
      now destruct (par_ctype E F _ H1).
Qed.

Theorem par_bisim {S A B} (E:ES S A) (F:ES S B) :
  Bisimilar (par_lts (lts_of_es E) (lts_of_es F)) (lts_of_es (par_es E F)).
Proof.
  exists (fun x y => y=f E F x).
  split; try split.
  - apply par_sim1.
  - apply par_sim2.
  - apply specif_eq; simpl.
    apply Extensionality_Ensembles; split; intros x ix; destruct x; apply Noone_in_empty in ix; intuition.
Qed.
