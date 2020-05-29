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
  unfold ctype,downclosed,conflict_free.
  split.
  - intros x ix.
    now apply Noone_in_empty in ix.
  - intros x y ix.
    now apply Noone_in_empty in ix.
Defined.

Definition lts_of_es {s A} (E:ES s A) : LTS s (sig (ctype E)) :=
  let t x :=
      let x := proj1_sig x in
      fun '(c,a) =>
        let x' := proj1_sig c in
        exists e, (x'=Add _ x e /\ ctype E (Add _ x e) /\ not (In _ x e) /\ E.(lbl) e = a) in
  mkLTS _ (sig (ctype E)) t (empty _).

Lemma add_none {S A} (E: ES S A) a (x : option (sig (ctype E))) : {x : Ensemble (option A) | ctype (prefixing_es a E) x}.
  split with (x:= maybe (Singleton (option A) None) (fun x => maybe True (proj1_sig x)) x).
  split.
  - unfold downclosed,In; intros y hy z hz.
    destruct x; unfold proj1_sig,maybe,cmp,prefixing_es,prefix_opt,maybe in *.
    + destruct s as (s,hs); destruct y,z; simpl; firstorder.
    + destruct y,z; simpl; firstorder.
      apply Singleton_inv in hy; congruence.
  - unfold conflict_free, not, In, lift_rel,maybe,proj1_sig in *; intros y z iy iz cyz.
    destruct x; simpl in *.
    + destruct s as (s,hs); destruct y,z; firstorder.
    + destruct y,z; firstorder.
      apply Singleton_inv in iy; congruence.
Defined.

Lemma remove_none {S A} (E: ES S A) a (X : sig (ctype (prefixing_es a E))) : sig (ctype E).
Proof.
  split with (x:=(fun x => proj1_sig X (Some x))).
  destruct X as (X,HX); simpl. firstorder.
Defined.

Theorem prefixing_compat {S A} (a:S) (E:ES S A) :
  Bisimilar (lts_of_es (prefixing_es a E)) (prefixing_lts a (lts_of_es E)).
Proof.
  exists (fun x y => Same_set _ (proj1_sig x) (proj1_sig (add_none E a y))).
Admitted.
