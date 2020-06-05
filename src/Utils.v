Require Import Coq.Sets.Constructive_sets.
Set Implicit Arguments.

Definition maybe A B (e:B) (f:A -> B) (x:option A) :=
  match x with
  | None => e
  | Some x => f x end.

Definition add_none A (X: Ensemble A) : Ensemble (option A) :=
  maybe True X.

Definition either A B C (f: A -> C) (g: B -> C) (x:A + B) :=
  match x with
  | inl x => f x
  | inr x => g x end.

Definition left_part  A B (X : Ensemble (A+B)) : Ensemble A := fun x => X (inl x).
Definition right_part A B (X : Ensemble (A+B)) : Ensemble B := fun x => X (inr x).

Lemma eihter_set A B (X Y : Ensemble (A+B)) :
  X = Y -> left_part X = left_part Y /\ right_part X = right_part Y.
Proof.
  intros H.
  split; apply Extensionality_Ensembles; split; intros x ix; now rewrite H in *.
Qed.

Lemma add_left A B (X : Ensemble (A+B)) x :
  Add _ (left_part X) x = left_part (Add _ X (inl x)).
  apply Extensionality_Ensembles; split; intros y iy; apply Add_inv in iy; destruct iy.
  1,3: now apply Union_introl.
  - rewrite H; now apply Union_intror.
  - injection H as h; rewrite h; now apply Union_intror.
Qed.

Lemma add_right A B (X : Ensemble (A+B)) x :
  Add _ (right_part X) x = right_part (Add _ X (inr x)).
  apply Extensionality_Ensembles; split; intros y iy; apply Add_inv in iy; destruct iy.
  1,3: now apply Union_introl.
  - rewrite H; now apply Union_intror.
  - injection H as h; rewrite h; now apply Union_intror.
Qed.

Lemma wrong_add1 A B(X : Ensemble (A+B)) x :
  left_part (Add _ X (inr x)) = left_part X.
Proof.
  apply Extensionality_Ensembles; split; intros y iy.
  - apply Add_inv in iy; destruct iy; intuition (try congruence).
  - now apply Union_introl.
Qed.

Lemma wrong_add2 A B (X : Ensemble (A+B)) x :
  right_part (Add _ X (inl x)) = right_part X.
Proof.
  apply Extensionality_Ensembles; split; intros y iy.
  - apply Add_inv in iy; destruct iy; intuition (try congruence).
  - now apply Union_introl.
Qed.

Definition disjoint_union A B X Y := either (In A X) (In B Y).

Lemma add_either A B X Y :
  (forall e,
      Add (A + B) (disjoint_union X Y) (inl e) =
      disjoint_union (Add _ X e) Y) /\
  (forall e,
      Add (A + B) (disjoint_union X Y) (inr e) =
      disjoint_union X (Add _ Y e)).
Proof.
  split; intros e;
    apply Extensionality_Ensembles;
    split; intros x ix; destruct x; intuition; apply Add_inv in ix; destruct ix; intuition (try congruence).
  1,3,5,7:now apply Union_introl.
  1,3:injection H as h; rewrite h; apply Add_intro2.
  all:rewrite H; now apply Union_intror.
Qed.
