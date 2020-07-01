Require Import Coq.Sets.Constructive_sets.
Set Implicit Arguments.

Definition maybe A B (e:B) (f:A -> B) (x:option A) :=
  match x with
  | None => e
  | Some x => f x end.

Definition add_none A (X: Ensemble A) : Ensemble (option A) :=
  maybe True X.

Lemma Add_none_empty A : add_none (Empty_set A) = Add _ (Empty_set _) None.
Proof.
  apply Extensionality_Ensembles; split; intros x ix; destruct x; firstorder.
  apply Add_inv in ix; destruct ix; firstorder congruence.
Qed.

Lemma Add_empty A e : Add _ (Empty_set A) e = Singleton _ e.
Proof.
  apply Extensionality_Ensembles.
  split; intros i ix.
  - apply Add_inv in ix; destruct ix.
    now apply Noone_in_empty in H.
    now rewrite H.
  - apply Singleton_inv in ix; rewrite ix; intuition.
Qed.

Lemma add_none_add_eq A X e: Add (option A) (add_none X) (Some e) = add_none (Add A X e).
Proof.
  apply Extensionality_Ensembles; split; intros x ix; destruct x; intuition.
  - apply Add_inv in ix; destruct ix.
    + apply Add_intro1; intuition.
    + injection H as h; rewrite h; apply Add_intro2.
  - apply Add_inv in ix; destruct ix; try congruence; intuition.
  - apply Add_inv in ix; destruct ix; intuition.
    rewrite H; intuition.
Qed.

Definition ens_of_opt A (E:Ensemble (option A)) : Ensemble A := fun x => E (Some x).

Lemma ens_of_opt_add A (E:Ensemble (option A)) e :
  ens_of_opt (Add _ E (Some e)) = Add _ (ens_of_opt E) e.
Proof.
  apply Extensionality_Ensembles; split; intros x ix; apply Add_inv in ix; destruct ix; intuition.
  - injection H as h; rewrite h; intuition.
  - now apply Add_intro1.
  - rewrite H; now apply Add_intro2.
Qed.

Lemma ens_of_opt_add_none A (E:Ensemble A) : ens_of_opt (add_none E) = E.
Proof. intuition. Qed.

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

Definition cast {T : Type} {T1 T2 : T} (H : T1 = T2) (f : T -> Type) (x : f T1) :=
    match H with
    | eq_refl => x end.

Require Import Coq.Lists.List.
Import List.ListNotations.

Lemma singl_app_last A (xs:list A) (x y:A) : [x] = xs ++ [y] -> x = y.
Proof.
  intros H.
  destruct xs; simpl in *;injection H.
  - easy.
  - now destruct xs.
Qed.
