Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Relations.Relation_Definitions.

Set Implicit Arguments.

Fixpoint prefix A (xs ys:list A) :=
  match xs,ys with
  | [],_ => True
  | x::xs,y::ys => x=y /\ prefix xs ys
  | _,[] => False end.

Lemma prefix_order A : order _ (@prefix A).
Proof.
  split.
  - intros x; induction x; firstorder.
  - intros x.
    induction x; intros y; destruct y; try easy.
    intros z H1 H2.
    destruct z; simpl in *; try easy.
    destruct H1 as (E1,H1), H2 as (E2,H2).
    split.
    + now rewrite E1.
    + now apply IHx with y.
  - unfold antisymmetric.
    intros x; induction x; simpl in *.
    + intros y; destruct y; easy.
    + intros y Hy; destruct y; try easy; simpl in *.
      intros H.
      destruct Hy as (Ey,Hy).
      f_equal; try easy.
      now apply IHx.
Qed.

Lemma prefix_app A (xs ys : list A) : prefix xs (xs++ys).
Proof. induction xs; firstorder. Qed.

Lemma prefix_napp A (xs ys : list A) : ys <> [] -> ~ (prefix (xs++ys) xs).
Proof.
  intros H.
  apply exists_last in H; destruct H as (H1,(zs,H2)).
  rewrite H2.
  intros Z.
  induction xs; simpl in *.
  - destruct (H1 ++ [zs]) eqn:eq; try easy.
    now destruct H1.
  - firstorder.
Qed.

Lemma prefix_ex A (xs ys:list A) : prefix xs ys -> exists zs, ys= xs ++ zs.
Proof.
  revert ys.
  induction xs; intros ys H.
  - exists ys; intuition.
  - destruct ys; simpl in H; try easy.
    destruct H as (E,H).
    apply IHxs in H.
    destruct H as (zs,H).
    exists zs.
    now rewrite E, <- app_comm_cons; f_equal.
Qed.

Lemma neq_extend A (xs ys:list A) a : a::xs <> a::ys -> xs <> ys.
Proof.
  intros H P.
  apply H.
  now rewrite P.
Qed.

Lemma prefix_extend A (xs ys:list A) a : xs<>ys++[a] -> prefix xs (ys ++ [a]) -> prefix xs ys.
Proof.
  revert ys; induction xs.
  - easy.
  - intros ys H P.
    destruct (ys++[a]) eqn:eq; try easy.
    simpl in P; destruct P as (E,P),E.
    apply neq_extend in H.
    destruct ys.
    + simpl in eq.
      assert (l=[]) as E.
      * apply (@f_equal _ _ (@length _) [a] (a0::l)) in eq.
        injection eq; intros E.
        symmetry in E.
        now apply length_zero_iff_nil in E.
      * rewrite E in *.
        now destruct xs.
    + rewrite <- app_comm_cons in eq.
      injection eq; intros H1 H2.
      destruct H2.
      rewrite <- H1 in *.
      simpl; split; try easy.
      now apply IHxs.
Qed.

Lemma prefix_propagate A (x y z:list A) : prefix x z -> prefix y z -> prefix x y \/ prefix y x.
Proof.
  revert y z.
  induction x.
  - intuition.
  - intros y z XZ YZ.
    destruct z,y; intuition; try easy.
    destruct XZ as (E1,XZ), YZ as (E2,YZ).
    assert (prefix x y \/ prefix y x) as H by (now apply IHx with z).
    destruct H; [left | right]; rewrite E1, <- E2; now split.
Qed.

Definition noprefix A (xs ys:list A) := not (prefix xs ys) /\ not (prefix ys xs).

Lemma noprefix_cons A (x y:A) (xs ys:list A) : x=y -> noprefix (x::xs) (y::ys) <-> noprefix xs ys.
Proof. firstorder. Qed.

Lemma noprefix_cons' A (x y:A) (xs ys:list A) : x<>y -> noprefix xs ys -> noprefix (x::xs) (y::ys).
Proof. intros n; split; intros (H1,H2); congruence. Qed.

Require Import Coq.Structures.Equalities.

Module PrefixDec(X:MiniDecidableType).
  Module XX := Make_UDT(X).

  Import X XX.

  Lemma prefix_dec (xs ys:list t) : prefix xs ys \/ ~ prefix xs ys.
  Proof.
    revert ys.
    induction xs; intros ys.
    - now left.
    - destruct ys.
      + now right.
      + destruct (eq_dec a t0).
        * specialize IHxs with ys; destruct IHxs.
          -- now left.
          -- right; intros (H1,H2); congruence.
        * right; intros (H1,H2); congruence.
  Qed.

  Lemma not_noprefix_prefix (xs ys : list t) : ~ noprefix xs ys -> prefix xs ys \/prefix ys xs.
  Proof.
    intros H.
    destruct (prefix_dec xs ys).
    - left; easy.
    - destruct (prefix_dec ys xs).
      + right; easy.
      + exfalso; apply H; now split.
  Qed.
End PrefixDec.
