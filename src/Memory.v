Require Import Coq.Arith.PeanoNat.
Set Implicit Arguments.

Definition mem_state (N:Set) := N -> nat.

Require Import Causality.LTS.
Require Import Causality.Program.

Definition next_candidate (N:Set) (x:N) (n:nat) : nat -> mem_op N -> Prop :=
  fun k a =>
    match a with
    | Write x' k' => x=x' /\ k=k'
    | Read x' k' => x=x' /\ k=n /\ k=k' end.

Definition interp_val_lts (N:Set) (x:N) (mu:nat) : LTS (mem_op N) :=
  let trans n := fun '(k,a) => next_candidate x n k a in
  mkLTS trans mu.

Definition interp_mem_lts (N:Set) (mu:mem_state N) : LTS (mem_op N) :=
  par_arbitrary_lts (fun x => interp_val_lts x (mu x)).

Require Import Coq.Lists.List.
Import ListNotations.

Definition trace (N:Set) := list (mem_op N).

Definition nat_of_mem_op (N:Set) (x:mem_op N) :=
  match x with
  | Write _ k | Read _ k => k end.

Fixpoint trace_ok (N:Set) (x:N) (n:nat) (ts:trace N) :=
  match ts with
  | [] => True
  | t::ts =>
    match t with
    | Write x' k => x = x' /\ trace_ok x k ts
    | Read x' k => x = x' /\ k = n /\ trace_ok x n ts end end.

Require Import Coq.Relations.Relation_Definitions.
Require Import Causality.ES.Definition.

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

Definition lift_rel A (R:relation A) (P:A -> Prop) : relation (sig P) :=
  fun x y => R (proj1_sig x) (proj1_sig y).

Lemma restrict_order A (R:relation A) (ord : order _ R) (P:A -> Prop) : order _ (@lift_rel _ R P).
Proof.
  destruct ord as (O1,O2,O3).
  split.
  - firstorder.
  - intros (x,Px) (y,Py) (z,Pz); apply O2.
  - intros (x,Px) (y,Py) R1 R2; apply specif_eq; now apply O3.
Qed.

Definition noprefix A (xs ys:list A) := not (prefix xs ys) /\ not (prefix ys xs).

Lemma noprefix_cons A (x y:A) (xs ys:list A) : x=y -> noprefix (x::xs) (y::ys) <-> noprefix xs ys.
Proof. firstorder. Qed.

Lemma noprefix_cons' A (x y:A) (xs ys:list A) : x<>y -> noprefix xs ys -> noprefix (x::xs) (y::ys).
Proof. intros n; split; intros (H1,H2); congruence. Qed.

Lemma noprefix_cfl A : conflict (list A) (@noprefix A).
Proof.
  split.
  - firstorder.
  - intros x (C1,C2).
    destruct C2; induction x; firstorder.
Qed.

Lemma restrict_cfl A (R:relation A) (ord : conflict _ R) (P:A -> Prop) : conflict _ (@lift_rel _ R P).
Proof. firstorder. Qed.

Lemma prefix_propagate A (x y z:list A) : prefix x z -> prefix y z -> prefix x y \/ prefix y x.
Proof.
  revert y z.
  induction x.
  - intuition.
  - intros y z XZ YZ.
    destruct z,y; intuition.
    destruct XZ as (E1,XZ), YZ as (E2,YZ).
    assert (prefix x y \/ prefix y x) as H by (now apply IHx with z).
    destruct H; [left | right]; rewrite E1, <- E2; now split.
Qed.

Lemma prefix_noprefix_inherit A: conflict_inherit (@prefix A) (@noprefix A).
Proof.
  intros x y z (N1,N2) P1.
  split; intros P2.
  - assert (prefix x y \/ prefix y x) as H by (now apply prefix_propagate with z).
    now destruct H.
  - destruct (prefix_order A) as (R,T,An).
    unfold transitive in T.
    now apply N2, T with z.
Qed.

Lemma restrict_inherit  A (R1 R2:relation A) (inherit : conflict_inherit R1 R2) (P:A -> Prop) :
  conflict_inherit (@lift_rel _ R1 P) (@lift_rel _ R2 P).
Proof.
  intros (x,Px) (y,Py) (z,Pz) H1 H2; firstorder.
Qed.

Definition interp_val_es (N:Set) (x:N) (mu:nat) : ES (mem_op N) :=
  let lbl '(exist _ l H) := proj1_sig (projT2 (@exists_last _ l (proj1 H))) in
  @mkES _ {xs | xs <> nil /\ trace_ok x mu xs} _
        (restrict_order (@prefix_order _) _) _
        (restrict_cfl (@noprefix_cfl _) _)
        (@restrict_inherit _ _ _ (@prefix_noprefix_inherit _) _) lbl.

Require Import Coq.Logic.Eqdep_dec.
Require Import Causality.ES.Parallel.

Module InterpMemES(NS:DecidableSet).

End InterpMemES.

Require Import Coq.Sets.Constructive_sets.

Lemma add_two_elem A xs (a b:A) : xs ++ [a;b] = xs ++ [a] ++ [b].
Proof. firstorder. Qed.

Definition majorant A (E:Ensemble A) (x:A) (R:relation A) := forall y, In _ E y -> R y x.

Module InterpMemOK(NS:DecidableSet).
  Import NS.

  Module Par := ArbitraryParallel(NS).

  Definition interp_mem_es (mu:mem_state U) : ES (mem_op U) :=
    Par.par_arbitrary_es (fun i => interp_val_es i (mu i)).

  Module ALTS := ArbitraryLTS(NS).

  Section WithEM.

    Variables (x:U) (mu:nat).

    Definition therel : State (interp_val_lts x mu) -> State (lts_of_es (interp_val_es x mu)) -> Prop :=
      fun x Y =>
        if Nat.eqb x mu
        then Y = empty _
        else
          exists y,
            In _ (proj1_sig Y) y /\
            x = nat_of_mem_op (proj1_sig (projT2 (@exists_last _ (proj1_sig y) (proj1 (proj2_sig y)))))
            /\ majorant (proj1_sig Y) y (@lift_rel _ (@prefix _) _).

    Lemma trace_ok_pre (a:mem_op U) ys : trace_ok x mu (ys ++ [a]) -> trace_ok x mu ys.
    Proof.
      revert mu; induction ys; try easy.
      intros H; destruct a0; firstorder.
    Qed.

    Lemma trace_ok_next (a a': mem_op U) ys p' (tpp':next_candidate x (nat_of_mem_op a') p' a) : trace_ok x mu (ys++[a']) -> trace_ok x mu (ys++[a';a]).
    Proof.
      revert mu.
      induction ys.
      - intros mu H.
        destruct a'.
        + destruct H as (H1,(H2,H3)); split; try split; try easy.
          destruct a; simpl in tpp'; split; try split; try easy.
          destruct tpp' as (H4,(H5,H6)).
          now rewrite <- H6, H5.
        + destruct H as (H1,H2).
          split; try easy.
          destruct a; simpl in tpp'; split; try split; try easy.
          destruct tpp' as (H4,(H5,H6)).
          now rewrite <- H6, H5.
      - intros mu H; simpl in *; destruct a0; firstorder.
    Qed.

    Program Definition add_next_cand (a a': mem_op U) ys (H:trace_ok x mu (ys++[a'])) p' (tpp':next_candidate x (nat_of_mem_op a') p' a) :
      {xs | xs <> [] /\ trace_ok x mu xs} :=
      exist _ (ys ++ [a';a]) _.

    Next Obligation.
      split.
      - intros E; now apply app_eq_nil in E.
      - now apply trace_ok_next with p'.
    Qed.

    Lemma config_1 q a a' ys ys' H Hys p' tpp' :
      ys = ys' ++ [a']
      -> majorant q (exist (fun xs : list (mem_op U) => xs <> [] /\ trace_ok x mu xs) ys Hys)
               (@lift_rel _ (@prefix (mem_op U)) (fun xs : list (mem_op U) => xs <> [] /\ trace_ok x mu xs))
      -> Configuration (interp_val_es x mu) q
      -> Configuration (interp_val_es x mu) (Add _ q (add_next_cand a a' ys' H p' tpp')).
    Proof.
      intros E M (D,C).
      split.
      - intros y iy z iz.
        apply Add_inv in iy.
        destruct iy as [iy|iy].
        + generalize iy; intros iy'.
          unfold majorant in M.
          apply M in iy.
          unfold downclosed in D.
          specialize D with y z.
          now apply Add_intro1, D.
        + admit. (* TODO contradiction majorant *)
      - intros y z iy iz cyz.
    Admitted.

    Lemma interp_val_sim_1 :
      Simulation (interp_val_lts x mu) (lts_of_es (interp_val_es x mu)) therel.
    Proof.
      intros p (q,Confq) rpq p' a tpp'; simpl in *.
      unfold therel in rpq; destruct (Nat.eqb p mu) eqn:eq.
      - apply Nat.eqb_eq in eq. admit.
      - destruct rpq as ((ys,Hys),(R1,(R2,R3))); simpl in *.
        destruct (exists_last (proj1 Hys)) as (ys',(a',E)); simpl in *.
        generalize Hys; intros (Hys1,Hys2).
        rewrite R2 in tpp'; rewrite E in Hys2.
        generalize Hys2; intros Hys2'.
        apply trace_ok_pre in Hys2.
        unfold lift_rel in R3.
        exists (exist  _ (Add _ q (add_next_cand a a' ys' Hys2' p' tpp')) (config_1 a a' ys' Hys2' p' tpp' E R3 Confq)).
        destruct (@prefix_order (mem_op U)).
        unfold majorant,lift_rel in *;
          split.
        + exists (add_next_cand a a' ys' Hys2' p' tpp'); split; try split.
          * now apply config_1 with ys Hys.
          * split.
            -- intros H.
               apply R3 in H; simpl in H.
               rewrite add_two_elem,app_assoc, <- E in H.
               assert (~ (prefix (ys ++ [a]) ys)).
               apply prefix_napp; easy.
               congruence.
            -- simpl.
               destruct (exists_last (proj1 (add_next_cand_obligation_1 a a' ys' Hys2' p' tpp'))) as (k,(l,H));
                 simpl.
               rewrite add_two_elem,app_assoc in H.
               apply app_inj_tail in H; intuition.
        + unfold therel; simpl.
          destruct (Nat.eqb p' mu) eqn:eq'.
          * admit.
          * exists (add_next_cand a a' ys' Hys2' p' tpp'); split; try split.
            -- apply Add_intro2.
            -- destruct (exists_last (proj1 (proj2_sig (add_next_cand a a' ys' Hys2' p' tpp')))) as (E1,(E2,E3));
                 simpl in *.
               rewrite add_two_elem,app_assoc in E3.
               apply app_inj_tail in E3; destruct E3 as (E31,E32),E32.
               destruct a; simpl in *; intuition.
            -- unfold add_next_cand; simpl in *.
               rewrite E in R3.
               intros y Hy.
               apply Add_inv in Hy.
               destruct Hy.
               ++ unfold transitive in ord_trans.
                  apply ord_trans with (y:=ys'++[a']).
                  now apply R3.
                  simpl.
                  rewrite add_two_elem,app_assoc.
                  apply prefix_app.
               ++ rewrite <- H; simpl.
                  apply ord_refl.
    Admitted.

    Lemma interp_val_sim_2 :
      Simulation (lts_of_es (interp_val_es x mu)) (interp_val_lts x mu) (fun x y => therel y x).
    Proof.
    Admitted.

    Lemma interp_val_ok:
      Bisimilar (interp_val_lts x mu) (lts_of_es (interp_val_es x mu)).
    Proof.
      exists therel.
      split; try split.
      - apply interp_val_sim_1.
      - apply interp_val_sim_2.
      - unfold therel; simpl.
        destruct (mu =? mu) eqn:eq; try easy.
        assert (mu <> mu) by (intros C; apply Nat.eqb_eq in C; congruence).
        congruence.
    Qed.

  End WithEM.

  Theorem interp_mem_ok (mu:mem_state U) :
    Bisimilar (interp_mem_lts mu) (lts_of_es (interp_mem_es mu)).
  Proof.
    apply bisim_trans with (Y:=par_arbitrary_lts (fun i => lts_of_es (interp_val_es i (mu i)))).
    - apply ALTS.par_bisim_morphism.
      intros i.
      apply interp_val_ok.
    - apply Par.par_arbitrary_ok.
  Qed.

End InterpMemOK.
