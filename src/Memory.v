Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Causality.Utils.

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
  let lbl '(exist _ l H) := proj1_sig (projT2 (exists_last (proj1 H))) in
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

Lemma app_inj_l A (xs ys zs : list A) : xs ++ ys = xs ++zs -> ys =zs.
Proof.
  revert ys zs.
  induction xs;try easy.
  intros ys zs H.
  do 2 rewrite <- app_comm_cons in H.
  injection H; intros H1.
  now apply IHxs.
Qed.

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
        ((x = mu) /\ Y = empty _) \/
        exists y,
          In _ (proj1_sig Y) y /\
          x = nat_of_mem_op (proj1_sig (projT2 (@exists_last _ (proj1_sig y) (proj1 (proj2_sig y)))))
          /\ majorant (proj1_sig Y) y (@lift_rel _ (@prefix _) _).

    Lemma trace_ok_pre xs ys : trace_ok x mu (xs++ys) -> trace_ok x mu xs.
    Proof.
      revert mu; induction xs; try easy.
      intros n H; destruct ys.
      - now rewrite app_nil_r in H.
      - rewrite <- app_comm_cons in H.
        destruct a; firstorder.
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
      In _ q ys
      -> majorant q (exist (fun xs : list (mem_op U) => xs <> [] /\ trace_ok x mu xs) (proj1_sig ys) Hys)
                  (@lift_rel _ (@prefix (mem_op U)) (fun xs : list (mem_op U) => xs <> [] /\ trace_ok x mu xs))
      -> proj1_sig ys = ys' ++ [a']
      -> Configuration (interp_val_es x mu) q
      -> Configuration (interp_val_es x mu) (Add _ q (add_next_cand a a' ys' H p' tpp')).
    Proof.
      intros Iys M E (D,C).
      split.
      - intros y iy z iz.
        unfold downclosed in D.
        apply Add_inv in iy.
        destruct iy as [iy|iy].
        + specialize D with y z.
          generalize iy; intros iy'.
          unfold majorant in M.
          apply M in iy.
          now apply Add_intro1, D.
        + unfold cmp,interp_val_es,lift_rel in iz.
          generalize iz; intros iz'.
          apply prefix_ex in iz.
          destruct iz as (zs,iz).
          destruct zs.
          * rewrite app_nil_r in iz.
            assert (y=z) as R by (now apply specif_eq).
            rewrite <-R, <- iy;intuition.
          * specialize D with ys z.
            left.
            apply D; try easy.
            unfold cmp,interp_val_es,lift_rel.
            destruct z as (z,Hz), y as (y,Hy), ys as (ys,HH); simpl in *.
            unfold add_next_cand in iy; apply proj1_sig_eq in iy; simpl in iy.
            rewrite E.
            rewrite <- iy in iz'.
            apply prefix_extend with a; rewrite <- app_assoc,<- add_two_elem; try easy.
            intros P.
            rewrite P, iy in iz.
            assert (y=y++[]) as Y by (now rewrite app_nil_r).
            rewrite Y in iz at 1.
            apply app_inj_l in iz.
            congruence.
      - intros y z iy iz cyz.
        apply Add_inv in iy.
        apply Add_inv in iz.
        unfold cfl, interp_val_es,lift_rel in cyz.
        destruct cyz as (C1,C2).
        destruct (@prefix_order (mem_op U)).
        unfold transitive in ord_trans.
        destruct iy as [iy|iy],iz as [iz|iz].
        + unfold conflict_free,not in C.
          now apply C with y z.
        + apply proj1_sig_eq in iz.
          unfold majorant in M; apply M in iy.
          unfold lift_rel in iy.
          destruct y as (y,Hy), z as (z,Hz); simpl in *.
          apply C1.
          apply ord_trans with (proj1_sig ys); try easy.
          rewrite E, <- iz, add_two_elem,app_assoc.
          apply prefix_app.
        + apply proj1_sig_eq in iy.
          unfold majorant in M; apply M in iz.
          unfold lift_rel in iz.
          destruct y as (y,Hy), z as (z,Hz); simpl in *.
          apply C2.
          apply ord_trans with (proj1_sig ys); try easy.
          rewrite E, <- iy, add_two_elem,app_assoc.
          apply prefix_app.
        + apply proj1_sig_eq in iy.
          apply proj1_sig_eq in iz.
          destruct y as (y,Hy), z as (z,Hz); simpl in *.
          apply C1.
          rewrite <-iy,<-iz.
          firstorder.
    Qed.

    Program Definition singleton_next p' a (H:next_candidate x mu p' a) :
      {xs | xs <> [] /\ trace_ok x mu xs} :=
      exist _ [a] _.

    Next Obligation.
      destruct a; firstorder.
      now rewrite <- H1.
    Defined.

    Lemma config_singleton_next p' a (H:next_candidate x mu p' a) :
      Configuration (interp_val_es x mu) (Singleton _ (singleton_next p' a H)).
    Proof.
      apply config_singl_minimum.
      intros y T; simpl in *.
      apply specif_eq.
      destruct y as (y,Hy); unfold lift_rel in H; simpl in *.
      destruct y.
      - now destruct Hy as (H1,H2).
      - destruct T as (H1,H2).
        rewrite H1.
        f_equal; now destruct y.
    Qed.

    Lemma interp_val_sim_1 :
      Simulation (interp_val_lts x mu) (lts_of_es (interp_val_es x mu)) therel.
    Proof.
      intros p (q,Confq) rpq p' a tpp'; simpl in *.
      destruct (@prefix_order (mem_op U)).
      destruct rpq as [(rpq1,rpq2)|rpq].
      - rewrite rpq1 in tpp'.
        exists (exist _ (Singleton _ (singleton_next p' a tpp')) (config_singleton_next p' a tpp')).
        apply proj1_sig_eq in rpq2; simpl in rpq2.
        split.
        + exists (singleton_next p' a tpp');
            rewrite rpq2, Add_empty in *; split; try split; try easy; simpl in *.
          * apply config_singleton_next.
          * split; simpl.
            -- apply Noone_in_empty.
            -- destruct (exists_last (proj1 (singleton_next_obligation_1 p' a tpp'))) as (x0, (l,Hl)) eqn:eq.
               destruct a; simpl in *;
                 rewrite eq; simpl; destruct eq;
                   now apply singl_app_last in Hl.
        + right.
          exists (singleton_next p' a tpp');split; try split; try easy.
          * destruct (exists_last (proj1 (proj2_sig (singleton_next p' a tpp')))).
            destruct s as (s1,s2); simpl in *.
            apply singl_app_last in s2.
            rewrite <- s2.
            destruct a; simpl in *; intuition.
          * intros y iy.
            apply Singleton_inv,proj1_sig_eq in iy.
            unfold lift_rel; rewrite iy.
            apply ord_refl with (x:=proj1_sig y).
      - destruct rpq as ((ys,Hys),(R1,(R2,R3))); simpl in *.
        destruct (exists_last (proj1 Hys)) as (ys',(a',E)); simpl in *.
        generalize Hys; intros (Hys1,Hys2).
        rewrite R2 in tpp'; rewrite E in Hys2.
        generalize Hys2; intros Hys2'.
        apply trace_ok_pre in Hys2.
        unfold lift_rel in R3.
        exists (exist  _ (Add _ q (add_next_cand a a' ys' Hys2' p' tpp')) (config_1 a a' (exist _ ys Hys) ys' Hys2' p' tpp' R1 R3 E Confq)).
        unfold majorant,lift_rel in *;
          split.
        + exists (add_next_cand a a' ys' Hys2' p' tpp'); split; try split.
          * now apply config_1 with (exist _ ys Hys) Hys.
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
          right.
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
    Qed.

    Lemma interp_val_sim_2 :
      Simulation (lts_of_es (interp_val_es x mu)) (interp_val_lts x mu) (fun x y => therel y x).
    Proof.
      intros p q rpq p' a ((e,(Hl,toke)),(He1,(He2,(He3,He4)))); simpl in *.
      exists (nat_of_mem_op a); split.
      - destruct rpq as [(rpq1,rpq2)|rpq].
        + rewrite rpq1,rpq2 in *; simpl in *.
          assert (e=[a]) as H.
          * rewrite Add_empty in He2.
            destruct He2 as (D,C).
            destruct e as [|e]; try congruence.
            destruct e0 as [|e0].
            -- destruct (exists_last (proj1 (conj Hl toke))) as (z,(l,T)); simpl in *.
               apply singl_app_last in T.
               rewrite He4 in T; now rewrite T.
            -- unfold downclosed in D.
               pose (y:=exist (fun xs => xs <> [] /\ trace_ok x mu xs) (e :: e0 :: e1) (conj Hl toke)).
               assert ([e] <> []) as Xl by (intros H; congruence).
               assert (trace_ok x mu [e]) as Xr by (now apply trace_ok_pre with (ys:=e0::e1)).
               pose (z:=exist (fun xs => xs <> [] /\ trace_ok x mu xs) [e] (conj Xl Xr)).
               specialize D with y z.
               exfalso.
               assert (y=z) as H by (now apply Singleton_inv,D).
               easy.
          * generalize toke;intros toke'.
            rewrite H in toke'.
            destruct a; simpl in *; intuition.
        + destruct rpq as (y,(rpq1,(rpq2,rpq3))).
          admit.
      - right.
        exists (exist _ e (conj Hl toke)); split; try split.
        + apply Extension in He1; destruct He1 as (He11,He12).
          apply He12; intuition.
        + now f_equal.
        + destruct rpq as [(rpq1,rpq2)|rpq].
          * rewrite rpq2, Add_empty in He1.
            intros y iy.
            unfold lift_rel;simpl.
            apply Extension in He1; destruct He1 as (He11,He12).
            apply He11, Singleton_inv in iy.
            rewrite <- iy; simpl.
            destruct (prefix_order (mem_op U)).
            unfold reflexive in ord_refl; apply ord_refl.
          * admit.
    Admitted.

    Lemma interp_val_ok:
      Bisimilar (interp_val_lts x mu) (lts_of_es (interp_val_es x mu)).
    Proof.
      exists therel.
      split; try split.
      - apply interp_val_sim_1.
      - apply interp_val_sim_2.
      - left; easy.
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
