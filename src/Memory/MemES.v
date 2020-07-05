Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Causality.Utils.
Require Import Causality.LTS.
Require Import Causality.Program.
Require Import Causality.Memory.MemLTS.
Require Import Causality.Memory.Prefix.
Require Import Causality.Memory.Restrict.

Set Implicit Arguments.

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

Lemma trace_ok_pre (N:Set) (x:N) mu xs ys : trace_ok x mu (xs++ys) -> trace_ok x mu xs.
Proof.
  revert mu; induction xs; try easy.
  intros n H; destruct ys.
  - now rewrite app_nil_r in H.
  - rewrite <- app_comm_cons in H.
    destruct a; firstorder.
Qed.

Require Import Coq.Relations.Relation_Definitions.
Require Import Causality.ES.Definition.

Lemma noprefix_cfl A : conflict (list A) (@noprefix A).
Proof.
  split.
  - firstorder.
  - intros x (C1,C2).
    destruct C2; induction x; firstorder.
Qed.

Lemma prefix_noprefix_inherit A: conflict_inherit (@prefix A) (@noprefix A).
Proof.
  intros x y z (N1,N2) P1.
  split; intros P2.
  - assert (prefix x y \/ prefix y x) as H by (now apply prefix_propagate with z).
    now destruct H.
  - destruct (prefix_order A) as (R,T,An).
    apply N2; now transitivity z.
Qed.

Definition trace_pred (N:Set) (x:N) mu := fun xs => xs <> [] /\ trace_ok x mu xs.

Definition interp_val_es (N:Set) (x:N) (mu:nat) : ES (mem_op N) :=
  let lbl '(exist _ l H) := proj1_sig (projT2 (exists_last (proj1 H))) in
  @mkES _ {xs | trace_pred x mu xs} _
        (lift_order (@prefix_order _) _) _
        (lift_cfl (@noprefix_cfl _) _)
        (@lift_inherit _ _ _ (@prefix_noprefix_inherit _) _) lbl.

Require Import Coq.Logic.Eqdep_dec.
Require Import Causality.ES.Parallel.

Require Import Coq.Sets.Constructive_sets.

Lemma add_two_elem A xs (a b:A) : xs ++ [a;b] = xs ++ [a] ++ [b].
Proof. firstorder. Qed.

Lemma app_inj_l A (xs ys zs : list A) : xs ++ ys = xs ++ zs -> ys = zs.
Proof.
  revert ys zs.
  induction xs;try easy.
  intros ys zs H.
  do 2 rewrite <- app_comm_cons in H.
  injection H; intros H1.
  now apply IHxs.
Qed.

Require Import Coq.Structures.Equalities.

Definition majorant A (E:Ensemble A) (x:A) (R:relation A) := forall y, In _ E y -> R y x.

Module InterpMemOK(NameSet:DecidableSet).
  Import NameSet.

  Module Par := ArbitraryParallel(NameSet).

  Definition interp_mem_es (mu:mem_state U) : ES (mem_op U) :=
    Par.par_arbitrary_es (fun i => interp_val_es i (mu i)).

  Module ALTS := ArbitraryLTS(NameSet).

  Module MemOpU.
    Definition t := mem_op U.
    Definition eq_dec := mem_op_eq_dec NameSet.eq_dec.
  End MemOpU.

  Module PrefixDec := PrefixDec(MemOpU).

  Section WithEM.

    Variables (x:U) (mu:nat).

    Definition therel : State (interp_val_lts x mu) -> State (lts_of_es (interp_val_es x mu)) -> Prop :=
      fun x Y =>
        ((x = mu) /\ Y = empty _) \/
        exists y,
          In _ (proj1_sig Y) y /\
          x = nat_of_mem_op (proj1_sig (projT2 (@exists_last _ (proj1_sig y) (proj1 (proj2_sig y)))))
          /\ majorant (proj1_sig Y) y (@lift_rel _ (@prefix _) _).

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
        + generalize iz; intros iz'.
          apply prefix_ex in iz; destruct iz as (zs,iz).
          destruct zs.
          * rewrite app_nil_r in iz.
            assert (y=z) as R by (now apply specif_eq).
            rewrite <- R, <- iy; intuition.
          * specialize D with ys z.
            left.
            apply D; try easy.
            unfold cmp,interp_val_es,lift_rel.
            destruct z as (z,Hz), y as (y,Hy), ys as (ys,HH); simpl in *.
            unfold add_next_cand in iy; apply proj1_sig_eq in iy; simpl in iy.
            rewrite E.
            unfold cmp,interp_val_es,lift_rel in iz'; rewrite <- iy in iz'.
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
        unfold majorant, lift_rel in *.
        destruct iy as [iy|iy],iz as [iz|iz].
        1:unfold conflict_free,not in C;
          now apply C with y z.
        1,3:apply proj1_sig_eq in iz.
        2,3:apply proj1_sig_eq in iy.
        all:destruct y as (y,Hy), z as (z,Hz); simpl in *.
        + apply M in iy.
          apply C1; transitivity (proj1_sig ys); try easy.
          rewrite E, <- iz, add_two_elem,app_assoc.
          apply prefix_app.
        + apply C1.
          rewrite <-iy,<-iz.
          firstorder.
        + apply M in iz.
          apply C2; transitivity (proj1_sig ys); try easy.
          rewrite E, <- iy, add_two_elem,app_assoc.
          apply prefix_app.
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
          * destruct (exists_last (proj1 (proj2_sig (singleton_next p' a tpp'))))
              as (ss,(s,Hs)) eqn:eq.
            destruct a; [destruct tpp' as (H1,(H2,H3)) | destruct tpp' as (H1,H2)];
              simpl in *; rewrite eq; simpl in *; generalize Hs; intros Hs';
                apply singl_app_last in Hs'; rewrite <- Hs';
                  destruct s; try injection Hs'; simpl in *; intuition.
          * intros (y,Hy) iy.
            apply Singleton_inv,proj1_sig_eq in iy; simpl in *.
            unfold lift_rel; simpl; rewrite <- iy.
            apply ord_refl with (x:=[a]).
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
               assert (~ (prefix (ys ++ [a]) ys)) by (apply prefix_napp; easy).
               congruence.
            -- simpl.
               destruct
                 (exists_last (proj1 (add_next_cand_obligation_1 a a' ys' Hys2' p' tpp')))
                 as (k,(l,H)); simpl.
               rewrite add_two_elem,app_assoc in H.
               apply app_inj_tail in H; intuition.
        + unfold therel; simpl.
          right.
          * exists (add_next_cand a a' ys' Hys2' p' tpp'); split; try split.
            -- apply Add_intro2.
            -- simpl.
               destruct (exists_last (proj1 (add_next_cand_obligation_1 a a' ys' Hys2' p' tpp')))
                 as (E1,(E2,E3));
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
               ++ now rewrite <- H.
    Qed.

    Lemma prefix_of_last_added X y e:
      In _ X y
      -> majorant X y (cmp (interp_val_es x mu))
      -> ~ In _ X e
      -> Configuration
           (interp_val_es x mu)
           (Add _ X e)
      -> Configuration (interp_val_es x mu) X
      -> cmp (interp_val_es x mu) y e.
    Proof.
      intros iy majo_y not_x_e (D,C) (D1,C1).
      unfold majorant,downclosed,conflict_free,lift_rel in *.
      specialize C with y e.
      assert (~ cfl (interp_val_es x mu) y e) as H by (apply C; intuition).
      apply PrefixDec.not_noprefix_prefix in H.
      destruct H; try easy.
      exfalso.
      specialize D1 with y e.
      now apply D1 in iy.
    Qed.

    Lemma trace_ok_next_cand y le ly :
      trace_ok x mu (y ++ [ly; le])
      -> next_candidate x (nat_of_mem_op ly) (nat_of_mem_op le) le.
    Proof.
      revert mu.
      induction y;intros mu H.
      - destruct le,ly; firstorder.
        simpl; now rewrite H2, <- H0.
      - rewrite <- app_comm_cons in H.
        destruct a; [destruct H as (H1,(H2,H)) | destruct H as (H1,H)];
          now apply IHy in H.
    Qed.

    Definition trace_pred := trace_pred x mu.

    Lemma interp_val_sim_2 :
      Simulation (lts_of_es (interp_val_es x mu)) (interp_val_lts x mu) (fun x y => therel y x).
    Proof.
      intros p q rpq p' a ((e,(Hl,toke)),(He1,(He2,(He3,He4)))); simpl in *.
      destruct (prefix_order (mem_op U)).
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
               pose (y:=exist trace_pred (e :: e0 :: e1) (conj Hl toke)).
               assert ([e] <> []) as Xl by (intros H; congruence).
               assert (trace_ok x mu [e]) as Xr by (now apply trace_ok_pre with (ys:=e0::e1)).
               pose (z:=exist trace_pred [e] (conj Xl Xr)).
               specialize D with y z.
               exfalso.
               assert (y=z) as H by (now apply Singleton_inv,D).
               easy.
          * generalize toke;intros toke'.
            rewrite H in toke'.
            destruct a; simpl in *; intuition.
        + destruct rpq as ((y,Hy),(rpq1,(rpq2,rpq3))).
          destruct (exists_last (proj1 (conj Hl toke))) as (e',(le,Hle)); simpl in *.
          destruct (exists_last (proj1 Hy)) as (y',(ly,Hly)); simpl in *.
          destruct He4.
          rewrite rpq2.
          unfold majorant in rpq3.
          assert (cmp (interp_val_es x mu) (exist _ y Hy) (exist _ e (conj Hl toke)))
            by (apply prefix_of_last_added with (X:=proj1_sig p); destruct p as (p,Hp); easy).
          unfold cmp,interp_val_es,lift_rel in H; simpl in H.
          rewrite Hle in H.
          assert (prefix e' y) as T.
          * assert (e' <> []) as L.
            -- intros L.
               rewrite L in H; simpl in H.
               destruct Hy as (Hy1,Hy2).
               destruct y; try easy.
               destruct y; destruct H as (H1,H2),H1; try easy.
               rewrite L in Hle; simpl in Hle.
               assert ((exist (fun xs => MemES.trace_pred x mu xs) [m] (conj Hy1 Hy2))
                       = (exist (fun xs => MemES.trace_pred x mu xs) e (conj Hl toke))) as H by (now apply specif_eq).
               now rewrite H in rpq1.
            -- generalize toke; intro tok.
               rewrite Hle in tok.
               apply trace_ok_pre in tok.
               specialize rpq3 with (exist trace_pred e' (conj L tok)).
               apply rpq3.
               destruct He2 as (D,C); unfold downclosed in D.
               specialize D with (exist trace_pred e (conj Hl toke)) (exist trace_pred e' (conj L tok)).
               assert ((Add _ (proj1_sig p)
                            (exist trace_pred e (conj Hl toke))) (exist trace_pred e' (conj L tok))) as R.
               ++ apply D.
                  ** intuition.
                  ** simpl; unfold lift_rel; simpl.
                     rewrite Hle.
                     apply prefix_app.
               ++ apply Add_inv in R.
                  destruct R;try easy.
                  apply proj1_sig_eq in H0;simpl in H0.
                  rewrite H0 in Hle.
                  rewrite <- app_nil_r in Hle at 1.
                  apply app_inj_l in Hle; congruence.
          * assert (y <> e) as goody.
            -- intros E.
               assert ((exist (fun xs => MemES.trace_pred x mu xs) y Hy)
                       =  (exist (fun xs => MemES.trace_pred x mu xs) e (conj Hl toke)))
                 as E' by (now apply specif_eq).
               now rewrite E' in rpq1.
            -- rewrite Hle in goody.
               apply prefix_extend in H; try easy.
               unfold antisymmetric in ord_antisym.
               apply ord_antisym in H; try easy.
               generalize toke; intros tok.
               rewrite Hle,H,Hly,<-app_assoc in tok.
               now apply trace_ok_next_cand with y'.
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
            now destruct (prefix_order (mem_op U)).
          * destruct rpq as ((y,Hy),(Hy1,(Hy2,Hy3))); simpl in *.
            intros (z,Hz) iz.
            rewrite He1 in iz.
            apply Add_inv in iz.
            destruct iz as [H|H].
            -- assert (cmp (interp_val_es x mu) (exist _ y Hy) (exist _ e (conj Hl toke)))
                by (apply prefix_of_last_added with (X:=proj1_sig p); destruct p as (p,Hp); easy).
               unfold transitive in ord_trans.
               apply ord_trans with y.
               ++ unfold majorant in Hy3; now apply Hy3 in H.
               ++ easy.
            -- apply proj1_sig_eq in H; simpl in H.
               unfold lift_rel; simpl.
               now rewrite H.
    Qed.

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
