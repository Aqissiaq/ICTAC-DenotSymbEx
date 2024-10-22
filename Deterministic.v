(** Results about the While language (5.2)*)

(* This file culminates in encoding_deterministic which corresponds to Lemma 9
Before we get there, we need to characterize the denotation of loops, called Fₘ
in the paper proof of lemma 9, and then prove that at most one such Fₘ will be
inhabited. The final proof is necessarily non-constructive, since determining
whether the denotation of a loop is inhabited is essentially the halting
problem. *)
From Coq Require Import
                 Lists.List
                 Ensembles
                 Psatz
                 Arith
                 Classical.
Import ListNotations.

From BigStepSymbEx Require Import
  Utils
  Expr
  Maps
  Syntax
  Traces
  Programs.
Import NonDet WhileNotations Trace.
Open Scope com_scope.

Definition deterministic: Prg -> Prop :=
  fun p => forall V, sub_singleton (denot_fun_nondet p V).

(* this is Fₘ *)
Definition m_loop m b q V :=
  set_compose (n_fold_set m (denot_fun_nondet (PSeq (PAsrt b) q))) (denot_fun_nondet (PAsrt <{~b}>)) V.

Lemma while_m_loop: forall b q V,
    denot_fun_nondet (encode <{while b {q}}>) V = Union_Fam (fun n => m_loop n b (encode q) V).
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; intros ?V ?.
  - destruct H as (?V & ? &?).
    inv H.
    exists i, V1.
    split; auto.
  - inv H.
    destruct H0 as (?V & ? & ?).
    exists V1.
    split; auto.
    exists i; auto.
Qed.

Lemma deterministic_loop_charact: forall m b q V,
    deterministic q ->
    sub_singleton (m_loop m b q V).
Proof.
  induction m; intros.
  - cbn.
    apply sub_singleton_set_compose_first.
    + apply sub_singleton_singleton.
    + intro V0.
      apply sub_singleton_if.
  - cbn.
    apply sub_singleton_set_compose_first;
      [ | intro; apply sub_singleton_if ].
    apply sub_singleton_set_compose_first.
    + apply sub_singleton_set_compose_first.
      * apply sub_singleton_if.
      * apply H.
    + intros ?V.
      apply sub_singleton_n_fold_set.
      intros ?V.
      apply sub_singleton_set_compose_first.
      * apply sub_singleton_if.
      * apply H.
Qed.

(* Fₘ is characterized in terms of finite lists of valuations. For the head and
last functions we provide a default – it is never used, but simplifies the
presentation somehwat *)
Definition Vd : Valuation := (_ !-> 0).

Lemma in_m_loop_charact: forall m b q V V',
    deterministic q ->
    In _ (m_loop m b q V) V' ->
    exists (Vs: list Valuation),
      length Vs = S m
      /\ hd Vd Vs = V
      /\ last Vs Vd = V'
      /\ (last Vs Vd |/= b)
      /\ forall j, j < m -> (nth j Vs Vd |= b) /\ denot_fun_nondet q (nth j Vs Vd) = Singleton _ (nth (S j) Vs Vd).
Proof.
  unfold m_loop.
  induction m; intros.
  - cbn in H0.
    destruct H0 as (?V & ? & ?).
    destruct (Beval V0 b) eqn:?;
      inv H1; inv H0.
    exists [V'].
    splits; auto with datatypes.
    all: lia.
  - cbn in H0.
    destruct H0 as (?V & (?V & (?V & ? & ?) & ?) & ?).
    destruct (Beval V b) eqn:?; inv H0.
    destruct (Beval V0 b) eqn:?; cbn in H3; inv H3.
    pose proof IHm b q V1 V' H as (?Vs & ? & ? & ? & ? & ?).
    {
      exists V'.
      split; auto.
      cbn.
      now rewrite Heqb1.
    }
    assert (Vs <> []). {
      intro.
      rewrite H9 in H4.
      cbn in H4.
      lia.
    }
    exists (V2 :: Vs).
    splits.
    + cbn; now rewrite H4.
    + rewrite <- H6; rewrite last_cons; auto; now apply last_non_empty.
    + rewrite last_cons; auto.
    + destruct j; auto.
      rewrite <- nth_cons; auto.
      pose proof H8 j as (? & _); auto.
      lia.
    + rewrite <- nth_cons; auto.
      destruct j; auto.
      -- cbn.
         replace (nth 0 Vs Vd) with V1 by (destruct Vs; auto).
         pose proof H V2.
         destruct H11 as [ ? | (?V & ?) ].
         ++ rewrite H11 in H1. inv H1.
         ++ rewrite H11 in H1.
            now inv H1.
      -- rewrite <- nth_cons; auto.
         pose proof H8 j as (_&?); auto.
         lia.
Qed.

Corollary singleton_m_loop_charact: forall m b q V V',
    deterministic q ->
    m_loop m b q V = Singleton _ V' ->
    exists (Vs: list Valuation),
      length Vs = S m
      /\ hd Vd Vs = V
      /\ last Vs Vd = V'
      /\ (last Vs Vd |/= b)
      /\ forall j, j < m -> (nth j Vs Vd |= b) /\ denot_fun_nondet q (nth j Vs Vd) = Singleton _ (nth (S j) Vs Vd).
Proof.
  intros.
  assert (In _ (m_loop m b q V) V') by (now rewrite H0).
  now apply in_m_loop_charact.
Qed.

Lemma in_m_loop_charact': forall m b q V V',
    deterministic q ->
    (exists (Vs: list Valuation),
      length Vs = S m
      /\ hd Vd Vs = V
      /\ last Vs Vd = V'
      /\ (last Vs Vd |/= b)
      /\ forall j, j < m -> (nth j Vs Vd |= b) /\ denot_fun_nondet q (nth j Vs Vd) = Singleton _ (nth (S j) Vs Vd)) ->
    In _ (m_loop m b q V) V'.
Proof.
  induction m as [n IHn] using lt_wf_ind;
    intros b q V V' DET (Vs & LEN & HD & LAST & COND & ?).
  destruct n.
  - assert (Vs = [V']) as ->. {
      apply length_one_iff_singl in LEN.
      destruct LEN as (?V & ->).
      inv LAST.
      now cbn.
    }
    exists V.
    split; cbn; try easy.
    cbn in COND.
    cbn in LAST, HD.
    inv HD.
    now rewrite COND.

  - apply length_SSm_iff in LEN.
    destruct LEN as (?V & ?V & Vs' & -> & ?).
    cbn in HD.
    replace ([V0] ++ Vs' ++ [V1]) with ((V0 :: Vs') ++ [V1]) in * by trivial.
    rewrite last_last in COND, LAST.
    subst.
    destruct (length Vs') eqn:?.
    + apply length_zero_iff_nil in Heqn; subst.
      pose proof H 0 as (? & ?); auto.
      cbn in H0, H1.
      exists V'.
      split; auto.
      * exists V'.
        split; cbn; try easy.
        exists V.
        split.
        -- now rewrite H0.
        -- now rewrite H1.
      * cbn.
        now rewrite COND.
    + assert (Vs' <> []). {
        intro.
        apply length_zero_iff_nil in H0.
        lia.
      }
      exists V'.
      split; [ |cbn; now rewrite COND ].
      pose proof H (S n) as (?&?).
      { lia. }
      rewrite app_nth1 in H1, H2.
      rewrite <- Heqn in H1, H2.
      rewrite nth_length_cons in H1, H2; auto.
      rewrite app_nth2 in H2; auto.
      cbn in H2.
      replace (length Vs' - length Vs') with 0 in H2 by lia.
      2,3: cbn; rewrite Heqn; lia.

      pose proof H 0 as (?&?).
      { lia. }
      cbn in H3, H4.
      rewrite app_nth1 in H4; try lia.

      pose proof H 1 as (?&?).
      { lia. }
      rewrite app_nth1 in H5, H6.
      rewrite <- app_comm_cons in H6.
      rewrite <- nth_cons in H5, H6.
      rewrite <- nth_cons in H6.
      all: try auto; try (cbn; rewrite Heqn; lia).
      2: destruct Vs'; easy.
      replace (nth 0 Vs' Vd) with (hd Vd Vs') in * by (destruct Vs'; easy).

      exists (hd Vd Vs').
      split.
      { exists V; split.
        - cbn; now rewrite H3.
        - now rewrite H4.
      }

      epose proof IHn (S n) _ b q (hd Vd Vs') V' DET as (?V & ? & ?).
      {
        exists (Vs' ++ [V']).
        splits; auto.
        - rewrite app_length; cbn; lia.
        - erewrite head_non_empty, head_app; eauto.
          destruct Vs'; easy.
        - erewrite last_non_empty with (d':= V), last_last; auto.
          destruct Vs'; easy.
        - now rewrite last_last.
        - pose proof H (S j) as (?&_).
          { lia. }
          rewrite <- app_comm_cons in H8.
          rewrite <- nth_cons in H8.
          erewrite nth_indep; eauto.
          rewrite app_length, Heqn; lia.
          destruct Vs'; easy.
        - pose proof H (S j) as (_&?).
          { lia. }
          rewrite <- app_comm_cons in H8.
          rewrite <- 2 nth_cons in H8; auto.
          all: destruct Vs'; easy.
      }
      cbn in H8.
      destruct (Beval V0 b); inv H8.
      apply H7.

      Unshelve.
      lia.
Qed.

Corollary singleton_m_loop_charact': forall m b q V V',
    deterministic q ->
    (exists (Vs: list Valuation),
        length Vs = S m
        /\ hd Vd Vs = V
        /\ last Vs Vd = V'
        /\ (last Vs Vd |/= b)
        /\ forall j, j < m -> (nth j Vs Vd |= b) /\ denot_fun_nondet q (nth j Vs Vd) = Singleton _ (nth (S j) Vs Vd)) ->
    m_loop m b q V = Singleton _ V'.
Proof.
  intros.
  apply in_m_loop_charact' in H0; auto.
  destruct (deterministic_loop_charact m b q V H) as [? | (?V & ?)].
  - rewrite H1 in H0.
    inv H0.
  - rewrite H1 in *.
    now inv H0.
Qed.

Theorem m_loop_charact: forall m b q V V',
    deterministic q ->
    (exists (Vs: list Valuation),
        length Vs = S m
        /\ hd Vd Vs = V
        /\ last Vs Vd = V'
        /\ (last Vs Vd |/= b)
        /\ forall j, j < m -> (nth j Vs Vd |= b) /\ denot_fun_nondet q (nth j Vs Vd) = Singleton _ (nth (S j) Vs Vd))
    <-> m_loop m b q V = Singleton _ V'.
Proof.
  split.
  - now apply singleton_m_loop_charact'.
  - now apply singleton_m_loop_charact.
Qed.

Lemma m_loop_unique: forall m b q V V',
    deterministic q ->
    In _ (m_loop m b q V) V' ->
    forall l, m <> l -> m_loop l b q V = Empty_set _.
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; intros ?V ?; [ |contradiction ].
  apply in_m_loop_charact in H0; auto.
  destruct H0 as (?Vs & ?LEN & ?HD & ?LAST & ?COND & ?).
  apply in_m_loop_charact in H2; auto.
  destruct H2 as (?Vs & ?LEN & ?HD & ?LAST & ?COND & ?).
  assert (forall i, i < S m -> i < S l -> nth i Vs Vd = nth i Vs0 Vd). {
    induction i; intros LT1 LT2.
    - replace (nth 0 Vs Vd) with (hd Vd Vs) in * by (destruct Vs; easy).
      replace (nth 0 Vs0 Vd) with (hd Vd Vs0) in * by (destruct Vs0; easy).
      now rewrite HD, HD0.
    - destruct (not_eq _ _ H1).
      + destruct (Nat.le_gt_cases i l); try lia.

        destruct (proj1 (Nat.lt_eq_cases i l) H4);
          [ | rewrite 2 nth_overflow; auto; lia].
        destruct (Nat.le_gt_cases i m); try lia.
        destruct (proj1 (Nat.lt_eq_cases i m) H6).
        * pose proof H0 i H7 as (_&?).
          pose proof H2 i H5 as (_&?).
          rewrite IHi in H8; auto.
          rewrite H8 in H9; auto.
          now apply singleton_inv.
        * subst.
          pose proof H2 m H3 as (?&_).
          rewrite <- IHi in H7; lia.
      + destruct (Nat.le_gt_cases i m); try lia.
        destruct (proj1 (Nat.lt_eq_cases _ _) H4);
            [ | rewrite 2 nth_overflow; auto; lia].
          destruct (Nat.le_gt_cases i l); try lia.
          destruct ((proj1 (Nat.lt_eq_cases _ _) H6)).
             * pose proof H0 i H5 as (_&?).
                pose proof H2 i H7 as (_&?).
                rewrite IHi in H8; auto.
                rewrite H8 in H9; auto.
                now apply singleton_inv.
             * subst.
                pose proof H0 l H3 as (?&_).
                rewrite IHi in H7; lia.
  }
  destruct (not_eq _ _ H1).
  - pose proof H2 m H4 as (?&_).
    rewrite <- H3 in H5; auto.
    pose proof nth_last _ Vs Vd.
    rewrite LEN in H6.
    cbn in H6.
    rewrite <- H6 in H5.
    rewrite H5 in COND.
    discriminate.
    - pose proof H0 l H4 as (?&_).
      rewrite H3 in H5; auto.
      pose proof nth_last _ Vs0 Vd.
      rewrite LEN0 in H6.
      cbn in H6.
      rewrite <- H6 in H5.
      rewrite H5 in COND0.
      discriminate.
Qed.

Theorem encoding_deterministic: forall s,
    deterministic (encode s).
Proof.
  induction s; intros V;
    try apply sub_singleton_singleton.
  - cbn.
    apply sub_singleton_set_compose_first; auto.
  - cbn.
    set (f := (fun V0 : Valuation => if Beval V0 b then Singleton Valuation V0 else Empty_set Valuation)).
    set (f' := (fun V0 : Valuation => if negb (Beval V0 b) then Singleton Valuation V0 else Empty_set Valuation)).
    pose proof set_compose_empty f (denot_fun_nondet (encode s1)) V.
    pose proof set_compose_empty f' (denot_fun_nondet (encode s2)) V.
    pose proof set_compose_singleton_first f (denot_fun_nondet (encode s1)) V.
    pose proof set_compose_singleton_first f' (denot_fun_nondet (encode s2)) V.
    subst f.
    subst f'.
    unfold set_compose in *.
    destruct (Beval V b).
    + rewrite H0; auto.
      rewrite union_unit_r.
      rewrite (H1 V); eauto.
    + rewrite H; auto.
      rewrite union_unit_l.
      rewrite (H2 V); eauto.
  - rewrite while_m_loop.
    (* here we need LEM to solve the halting problem in a poor disguise *)
    destruct (classic (Inhabited _ (Union_Fam (fun n : nat => m_loop n b (encode s) V))))
      as [(?V & ?) | ?]; apply (union_fam_sub_singleton nat_eq_dec).
    + inv H.
      left.
      exists V0, i.
      split.
      * pose proof deterministic_loop_charact i b (encode s) V IHs.
        destruct H1 as [RW | (?V & RW)]; rewrite RW in *; now inv H0.
      * intros; eapply m_loop_unique; eauto.
    + right.
      intros.
      apply Extensionality_Ensembles.
      split; intros ?V ?; [ | contradiction ].
      exfalso.
      apply H.
      now exists V0, i.
Qed.

Type encoding_deterministic.
Print Assumptions encoding_deterministic.
