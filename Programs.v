(** Section 5 and 6: Programs and Symbolic Semantics*)
(* This file contains the developments and results about nondeterministic
programs: the concrete and symbolic semantics of programs and the results
connecting the two. Well-formed (While) programs are handled separately in
Determinism.v*)
From Coq Require Import
                 Bool.Bool
                 Logic.FunctionalExtensionality 
                 Ensembles.

From BigStepSymbEx Require Import
  Utils
  Expr
  Maps
  Syntax
  Traces.

Import NonDet NonDetNotations.
Import Trace.
Open Scope com_scope.

(* Definition 9 *)
Fixpoint denot_fun_nondet (p: Prg) (V: Valuation): Ensemble Valuation :=
  match p with
  | PSkip => Singleton _ V
  | PAsgn x e => Singleton _ (x !-> Aeval V e ; V)
  | PAsrt b => if Beval V b then Singleton _ V else Empty_set _
  | <{p1 (+) p2}> => Union _ (denot_fun_nondet p1 V) (denot_fun_nondet p2 V)
  | <{p*}> => Union_Fam (fun n => n_fold_set n (denot_fun_nondet p) V)
  | PSeq p1 p2 => set_compose (denot_fun_nondet p1) (denot_fun_nondet p2) V
  end.

(* Lemma 7 (unfolding) *)
Lemma unfolding_iterations: forall p,
    denot_fun_nondet <{p*}> = denot_fun_nondet (PChoice PSkip (PSeq p <{p*}>)).
Proof.
  intro.
  extensionality V.
  apply Extensionality_Ensembles.
  split;cbn; intros ? ?.
  - inv H.
    destruct i.
    + inv H0.
      now left.
    + cbn in H0.
      right.
      destruct H0 as (?V & ? & ?).
      exists V0.
      split; auto.
      exists i; auto.
  - destruct H.
    + exists 0; auto.
    + destruct H as (?V & ? & [?n ?V ?]).
      exists (S n).
      eexists V0.
      split; auto.
Qed.

(* Lemma 7 (distributes) *)
Lemma choice_distributes: forall p q r,
    denot_fun_nondet <{(p (+) q) ; r}> = denot_fun_nondet <{(p ; r) (+) (q ; r)}>.
Proof.
  intros.
  extensionality V.
  apply Extensionality_Ensembles.
  split;cbn; intros ?V ?.
  - destruct H as (?V & [?V | ?V] & ?).
    + left.
      now exists V2.
    + right.
      now exists V2.
  - destruct H as [?V | ?V].
    + destruct H as (?V & ? & ?).
      exists V1; split; auto.
      now left.
    + destruct H as (?V & ? & ?).
      exists V1; split; auto.
      now right.
Qed.

Lemma denot_fun_unit_l: forall t, denot_fun t = denot_fun (TSeq TSkip t).
Proof. destruct t; auto. Qed.

Lemma denot_fun_unit_r: forall t, denot_fun t = denot_fun (TSeq t TSkip).
Proof.
  intro.
  extensionality V.
  generalize dependent V.
  induction t; auto.
  - intros; cbn.
    now destruct (Beval V b).
  - simpl; intro.
    destruct (denot_fun t1 V); simpl; auto.
    destruct (denot_fun t2 v); simpl; auto.
Qed.

Fixpoint n_fold_seq (n:nat) (ts: Ensemble Trc): Ensemble Trc :=
  match n with
  | 0 => Singleton _ TSkip
  | S n => fun t => exists u v,
              In _ ts u
              /\ In _ (n_fold_seq n ts) v
              /\  t = TSeq u v
  end.

(* Definition 10 *)
Fixpoint traces_of (p:Prg): Ensemble Trc :=
  match p with
  | PSkip => Singleton _ TSkip
  | PAsgn x e => Singleton _ (TAsgn x e)
  | PAsrt b => Singleton _ (TAsrt b)
  | <{p1 (+) p2}> => Union _ (traces_of p1) (traces_of p2)
  | <{p*}> => Union_Fam (fun n => n_fold_seq n (traces_of p))
  | PSeq p1 p2 => fun x => exists t u, In _ (traces_of p1) t /\ In _ (traces_of p2) u /\ x = TSeq t u
  end.

Lemma traces_of_loop_step: forall p n u v,
    In _ (traces_of p) u ->
    In _ (n_fold_seq n (traces_of p)) v ->
    In _ (n_fold_seq (S n) (traces_of p)) (TSeq u v).
Proof.
  induction n; intros.
  - cbn in *.
    inv H0.
    exists u, TSkip.
    split; auto.
  - destruct H0 as (?u & ?v & (? & ? & ->)).
    pose proof IHn _ _ H H1.
    exists u, (TSeq u0 v0).
    split; auto.
Qed.

(* Lemma 8 *)
Lemma traces_of_correspondence: forall p V,
    denot_fun_nondet p V = (fun V' => exists t, denot_fun t V = Some V' /\ In _ (traces_of p) t).
Proof.
  intros.
  apply Extensionality_Ensembles.
  generalize dependent V.
  induction p; intros.
  - split; intros ? ?.
    + inv H.
      exists TSkip.
      split; easy.
    + destruct H as (t & ? & ?).
      inv H0.
      now inv H.
  - split; intros ? ?.
    + inv H.
      exists (TAsgn x e).
      split; easy.
    + destruct H as (t & ? & ?).
      inv H0.
      now inv H.
  - split; intros ? ?.
    + cbn in H.
      destruct (Beval V b) eqn:?.
      * inv H.
        exists (TAsrt b).
        split; cbn.
        now rewrite Heqb0.
        easy.
      * inv H.
    + destruct H as (t & ? & ?).
      inv H0.
      cbn in *.
      destruct (Beval V b); [ |discriminate].
      now inv H.
  - split; intros ? ?.
    + destruct H as (?V & ? & ?).
      apply IHp1 in H.
      apply IHp2 in H0.
      destruct H as (?t & ? & ?).
      destruct H0 as (?t & ? & ?).
      exists (TSeq t t0).
      split.
      * cbn.
        now rewrite H.
      * exists t, t0.
        split; auto.
    + destruct H as (?t & ? & ?).
      destruct H0 as (u & v & ? & ? & ->).
      cbn in *.
      destruct (option_inversion H) as (?V & ? & ?).
      assert (exists t, denot_fun t V = Some V0 /\ In _ (traces_of p1) t). {
        exists u.
        split; auto.
      }
      apply IHp1 in H4.
      assert (exists t, denot_fun t V0 = Some x /\ In _ (traces_of p2) t). {
        exists v.
        split; auto.
      }
      apply IHp2 in H5.
      eexists V0.
      split; auto.
  - split; intros ? ?.
    + destruct H.
      * apply IHp1 in H.
        destruct H as (?t & ? & ?).
        exists t.
        split; auto.
        now left.
      * apply IHp2 in H.
        destruct H as (?t & ? & ?).
        exists t.
        split; auto.
        now right.
    + destruct H as (?t & ? & ?).
      destruct H0.
      * assert (exists t, denot_fun t V = Some x /\ In _ (traces_of p1) t). {
          exists x0.
          split; auto.
        }
        apply IHp1 in H1.
        now left.
      * assert (exists t, denot_fun t V = Some x /\ In _ (traces_of p2) t). {
          exists x0.
          split; auto.
        }
        apply IHp2 in H1.
        now right.
  - split; intros ? ?.
    + destruct H as [?n ?V ?].
      generalize dependent V0.
      generalize dependent V.
      induction n; intros.
      * cbn in H; inv H.
        exists TSkip.
        split; auto.
        exists 0; cbn; easy.

      * destruct H as (?V & ? & ?).
        destruct (IHp V) as (? & _).
        destruct (H1 _ H) as (?t & ? & ?).

        destruct (IHn _ _ H0) as (?t & ? & ?).
        exists (TSeq t t0).
        split.
        -- simpl.
           rewrite H2; auto.
        -- destruct H5 as [?n ? ?].
           exists (S n0).
           now apply traces_of_loop_step.
    + destruct H as (?t & ? & ?).
      destruct H0 as [?n ? ?].
      generalize dependent x0.
      generalize dependent x.
      generalize dependent V.
      induction n; intros.
      * cbn in H0.
        inv H0.
        inv H.
        exists 0; now cbn.
      * destruct H0 as (?u & ?v & ? & ? & ->).
        cbn in H.
        destruct (option_inversion H) as (?V & ? & ?).
        pose proof IHn _ _ _ H3 H1.
        destruct H4 as [?n ? ?].

        pose proof IHp V as (_&?).
        assert (exists t : Trc, denot_fun t V = Some V0 /\ In Trc (traces_of p) t).
        {
          exists u.
          split; auto.
        }
        apply H5 in H6.

        exists (S n0).
        exists V0.
        split; auto.
(* this proof is very ugly, but goes through *)
Qed.

(** Symbolic Semantics *)
Lemma denot_sub_sound: forall sigma V e,
    Aeval (denot_sub sigma V) e = Aeval V (Aapply sigma e).
Proof. unfold denot_sub. intros. apply comp_sub. Qed.

Lemma inverse_denotB: forall s b,
    denot__B (Bapply s b) = inverse_image (denot_sub s) (denot__B b).
Proof.
  intros. induction b.
  - simpl. rewrite denotB_top. rewrite inverse_full. reflexivity.
  - simpl. rewrite denotB_bot. rewrite inverse_empty. reflexivity.
  - simpl. rewrite 2 denotB_neg. rewrite IHb. rewrite inverse_complement. reflexivity.
  - simpl. rewrite 2 denotB_and. rewrite IHb1, IHb2. rewrite inverse_intersection. reflexivity.
  - apply Extensionality_Ensembles. split; intros V H.
    + inversion H. rewrite <- 2 denot_sub_sound in H1.
      unfold inverse_image, In. unfold denot_sub. apply H1.
    + inversion H.
      unfold denot__B, Ensembles.In. simpl. unfold denot_sub in H1.
      rewrite <- 2 comp_sub. apply H1.
Qed.

Definition Branch: Type := sub * Bexpr.

(* Definition 11 *)
Definition denot__S (p: Prg): Ensemble Branch :=
  fun '(s, b) => exists t, In _ (traces_of p) t /\ s = Sub t /\ b = PC t.

Lemma Sub_skip_unit_l: forall t,
    Sub (TSeq TSkip t) = Sub t.
Proof.
  intros.
  unfold Sub.
  cbn.
  destruct (trace_denot__S t); cbn.
  now rewrite compose_subs_id.
Qed.

Lemma Sub_skip_unit_r: forall t,
    Sub (TSeq t TSkip) = Sub t.
Proof.
  intros.
  unfold Sub.
  cbn.
  destruct (trace_denot__S t); cbn.
  now rewrite compose_subs_id'.
Qed.

Lemma sub_trace_app: forall u v,
    Sub (TSeq u v) = compose_subs (Sub u) (Sub v).
Proof.
  destruct u,v; cbn; auto.
  - now rewrite compose_subs_id, Sub_skip_unit_l.
  - unfold Sub; cbn.
    now destruct (trace_denot__S v1), (trace_denot__S v2); cbn.
  - unfold Sub; cbn.
    now destruct (trace_denot__S v1), (trace_denot__S v2); cbn.
  - now rewrite compose_subs_id', Sub_skip_unit_r.
  - unfold Sub; cbn.
    now destruct (trace_denot__S u1), (trace_denot__S u2); cbn.
  - unfold Sub; cbn.
    now destruct (trace_denot__S u1), (trace_denot__S u2); cbn.
  - unfold Sub; cbn.
    now destruct (trace_denot__S u1), (trace_denot__S u2),
      (trace_denot__S v1), (trace_denot__S v2) ; cbn.
Qed.

Lemma pc_trace_app: forall u v,
    PC (TSeq u v) =  BAnd (PC u) (Bapply (Sub u) (PC v)).
Proof.
  destruct u,v; unfold PC; cbn; auto;
    try (destruct (trace_denot__S v1) eqn:?, (trace_denot__S v2) eqn:?; cbn; auto);
    destruct (trace_denot__S u1) eqn:?, (trace_denot__S u2) eqn:?; cbn; auto.
  - pose proof Sub_spec_correct (TSeq u1 u2) as (?&_).
    specialize (H eq_refl).
    inv H.
    apply Sub_spec_correct in H3, H4.
    unfold Sub in H3, H4.
    rewrite Heqp in H3.
    rewrite Heqp0 in H4.
    now simpl in *; subst.

  - pose proof Sub_spec_correct (TSeq u1 u2) as (?&_).
    specialize (H eq_refl).
    inv H.
    apply Sub_spec_correct in H3, H4.
    unfold Sub in H3, H4.
    rewrite Heqp1 in H3.
    rewrite Heqp2 in H4.

    pose proof Sub_spec_correct (TSeq v1 v2) as (?&_).
    specialize (H0 eq_refl).
    inv H0.
    apply Sub_spec_correct in H7, H8.
    unfold Sub in H7, H8.
    rewrite Heqp in H7.
    rewrite Heqp0 in H8.
    now simpl in *; subst.
Qed.

(* Lemma 10 in four parts *)
(*10 (i)*)
Lemma denotS_spec_seq: forall p q,
    denot__S (PSeq p q) = fun '(σ, φ) => exists σp σq φp φq,
                            In _ (denot__S p) (σp, φp)
                            /\ In _ (denot__S q) (σq, φq)
                            /\ σ = compose_subs σp σq
                            /\ φ = BAnd φp (Bapply σp φq).
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; intros ? ?.
  - destruct x.
    destruct H as (t & ? & -> & ->).
    destruct H as (u & v & ? & ? & ->).
    eexists.
    eexists.
    eexists.
    eexists.
    splits.
    + eexists.
      splits; eauto.
    + eexists.
      splits; eauto.
    + apply sub_trace_app.
    + apply pc_trace_app.

  - destruct x.
    destruct H as (σp & σq & φp & φq & ? & ? & -> & ?).
    destruct H as (tp & ? & -> & ->).
    destruct H0 as (tq & ? & -> & ->).
    eexists (TSeq tp tq).
    splits.
    + eexists.
      eexists.
      splits; auto.
    + now rewrite sub_trace_app.
    + now rewrite H1, pc_trace_app.
Qed.

(*10 (ii)*)
Lemma denotS_spec_choice: forall p q,
    denot__S (PChoice p q) = Union _ (denot__S p) (denot__S q).
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; intros ? ?.
  - destruct x.
    destruct H as (t & ? & -> & ->).
    destruct H.
    + left.
      eexists.
      splits; auto.
    + right.
      eexists.
      splits; auto.
  - destruct H.
    + destruct x.
      destruct H as (t & ? & -> & ->).
      eexists.
      splits; eauto.
      now left.
    + destruct x.
      destruct H as (t & ? & -> & ->).
      eexists.
      splits; eauto.
      now right.
Qed.

(* For (iii) we need to define the n-fold composition of a program also note
 that the formulation of denotS_spec_ind does not include an extra TSkip, since
 this is the 0-case of n_fold_PSeq *)
Fixpoint n_fold_PSeq (n:nat) (p:Prg): Prg :=
  match n with
  | 0 => PSkip
  | S n => PSeq p (n_fold_PSeq n p)
  end.

Lemma n_fold_prg_trace: forall n p t,
    In _ (n_fold_seq n (traces_of p)) t <->
    In _ (traces_of (n_fold_PSeq n p)) t.
Proof.
  induction n; split; intros; try easy.
  - destruct H as (?u & ?v & ? & ? & ->).
    exists u, v.
    splits; auto.
    now apply IHn.
  - destruct H as (?u & ?v & ? & ? & ->).
    exists u, v.
    splits; auto.
    now apply IHn.
Qed.

(* 10 (iii)*)
Lemma denotS_spec_ind: forall p,
    denot__S (PStar p) = Union_Fam (fun n:nat => denot__S (n_fold_PSeq n p)).
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; intros ? ?.
  - destruct x.
    destruct H as (t & ? & -> & ->).
    inv H.
    exists i, t.
    splits.
    now apply n_fold_prg_trace.
  - destruct H.
    destruct x.
    destruct H as (t & ? & -> & ->).
    exists t.
    splits.
    exists i.
    now apply n_fold_prg_trace.
Qed.

(* 10 (iv)*)
Lemma denotS_spec_unfold: forall p,
    denot__S (PStar p) = Union _ (denot__S PSkip) (denot__S (PSeq p (PStar p))).
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; intros ? ?.
  - destruct x.
    destruct H as (t & ? & -> & ->).
    inv H.
    destruct i.
    + left.
      inv H0.
      eexists.
      splits; eauto.
    + destruct H0 as (u & v & ? & ? & ->).
      right.
      eexists.
      splits; eauto.
      exists u, v.
      splits; auto.
      eexists.
      apply H1.
  - destruct H.
    + destruct x.
      destruct H as (t & ? & -> & ->).
      inv H.
      eexists.
      splits; auto.
      exists 0; auto.
    + destruct x.
      destruct H as (t & ? & -> & ->).
      destruct H as (u & v & ? & ? & ->).
      exists (TSeq u v).
      splits.
      inv H0.
      exists (S i).
      exists u, v.
      splits; auto.
Qed.

(* Theorem 2: in two parts *)
Lemma SE_complete: forall p V V',
    In _ (denot_fun_nondet p V) V' ->
    exists s b,
      In _ (denot__S p) (s, b)
      /\ (V |= b)
      /\ ([| s |] V = V').
Proof.
  intros.
  rewrite traces_of_correspondence in H.
  destruct H as (?t & TRACE_DENOT & IN).
  apply trace_correspondence in TRACE_DENOT.

  exists (Sub t), (PC t).
  split; auto.
  exists t.
  split; auto.
Qed.

Lemma SE_correct: forall p V s b,
    In _ (denot__S p) (s, b) ->
    V |= b ->
    In _ (denot_fun_nondet p V) ([| s |] V).
Proof.
  intros.
  cbn in H.
  destruct H as (?t & ? & -> & ->).
  rewrite traces_of_correspondence.
  exists t.
  split; auto.
  apply trace_correspondence_aux in H0.
  now apply trace_sub_correct.
Qed.

Type SE_correct.
Print Assumptions SE_correct.

Type SE_complete.
Print Assumptions SE_complete.
