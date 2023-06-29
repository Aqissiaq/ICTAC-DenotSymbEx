From Coq Require Import
  String Bool Datatypes Relations Program.Equality Classes.RelationClasses
  Relations.Operators_Properties
  Logic.FunctionalExtensionality (* for equality of substitutions *)
  Ensembles
  Lists.List
.
Import ListNotations.

From BigStepSymbEx Require Import Expr
  Syntax
  Maps
  BigStep
  SmallStep
.
Import While.

Open Scope com_scope.
Open Scope string_scope.
Open Scope list_scope.

(** Substitutions *)
(* Definition 2 *)
Fixpoint acc_subst (t: trace__S) (sig: sub): sub :=
  match t with
  | [] => sig
  | Asgn x e :: t => acc_subst t (x !-> Aapply sig e; sig)
  | _ :: t => acc_subst t sig
  end.

Lemma acc_subst_asgn_last: forall t sig x e,
    acc_subst (t ++ [Asgn x e]) sig = (x !-> Aapply (acc_subst t sig) e ; acc_subst t sig).
Proof.
  induction t; intros.
  - reflexivity.
  - destruct a; simpl.
    + rewrite IHt. reflexivity.
    + apply IHt.
Qed.

Lemma acc_subst_cond_last: forall t sig b,
    acc_subst (t ++ [Cond b]) sig = acc_subst t sig.
Proof.
  induction t; intros.
  - reflexivity.
  - destruct a; simpl; apply IHt.
Qed.

Lemma acc_subst_concat: forall s t sig,
    acc_subst (s ++ t) sig = acc_subst t (acc_subst s sig).
Proof.
  induction s; intros.
  - reflexivity.
  - destruct a; simpl.
    + rewrite IHs. reflexivity.
    + apply IHs.
Qed.

Lemma asgn_acc_subst': forall sig x e V y,
    denot_sub (acc_subst [Asgn x e] id_sub) (denot_sub sig V) y = denot_sub (x !-> Aapply sig e ; sig) V y.
Proof.
  intros. unfold denot_sub; simpl.
  rewrite 2 asgn_sound. rewrite comp_id. reflexivity.
Qed.

Lemma asgn_acc_subst: forall sig x e,
    (fun V => denot_sub (acc_subst [Asgn x e] id_sub) (denot_sub sig V))
    = denot_sub (x !-> Aapply sig e ; sig).
Proof. intros. extensionality V. extensionality y. apply asgn_acc_subst'. Qed.

Lemma acc_subst_comp: forall t sig,
    denot_sub (acc_subst t sig) = fun V => denot_sub (acc_subst t id_sub) (denot_sub sig V).
Proof.
  induction t using rev_ind; intros.
  - simpl. rewrite denot_id_sub. reflexivity.
  - destruct x.
    + rewrite 2 acc_subst_asgn_last.
      rewrite <- 2 asgn_acc_subst.
      rewrite IHt. reflexivity.
    + rewrite 2 acc_subst_cond_last.
      apply IHt.
Qed.

(* Lemma 2 *)
Lemma acc_subst_concat_comp: forall s t,
    denot_sub (acc_subst (s ++ t) id_sub) = fun V => denot_sub (acc_subst t id_sub) (denot_sub (acc_subst s id_sub) V).
Proof.
  intros.
  rewrite acc_subst_concat.
  rewrite acc_subst_comp.
  reflexivity.
Qed.

(** Path Conditions *)
(* Definition 3 *)
Fixpoint acc_pc (t: trace__S) (sig: sub): Bexpr :=
  match t with
  | [] => BTrue
  | Asgn x e :: t => acc_pc t (x !-> Aapply sig e; sig)
  | Cond b :: t => BAnd (Bapply sig b) (acc_pc t sig)
  end.

Lemma acc_pc_asgn_last: forall t sig x e,
    acc_pc (t ++ [Asgn x e]) sig = acc_pc t sig.
Proof.
  induction t; intros.
  - reflexivity.
  - destruct a; simpl.
    + apply IHt.
    + rewrite IHt. reflexivity.
Qed.

Lemma acc_pc_cond_last: forall t sig b,
    denot__B (acc_pc (t ++ [Cond b]) sig) = denot__B (BAnd (acc_pc t sig) (Bapply (acc_subst t sig) b)).
Proof.
  induction t; intros.
  - simpl. rewrite 2 denotB_and.
    apply intersect_comm.
  - destruct a; simpl.
    + rewrite IHt. reflexivity.
    + rewrite denotB_and, IHt.
      rewrite 3 denotB_and, intersect_assoc.
      reflexivity.
Qed.

Lemma intersect_full' {X:Type}: forall A, Intersection X A (Full_set _) = A.
Proof.
  intros. apply Extensionality_Ensembles. split; intros x H.
  - destruct H; assumption.
  - split; [assumption | constructor].
Qed.

Lemma denot_acc_pc_cond: forall b, denot__B (acc_pc [Cond b] id_sub) = denot__B b.
Proof. intros. simpl. rewrite Bapply_id, denotB_and, denotB_top, intersect_full'. auto. Qed.

Lemma concat_pc: forall s t sig,
    denot__B (acc_pc (s ++ t) sig) = denot__B (BAnd (acc_pc s sig) (acc_pc t (acc_subst s sig))).
Proof.
  induction s; intros.
  - simpl. rewrite denotB_and, denotB_top, intersect_full.
    reflexivity.
  - destruct a; simpl.
    + rewrite IHs, denotB_and.
      reflexivity.
    + rewrite 3 denotB_and, IHs, denotB_and.
      rewrite <- intersect_assoc.
      reflexivity.
Qed.

Lemma backwards_comp: forall t sig,
    denot__B (acc_pc t sig) = inverse_image (denot_sub sig) (denot__B (acc_pc t id_sub)).
Proof.
  induction t using rev_ind; intros.
  - simpl. rewrite denotB_top,
      inverse_full.
    reflexivity.
  - destruct x; simpl.
    + rewrite 2 acc_pc_asgn_last. apply IHt.
    + rewrite 2 acc_pc_cond_last.
      rewrite <- inverse_denotB; simpl.
      rewrite 2 denotB_and.
      rewrite 2 (inverse_denotB sig).
      rewrite (inverse_denotB (acc_subst t sig)).
      rewrite (inverse_denotB (acc_subst t id_sub)).
      rewrite inverse_inverse.
      rewrite <- IHt.
      rewrite acc_subst_comp.
      reflexivity.
Qed.

(* Lemma 3 *)
Lemma pc_concat_intersect: forall s t,
    denot__B (acc_pc (s ++ t) id_sub) =
      Intersection _ (denot__B (acc_pc s id_sub)) (inverse_image (denot_sub (acc_subst s id_sub)) (denot__B (acc_pc t id_sub))).
Proof.
  intros.
  rewrite concat_pc.
  rewrite denotB_and.
  rewrite <- backwards_comp.
  reflexivity.
Qed.

(** Theorem 11: big-small step correspondence *)
Definition PHI (t: trace__S): Branch :=
  (denot_sub (acc_subst t id_sub), denot__B (acc_pc t id_sub)).

Definition feasible (t: trace__S): Prop :=
  Inhabited _ (denot__B (acc_pc t id_sub)).

Lemma empty_feasible: feasible [].
Proof. unfold feasible. simpl. rewrite denotB_top.
       apply Inhabited_intro with (x := (_ !-> 0)).
       constructor.
Qed.

Lemma feasible_app: forall s t,
    feasible (s ++ t) -> feasible s /\ feasible t.
Proof.
  destruct s; intros.
  - split.
    + apply empty_feasible.
    + rewrite app_nil_l in H; assumption.
  - unfold feasible; destruct t; simpl; inversion H; subst; split.
    + rewrite pc_concat_intersect in H0. simpl in H0.
      destruct H0. apply Inhabited_intro with (x := x0); assumption.
    + rewrite pc_concat_intersect in H0. simpl in H0.
      destruct H0. set (foo := (denot_sub (acc_subst s (x !-> Aapply id_sub e; id_sub)))).
      apply Inhabited_intro with (x := foo x0); assumption.
    + rewrite pc_concat_intersect in H0; simpl in H0.
      destruct H0. apply Inhabited_intro with (x := x); assumption.
    + rewrite pc_concat_intersect in H0; simpl in H0. destruct H0.
      apply Inhabited_intro with (x := (denot_sub (acc_subst s id_sub)) x); assumption.
Qed.

Lemma small_to_big_loop': forall b p t,
    canonical <{while b {p}}> t ->
    feasible t ->
    (forall t',
      canonical p t' -> feasible t' -> Ensembles.In Branch (denot__S p) (denot_sub (acc_subst t' id_sub), denot__B (acc_pc t' id_sub))) ->
    Ensembles.In Branch (denot__S <{ while b {p} }>) (denot_sub (acc_subst t id_sub), denot__B (acc_pc t id_sub)).
Proof.
  intros. destruct (canonical_loop _ _ _ H) as (m & ts & -> & ?).
  induction m.
  - simpl. rewrite denot_id_sub, denotB_and, denotB_neg, denotB_top, Bapply_id, intersect_full'.
    exists 0. constructor.
  - (* setup for denot_while__S *)
    replace (build_loop_trace b (S m) ts)
      with ([Cond b] ++ ts m ++ build_loop_trace b m ts) by auto.
    rewrite 3 acc_subst_concat_comp.
    replace (acc_subst [Cond <{ ~ b }>] id_sub) with id_sub by auto.
    rewrite <- app_assoc.
    rewrite pc_concat_intersect.
    rewrite <- app_assoc.
    rewrite pc_concat_intersect.
    replace (acc_subst [Cond b] id_sub) with id_sub by auto.
    rewrite denot_id_sub.
    replace (denot__B (acc_pc [Cond b] id_sub)) with (denot__B b)
      by (symmetry; apply denot_acc_pc_cond).

    (* this is entirely unnecessary, but cleans goal up to show how denot_while__S applies *)
    set (F := denot_sub (acc_subst (ts m) id_sub)).
    set (Floop := denot_sub (acc_subst (build_loop_trace b m ts) id_sub)).
    set (B := denot__B (acc_pc (ts m) id_sub)).
    set (Bloop := denot__B (acc_pc (build_loop_trace b m ts ++ [Cond <{ ~ b }>]) id_sub)).

    apply denot_while__S.
    + apply H1.
      * apply H2. auto.
      * replace (build_loop_trace b (S m) ts ++ [Cond <{ ~ b }>])
          with ([Cond b] ++ (ts m) ++ (build_loop_trace b m ts) ++ [Cond <{~ b}>]) in H0
            by (simpl; rewrite <- app_assoc; auto).
        destruct (feasible_app _ _ H0) as (_ & ?).
        destruct (feasible_app _ _ H3) as (? & _).
        assumption.
    + subst Floop. subst Bloop.
      replace (acc_subst (build_loop_trace b m ts ++ [Cond <{ ~ b }>]) id_sub)
                with (acc_subst (build_loop_trace b m ts) id_sub) in IHm
        by (rewrite acc_subst_cond_last; auto).
      apply IHm.
      * replace (build_loop_trace b (S m) ts ++ [Cond <{ ~ b }>])
          with ([Cond b] ++ (ts m) ++ (build_loop_trace b m ts) ++ [Cond <{~ b}>]) in H0
            by (simpl; rewrite <- app_assoc; auto).
        destruct (feasible_app _ _ H0) as (_ & ?).
        destruct (feasible_app _ _ H3) as (_ & ?).
        assumption.
      * apply loop_canonical. intros. apply H2. constructor. apply H3.
      * intros. apply H2. transitivity m. assumption. apply PeanoNat.Nat.lt_succ_diag_r.
Qed.

Theorem small_to_big: forall p t,
    canonical p t ->
    feasible t ->
    Ensembles.In _ (denot__S p) (PHI t).
Proof.
  unfold PHI. induction p; intros.
  - rewrite canonical_skip in H; subst; simpl.
    rewrite denot_id_sub, denotB_top.
    constructor.
  - rewrite canonical_asgn in H; subst; simpl.
    unfold denot_sub.
    assert (F_ext: (fun V => Comp V (x !-> Aapply id_sub e; id_sub))
                   = (fun V => (x !-> Aeval V e; V)))
      by (extensionality V; rewrite asgn_sound, comp_id; reflexivity).
    rewrite F_ext, denotB_top.
    constructor.
  - destruct (sequence_concat _ _ _ H) as (t1 & t2 & Happ & Ht1 & Ht2);
      subst; simpl.
    destruct (feasible_app _ _ H0).
    specialize (IHp1 _ Ht1 H1).
    specialize (IHp2 _ Ht2 H2).
    exists (denot_sub (acc_subst t1 id_sub)).
    exists (denot_sub (acc_subst t2 id_sub)).
    exists (denot__B (acc_pc t1 id_sub)).
    exists (denot__B (acc_pc t2 id_sub)).
    repeat split; try assumption.
    + simpl. apply acc_subst_concat_comp.
    + simpl. rewrite concat_pc, denotB_and.
      rewrite <- backwards_comp.
      reflexivity.
  - rewrite canonical_if in H.
    destruct H as [t' H]. destruct H.
    + destruct H as [Happ Hcanon].
      rewrite Happ in H0.
      destruct (feasible_app _ _ H0).
      specialize (IHp1 _ Hcanon H1).
      subst. left.
      exists (denot_sub (acc_subst t' id_sub)).
      exists (denot__B (acc_pc t' id_sub)).
      repeat split; try assumption.
      * simpl. rewrite denotB_and, Bapply_id.
        apply intersect_comm.
    + destruct H as [Happ Hcanon].
      rewrite Happ in H0.
      destruct (feasible_app _ _ H0).
      specialize (IHp2 _ Hcanon H1).
      subst. right.
      exists (denot_sub (acc_subst t' id_sub)).
      exists (denot__B (acc_pc t' id_sub)).
      repeat split; try assumption.
      * simpl.
        rewrite denotB_and, denotB_neg, Bapply_id.
        apply intersect_comm.
  - apply small_to_big_loop'; assumption.
Qed.

Theorem big_to_small: forall p F B,
    Ensembles.In _ (denot__S p) (F, B) ->
    Inhabited _ B ->
    exists t, canonical p t /\ PHI t = (F, B).
Proof.
  induction p; intros.
  - exists []. split.
    + constructor.
    + inversion H; subst.
      unfold PHI; simpl.
      rewrite denot_id_sub, denotB_top.
      reflexivity.
  - exists [Asgn x e]. split.
    + apply canonical_asgn. reflexivity.
    + inversion H; subst.
      unfold PHI; simpl.
      rewrite denotB_top.
      unfold denot_sub.
      replace (fun V : Valuation => Comp V (x !-> Aapply id_sub e; id_sub))
        with (fun V : total_map => x !-> Aeval V e; V)
        by (extensionality V; rewrite asgn_sound, comp_id; reflexivity).
      reflexivity.
  - destruct H as (F1 & F2 & B1 & B2 & ? & ? & ? & ?).
    simpl in H2, H3. subst.
    inversion H0. destruct H2.
    assert (InB1: Inhabited _ B1) by (apply Inhabited_intro with (x := x); assumption).
    assert (InB2: Inhabited _ B2) by (apply Inhabited_intro with (x := F1 x); assumption).
    destruct (IHp1 _ _ H InB1) as (t1 & Hcanon & HPHI).
    destruct (IHp2 _ _ H1 InB2) as (t2 & Hcanon' & HPHI').
    inversion HPHI; subst. inversion HPHI'; subst.
    exists (t1 ++ t2). split.
    + apply concat_sequence; assumption.
    + unfold PHI.
      rewrite acc_subst_concat_comp.
      rewrite pc_concat_intersect.
      reflexivity.
  - destruct H as [Htrue | Hfalse].
    + destruct Htrue as (F' & B' & Inp1 & ? & ?).
      simpl in H, H1; subst.
      inversion H0. destruct H.
      assert (InB': Inhabited _ B') by (apply Inhabited_intro with (x := x); assumption).
      destruct (IHp1 _ _ Inp1 InB') as (t1 & Hcanon & HPhi).
      exists (Cond b :: t1). split.
      * apply clos_rt1n_rtn1. econstructor.
        -- apply red_cond_true.
        -- simpl.
           replace (Cond b :: t1) with ([Cond b] ++ t1) by reflexivity.
           apply clos_rtn1_rt1n. apply canonical_extends; assumption.
      * inversion HPhi; subst.
        unfold PHI; simpl.
        rewrite denotB_and, Bapply_id, intersect_comm.
        reflexivity.
    + destruct Hfalse as (F' & B' & Inp2 & ? & ?).
      simpl in H, H1; subst.
      inversion H0. destruct H.
      assert (InB': Inhabited _ B') by (apply Inhabited_intro with (x := x); assumption).
      destruct (IHp2 _ _ Inp2 InB') as (t2 & Hcanon & HPhi).
      exists (Cond <{~ b}> :: t2). split.
      * apply clos_rt1n_rtn1. econstructor.
        -- apply red_cond_false.
        -- simpl.
           replace (Cond <{~ b}> :: t2) with ([Cond <{~ b}>] ++ t2) by reflexivity.
           apply clos_rtn1_rt1n. apply canonical_extends; assumption.
      * inversion HPhi; subst.
        unfold PHI; simpl.
        rewrite denotB_and, denotB_neg, Bapply_id, intersect_comm.
        reflexivity.
  - inversion H; subst.
    generalize dependent B.
    generalize dependent F.
    induction i; intros.
    + simpl in H1; inversion H1; subst.
      exists [Cond <{~ b}>]. split.
      * econstructor.
        -- apply red_loop_false with (t := []).
        -- constructor.
      * unfold PHI; simpl.
        rewrite Bapply_id, denotB_and, denotB_top, denotB_neg, denot_id_sub.
        rewrite intersect_full'.
        reflexivity.
    + apply loop_helper_step in H1.
      destruct H1 as (? & ? & ? & ?).
      destruct H2 as (Floop & Bloop & Fbody & Bbody & ? & ? & ? & ?).
      inversion H2. simpl in H4, H5. subst.
      inversion H0. destruct H4. destruct H5.
      assert (InBbody: Inhabited _ Bbody)
        by (apply Inhabited_intro with (x := x); assumption).
      destruct (IHp Fbody Bbody H3 InBbody) as (tBody & ? & PHIbody).
      assert (inBloop: Inhabited _ Bloop)
        by (apply Inhabited_intro with (x := Fbody x); assumption).
      assert (inLoop: Ensembles.In _ (denot__S <{while b {p}}>) (Floop, Bloop))
        by (apply Fam_intro with (i := i); apply H1).
      destruct (IHi Floop Bloop inLoop inBloop H1) as (tLoop & ? & PHIloop).
      exists (Cond b :: tBody ++ tLoop). split.
      * apply canonical_while. exists (tBody ++ tLoop). left. split.
        -- reflexivity.
        -- apply concat_sequence; assumption.
      * inversion PHIbody; subst; inversion PHIloop; subst.
        unfold PHI; simpl.
        rewrite acc_subst_concat_comp.
        rewrite denotB_and, Bapply_id.
        rewrite pc_concat_intersect.
        reflexivity.
Qed.

(* Theorem 2 *)
Theorem big_small_correspondence: forall p,
  (exists F B, Ensembles.In _ (denot__S p) (F, B) /\ Inhabited _ B) <->
    exists t, canonical p t /\ feasible t.
Proof.
  split; intros.
  - destruct H as (F & B & ? & ?).
    destruct (big_to_small _ _ _ H H0) as (t & ? & ?).
    exists t. split.
    + apply H1.
    + inversion H2; subst. apply H0.
  - destruct H as (t &Hcanon & Hfeas).
    specialize (small_to_big _ _ Hcanon Hfeas); intro.
    exists (fst (PHI t)). exists (snd (PHI t)).
    split; assumption.
Qed.
