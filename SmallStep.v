From Coq Require Import
  String Bool Datatypes Relations Program.Equality Classes.RelationClasses
  Relations.Operators_Properties
  Logic.FunctionalExtensionality (* for equality of substitutions *)
  Ensembles
  Init.Datatypes
  Lists.List
.
Import ListNotations.

From BigStepSymbEx Require Import
  Expr
  Syntax
  Maps
.
Import While.

Open Scope com_scope.
Open Scope string_scope.
Open Scope list_scope.

Section RelationHelpers.
  Variable A: Type.
  Variable R: relation A.

  Lemma clos_rtn1_rt1n: forall x y,
      clos_refl_trans_n1 _ R x y -> clos_refl_trans_1n _ R x y.
  Proof. intros. apply clos_rt_rt1n. apply clos_rtn1_rt. apply H. Qed.

  Lemma clos_rt1n_rtn1: forall x y,
      clos_refl_trans_1n _ R x y -> clos_refl_trans_n1 _ R x y.
  Proof. intros. apply clos_rt_rtn1. apply clos_rt1n_rt. apply H. Qed.

  Lemma clos_rt1n_rtn1_iff: forall x y,
      clos_refl_trans_1n _ R x y <-> clos_refl_trans_n1 _ R x y.
  Proof. split; [apply clos_rt1n_rtn1 | apply clos_rtn1_rt1n]. Qed.

  Global Instance clos_rtn1_trans: Transitive (clos_refl_trans_n1 _ R).
  Proof.
    intros x y z H0 H1.
    apply clos_rtn1_rt in H0, H1.
    apply clos_rt_rtn1.
    apply rt_trans with (y := y); assumption.
  Qed.
End RelationHelpers.

Section ListHelpers.
  Variable A : Type.

  Lemma app_tail_inj: forall (t1 t2 t2': list A),
      t1 ++ t2 = t1 ++ t2' -> t2 = t2'.
  Proof.
    induction t1; intros.
    - apply H.
    - simpl in H. inversion H.
      apply IHt1; assumption.
  Qed.

  Lemma app_nil_unique_r: forall (t1 t2: list A),
      t1 = t1 ++ t2 -> t2 = [].
  Proof.
    induction t1; intros.
    - rewrite H. auto.
    - inversion H. apply IHt1; assumption.
  Qed.

  Lemma app_nil_unique_l: forall (t1 t2: list A),
      t1 = t2 ++ t1 -> t2 = [].
  Proof.
    induction t1; intros.
    - rewrite app_nil_r in H. auto.
    - destruct t2; auto.
      inversion H; subst. replace (t2 ++ a0 :: t1) with ((t2 ++ [a0]) ++ t1) in H2.
      + apply IHt1 in H2. destruct (app_eq_nil _ _ H2); subst; assumption.
      + rewrite <- app_assoc. auto.
  Qed.
End ListHelpers.

Inductive trace_step: Type :=
| Asgn (x:string) (e:Aexpr)
| Cond (b:Bexpr).

Definition trace__S := list trace_step.

Inductive red__S: (trace__S * Stmt) -> (trace__S * Stmt) -> Prop :=
| red_asgn: forall t x e,
    red__S (t, <{ x := e }>) (t ++ [Asgn x e], SSkip)
| red_cond_true: forall t b p1 p2,
    red__S (t, <{ if b {p1} {p2} }>) (t ++ [Cond b], p1)
| red_cond_false: forall t b p1 p2,
    red__S (t, <{ if b {p1} {p2} }>) (t ++ [Cond (BNot b)], p2)
| red_loop_true: forall t b p,
    red__S (t, <{ while b {p} }>) (t ++ [Cond b], <{p ; while b {p}}>)
| red_loop_false: forall t b p,
    red__S (t, <{ while b {p} }>) (t ++ [Cond (BNot b)], SSkip)
| red_skip: forall t p,
    red__S (t, <{skip ; p}>) (t, p)
| red_seq: forall p p' t t' q,
    red__S (t, p) (t', p') ->
    red__S (t, <{p ; q}>) (t', <{p' ; q}>)
.
Definition red_star__S := clos_refl_trans_n1 _ red__S.

Notation " c '->*' c'" := (red_star__S c c') (at level 40).

Lemma trace_extends_step: forall p q s t,
    red__S (s, p) (t, q) -> exists t', t = s ++ t'.
Proof.
  intros. dependent induction H.
  - exists [Asgn x e]. reflexivity.
  - exists [Cond b]. reflexivity.
  - exists [Cond <{~ b}>]. reflexivity.
  - exists [Cond b]. reflexivity.
  - exists [Cond <{~ b}>]. reflexivity.
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct (IHred__S p0 p' s t) as [t' H']; try reflexivity.
    exists t'. apply H'.
Qed.

(* Lemma 3 *)
Lemma trace_extends: forall p q s t,
    (s, p) ->* (t, q) -> exists t', t = s ++ t'.
Proof.
  intros. dependent induction H.
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct y.
    destruct (trace_extends_step _ _ _ _ H) as [tStep Hstep].
    destruct (IHclos_refl_trans_n1 p s0 s t0 eq_refl eq_refl) as [tIH IH].
    exists (tIH ++ tStep). subst. rewrite app_assoc. reflexivity.
Qed.

Lemma trace_extends_cons: forall p q x s t,
    (x :: s, p) ->* (t, q) -> exists t', t = x :: t'.
Proof.
  intros. destruct (trace_extends _ _ (x::s) _ H); subst.
  exists (s ++ x0). reflexivity.
Qed.

Lemma trans_append: forall p q r s t,
    ([], p) ->* (s, q) ->
    (s, q) ->* (t, r) ->
    exists t', ([], p) ->* (s ++ t', r) /\ t = s ++ t'.
Proof.
  intros.
  destruct (trace_extends _ _ _ _ H0) as [t' Happ].
  exists t'. rewrite Happ in H0. split.
  - transitivity (s, q); assumption.
  - assumption.
Qed.

Definition canonical (p: Stmt): trace__S -> Prop :=
  fun t => ([], p) ->* (t, SSkip).

Lemma empty_to_empty: forall p q t0,
    (t0, p) ->* ([], q) -> t0 = [].
Proof.
  intros. destruct (trace_extends _ _ _ _ H).
  destruct x, t0;
    try reflexivity.
  - rewrite app_nil_r in H0. apply nil_cons in H0; contradiction.
    - apply app_cons_not_nil in H0. contradiction.
Qed.

Lemma empty_to_empty_step: forall p q t0,
    red__S (t0, p) ([], q) -> t0 = [].
Proof.
  intros. apply (empty_to_empty p q).
  econstructor.
  - apply H.
  - constructor.
Qed.

Lemma skip_terminates: forall t y,
    ~ (red__S (t, SSkip) y).
Proof.
  intros t y contra.
  inversion contra; subst.
Qed.

Lemma skip_non_productive: forall p s t,
    (s, SSkip) ->* (t, p) -> t = s /\ p = SSkip.
Proof.
  intros. apply clos_rtn1_rt1n in H. inversion H; subst.
  - split; reflexivity.
  - exfalso. apply (skip_terminates s y H0).
Qed.

Lemma prefix_step: forall s t p q,
    red__S (s, p) (t, q) ->
    forall t0, red__S (t0 ++ s, p) (t0 ++ t, q).
Proof.
  intros. dependent induction H;
    try (rewrite app_assoc; constructor).
  - apply red_skip.
  - apply red_seq. apply IHred__S; reflexivity.
Qed.

Lemma prefix_star: forall s t p q,
    (s, p) ->* (t, q) ->
    forall t0, (t0 ++ s, p) ->* (t0 ++ t, q).
Proof.
  intros. dependent induction H.
  - constructor.
  - destruct y. apply prefix_step with (t0 := t0) in H.
    specialize (IHclos_refl_trans_n1 s t1 p s0 eq_refl eq_refl t0).
    econstructor;
      [apply H | apply IHclos_refl_trans_n1].
Qed.

Lemma canonical_extends: forall p s t,
    canonical p t -> (s, p) ->* (s ++ t, SSkip).
Proof.
  intros.
  specialize (prefix_star _ _ _ _ H s). simpl; intros.
  rewrite app_nil_r in H0; assumption.
Qed.

Lemma sequence_star: forall p p' t t' q,
    (t, p) ->* (t', p') ->
    (t, <{p ; q}>) ->* (t', <{p' ; q}>).
Proof.
  intros. dependent induction H.
  - constructor.
  - destruct y.
    econstructor.
    + apply red_seq. apply H.
    + apply (IHclos_refl_trans_n1 p s t t0); reflexivity.
Qed.

Lemma prefix_irrelevant_step: forall x t t' p p',
    red__S (x :: t, p) (x :: t', p') ->
    red__S (t, p) (t', p').
Proof.
  intros. dependent induction H;
    try constructor.
  apply (IHred__S x); reflexivity.
Qed.

Lemma prefix_irrelevant_cons: forall x t t' p p',
    (x :: t, p) ->* (x :: t', p') ->
    (t, p) ->* (t', p').
Proof.
  intros. dependent induction H; subst.
  - constructor.
  - destruct y. apply trace_extends_cons in H0.
    destruct H0; subst.
    apply prefix_irrelevant_step in H.
    econstructor.
    + apply H.
    + apply (IHclos_refl_trans_n1 x); reflexivity.
Qed.

Lemma prefix_irrelevant: forall s t t' p p',
    (s ++ t, p) ->* (s ++ t', p') ->
    (t, p) ->* (t', p').
Proof.
  induction s; intros.
  - apply H.
  - simpl in H. apply prefix_irrelevant_cons in H.
    apply IHs. apply H.
Qed.

Lemma canonical_skip: forall t, canonical SSkip t <-> t = [].
Proof.
  split; intros.
  - apply clos_rtn1_rt in H. apply clos_rt_rt1n in H.
    inversion H; subst.
    + reflexivity.
    + inversion H0; subst.
  - subst. constructor.
Qed.

Lemma canonical_asgn: forall t x e, canonical <{x := e}> t <-> t = [Asgn x e].
Proof.
  split; intros.
  - apply clos_rtn1_rt1n in H. inversion H; subst.
    inversion H0; subst. apply clos_rt1n_rtn1 in H1.
    destruct (skip_non_productive _ _ _ H1).
    assumption.
  - subst. econstructor.
    + apply red_asgn with (t := []).
    + constructor.
Qed.

Lemma canonical_if: forall b p1 p2 t,
    canonical <{if b {p1} {p2}}> t <-> exists t',
      (t = [Cond b] ++ t' /\ canonical p1 t')
      \/ (t = [Cond <{ ~b }>] ++ t' /\ canonical p2 t').
Proof.
  split; intros.
  - apply clos_rtn1_rt1n in H. inversion H. inversion H0; subst.
    + apply clos_rt1n_rtn1 in H1.
      assert (([], <{if b {p1}{p2}}>) ->* ([Cond b], p1)). {
        econstructor. apply H0. constructor. }
      destruct (trans_append _ _ _ _ _ H2 H1) as (t' & Hcomp & ?).
      exists t'. left. split.
      * assumption.
      * apply (prefix_irrelevant [Cond b]).
        rewrite H3 in H1. simpl in H1.
        simpl. apply H1.
    + apply clos_rt1n_rtn1 in H1.
      assert (([], <{if b {p1}{p2}}>) ->* ([Cond <{~b}>], p2)). {
        econstructor. apply H0. constructor. }
      destruct (trans_append _ _ _ _ _ H2 H1) as (t' & Hcomp & ?).
      exists t'. right. split.
      * assumption.
      * apply (prefix_irrelevant [Cond <{~b}>]).
        rewrite H3 in H1. simpl in H1.
        simpl. apply H1.
  - destruct H as [t' H]. destruct H.
    + destruct H; subst.
      apply clos_rt1n_rtn1. econstructor.
      * apply red_cond_true.
      * apply clos_rtn1_rt1n. apply (prefix_star _ _ _ _ H0 [Cond b]).
    + destruct H; subst.
      apply clos_rt1n_rtn1. econstructor.
      * apply red_cond_false.
      * apply clos_rtn1_rt1n. apply (prefix_star _ _ _ _ H0 [Cond <{~b}>]).
Qed.

Lemma canonical_while: forall b p t,
    canonical <{while b {p}}> t <-> exists t',
      (t = [Cond b] ++ t' /\ canonical <{p ; while b {p}}> t')
      \/ (t = [Cond <{ ~b }>]).
Proof.
  split; intros.
  - apply clos_rtn1_rt1n in H. inversion H. inversion H0; subst.
    + apply clos_rt1n_rtn1 in H1.
      assert (([], <{while b {p}}>) ->* ([Cond b], <{p ; while b {p}}>)). {
        econstructor. apply H0. constructor. }
      destruct (trans_append _ _ _ _ _ H2 H1) as (t' & Hcomp & ?).
      exists t'. left. split.
      * assumption.
      * apply (prefix_irrelevant [Cond b]).
        rewrite H3 in H1. simpl in H1.
        simpl. apply H1.
    + exists [Cond <{~ b}>]. right.
      apply clos_rt1n_rtn1 in H1.
      apply skip_non_productive in H1.
      destruct H1; subst.
      reflexivity.
  - destruct H as [t' H]. destruct H.
    + destruct H; subst.
      apply clos_rt1n_rtn1. econstructor.
      * apply red_loop_true.
      * apply clos_rtn1_rt1n. apply (prefix_star _ _ _ _ H0 [Cond b]).
    + subst.
      apply clos_rt1n_rtn1. econstructor.
      * apply red_loop_false.
      * constructor.
Qed.

(* Lemma 5i *)
Lemma concat_sequence: forall p q s t,
    canonical p s -> canonical q t ->
    canonical <{p ; q}> (s ++ t).
Proof.
  intros. apply clos_rt_rtn1. apply rt_trans with (y := (s, <{skip ; q}>)).
  - apply clos_rtn1_rt. apply sequence_star. apply H.
  - apply clos_rt1n_rt. econstructor.
    + apply red_skip.
    + apply clos_rt_rt1n. apply clos_rtn1_rt.
      specialize (prefix_star _ _ _ _ H0 s). intros.
      rewrite app_nil_r in H1. apply H1.
Qed.

Lemma sequence_splits_step: forall p p' q s t u,
    red__S (s, <{p ; q}>) (t, <{p' ; q}>) ->
    (t, <{p' ; q}>) ->* (u, SSkip) ->
    exists t',
      u = t ++ t'
      /\ ([], <{p' ; q}>) ->* (t', SSkip).
Proof.
  intros. inversion H; subst.
  - apply seq_discriminate2 in H6. contradiction.
  - inversion H2; subst.
    + destruct (trace_extends _ _ _ _ H0); subst.
      exists x0. split.
      * reflexivity.
      * replace (s ++ [Asgn x e]) with ((s ++ [Asgn x e]) ++ []) in H0
            by (rewrite app_nil_r; reflexivity).
        replace (((s ++ [Asgn x e]) ++ []) ++ x0) with ((s ++ [Asgn x e]) ++ x0) in H0
            by (rewrite app_nil_r; reflexivity).
        apply (prefix_irrelevant (s ++ [Asgn x e]) [] x0 _ _ H0).
    + destruct (trace_extends _ _ _ _ H0); subst.
      exists x. split.
      * reflexivity.
      * replace (s ++ [Cond b]) with ((s ++ [Cond b]) ++ []) in H0
            by (rewrite app_nil_r; reflexivity).
        replace (((s ++ [Cond b]) ++ []) ++ x) with ((s ++ [Cond b]) ++ x) in H0
            by (rewrite app_nil_r; reflexivity).
        apply (prefix_irrelevant (s ++ [Cond b]) [] x _ _ H0).
    + destruct (trace_extends _ _ _ _ H0); subst.
      exists x. split.
      * reflexivity.
      * replace (s ++ [Cond <{~b}>]) with ((s ++ [Cond <{~b}>]) ++ []) in H0
            by (rewrite app_nil_r; reflexivity).
        replace (((s ++ [Cond <{~b}>]) ++ []) ++ x) with ((s ++ [Cond <{~b}>]) ++ x) in H0
            by (rewrite app_nil_r; reflexivity).
        apply (prefix_irrelevant (s ++ [Cond <{~b}>]) [] x _ _ H0).
    + destruct (trace_extends _ _ _ _ H0); subst.
      exists x. split.
      * reflexivity.
      * replace (s ++ [Cond b]) with ((s ++ [Cond b]) ++ []) in H0
            by (rewrite app_nil_r; reflexivity).
        replace (((s ++ [Cond b]) ++ []) ++ x) with ((s ++ [Cond b]) ++ x) in H0
            by (rewrite app_nil_r; reflexivity).
        apply (prefix_irrelevant (s ++ [Cond b]) [] x _ _ H0).
    + destruct (trace_extends _ _ _ _ H0); subst.
      exists x. split.
      * reflexivity.
      * replace (s ++ [Cond <{~b}>]) with ((s ++ [Cond <{~b}>]) ++ []) in H0
            by (rewrite app_nil_r; reflexivity).
        replace (((s ++ [Cond <{~b}>]) ++ []) ++ x) with ((s ++ [Cond <{~b}>]) ++ x) in H0
            by (rewrite app_nil_r; reflexivity).
        apply (prefix_irrelevant (s ++ [Cond <{~b}>]) [] x _ _ H0).
    + destruct (trace_extends _ _ _ _ H0); subst.
      exists x. split.
      * reflexivity.
      * replace t with (t ++ []) in H0
            by (rewrite <- app_nil_r; reflexivity).
        replace ((t ++ []) ++ x) with (t ++ x) in H0
            by (rewrite app_nil_r; reflexivity).
        apply (prefix_irrelevant _ _ _ _ _ H0).
    + destruct (trace_extends _ _ _ _ H0); subst.
      exists x. split.
      * reflexivity.
      * replace t with (t ++ []) in H0
            by (rewrite <- app_nil_r; reflexivity).
        replace ((t ++ []) ++ x) with (t ++ x) in H0
            by (rewrite app_nil_r; reflexivity).
        apply (prefix_irrelevant _ _ _ _ _ H0).
Qed.

Lemma sequence_splits: forall p q t s,
    (s, <{p ; q}>) ->* (t, SSkip) ->
    exists t',
      (s, p) ->* (t', SSkip)
      /\ (t', q) ->* (t, SSkip).
Proof.
  intros. apply clos_rtn1_rt1n in H. dependent induction H. destruct y.
  apply clos_rt1n_rtn1 in H0. inversion H; subst.
  - exists t0. split.
    + constructor.
    + apply H0.
  - destruct (sequence_splits_step _ _ _ _ _ _ H H0) as (t' & ? & ?); subst.
    destruct (IHclos_refl_trans_1n p' q (t0 ++ t') t0 eq_refl eq_refl) as (t'' & ? & ?).
    exists t''. split.
    + apply clos_rt1n_rtn1. econstructor.
      * apply H2.
      * apply clos_rtn1_rt1n. apply H1.
    + apply H4.
Qed.

(* and 5ii *)
Lemma sequence_concat: forall u p q,
    canonical <{p ; q}> u ->
    exists s t, u = s ++ t /\ canonical p s /\ canonical q t.
Proof.
  intros. apply sequence_splits in H.
  destruct H as (t' & ? & ?).
  destruct (trace_extends _ _ _ _ H0); subst.
  exists t'. exists x. repeat split.
  + apply H.
  + apply (prefix_irrelevant t'). rewrite app_nil_r. apply H0.
Qed.

Require Import Wellfounded.
Require Import Psatz.
Lemma canonical_loop_end: forall b p t,
    canonical <{while b {p}}> t ->
    exists t', t = t' ++ [Cond <{ ~ b }>].
Proof.
  induction t using (well_founded_induction
                       (wf_inverse_image _ nat _ (@length _)
                          PeanoNat.Nat.lt_wf_0)); intros.
  apply clos_rtn1_rt1n in H0. inversion H0; subst. inversion H1; subst.
  - apply clos_rt1n_rtn1 in H2. simpl in H2.
    destruct (trace_extends _ _ _ _ H2) as (t' & ->).
    apply prefix_irrelevant_cons in H2.
    destruct (sequence_concat _ _ _ H2) as (s & t & -> & ? & ?).
    apply H in H4. destruct H4; subst.
    exists ([Cond b] ++ s ++ x).
    simpl. rewrite <- app_assoc. auto.
    (* the list length *)
    rewrite 2 app_length. simpl. lia.
  - apply clos_rt1n_rtn1 in H2.
    destruct (skip_non_productive _ _ _ H2) as [-> _].
    exists []. auto.
Qed.

Definition indexed (A:Type):Type := nat -> A.

(* this does build the trace "backwards", (b . sm . b . s(m-1) ... b . s0) but it's waaay easier to work with *)
Fixpoint build_loop_trace (b:Bexpr) (m:nat) (ts: indexed (list trace_step)): list trace_step :=
  match m with
  | 0 => []
  | S n => [Cond b] ++ ts n ++ build_loop_trace b n ts
  end.

Lemma build_loop_ts_extentionally_eq: forall b m ts ts',
    (forall n, n < m -> ts n = ts' n) -> build_loop_trace b m ts = build_loop_trace b m ts'.
Proof.
  induction m; intros; auto.
  simpl. rewrite (H m), (IHm _ ts'). reflexivity.
  - intros. rewrite H; auto.
  - auto.
Qed.

(* surely this is somewhere in the standard library? *)
Fact lt_not_eqb: forall n m, n < m -> Nat.eqb n m = false.
Proof.
  intros. destruct (eqb_spec n m).
  - apply PeanoNat.Nat.lt_neq in H. contradiction.
  - apply PeanoNat.Nat.eqb_neq; assumption.
Qed.

Lemma canonical_loop: forall b p t,
    canonical <{while b {p}}> t ->
    exists m ts, t = build_loop_trace b m ts ++ [Cond <{~ b}>]
            /\ forall i, i < m -> canonical p (ts i).
Proof.
  induction t using (well_founded_induction
                       (wf_inverse_image _ nat _ (@length _)
                          PeanoNat.Nat.lt_wf_0)); intros.
  apply clos_rtn1_rt1n in H0. inversion H0; subst. inversion H1; subst.
  - apply clos_rt1n_rtn1 in H2. simpl in H2.
    destruct (trace_extends _ _ _ _ H2) as (t' & ->).
    apply prefix_irrelevant_cons in H2.
    destruct (sequence_concat _ _ _ H2) as (s & t & -> & ? & ?).
    apply H in H4. destruct H4 as (m & ts & -> & ?).
    set (ts' := fun n => if Nat.eqb n m then s else ts n).
    assert (Hts: ts' m = s) by (subst ts'; simpl; rewrite PeanoNat.Nat.eqb_refl; auto).
    exists (S m). exists ts'. split.
    + simpl. rewrite Hts.
      replace (build_loop_trace b m ts') with (build_loop_trace b m ts).
      rewrite app_assoc. auto.
      assert (ts_ext_eq: forall i, i < m -> ts i = ts' i). {
        intros. subst ts'; cbn. rewrite (lt_not_eqb _ _ H5). auto.
      }
      apply build_loop_ts_extentionally_eq; assumption.
    + intros. apply Arith_prebase.lt_n_Sm_le in H5.
      destruct (Lt.le_lt_or_eq_stt _ _ H5).
      * subst ts'; cbn. rewrite (lt_not_eqb _ _ H6). apply H4; assumption.
      * subst ts'; cbn. subst. rewrite PeanoNat.Nat.eqb_refl; assumption.
    (* the list length stuff *)
    + rewrite 2 app_length. simpl. lia.
  - apply clos_rt1n_rtn1 in H2.
    destruct (skip_non_productive _ _ _ H2) as [-> _].
    exists 0. exists (fun _ => []). split.
    + auto.
    + lia.
Qed.

Lemma loop_canonical: forall b p m (ts: indexed (list trace_step)),
    (forall i, i < m -> canonical p (ts i)) ->
    canonical <{while b {p}}> (build_loop_trace b m ts ++ [Cond <{~ b}>]).
Proof.
  induction m; intros.
  - econstructor.
    + apply (red_loop_false []).
    + constructor.
  - assert (H': forall i, i < m -> canonical p (ts i))
      by (intros; apply H; lia).
    specialize (IHm ts H').
    apply clos_rt1n_rtn1. econstructor.
    + apply red_loop_true.
    + simpl. apply clos_rtn1_rt1n.
      transitivity ([Cond b] ++ (ts m), <{skip ; while b {p}}>).
      * apply sequence_star. apply canonical_extends. apply H. auto.
      * apply clos_rt1n_rtn1. econstructor.
        -- apply red_skip.
        -- apply clos_rtn1_rt1n.
           replace (Cond b :: (ts m ++ build_loop_trace b m ts) ++ [Cond <{ ~ b }>])
             with (([Cond b] ++ ts m) ++ (build_loop_trace b m ts) ++ [Cond <{ ~ b }>])
           by (simpl; rewrite app_assoc; auto).
           apply canonical_extends; assumption.
Qed.
