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
  SmallStep
  BigStep
  Correspondence.
Import While.

Open Scope com_scope.
Open Scope string_scope.
Open Scope list_scope.

Definition SConfig : Type := Stmt * sub * Bexpr.

Reserved Notation " c '=>s' c' " (at level 40).

(* Figure 3 *)
Inductive Sstep : relation SConfig :=
| Asgn_step : forall x e sig phi,
    (<{ x := e }>, sig , phi) =>s (SSkip, (update sig x (Aapply sig e)), phi)
| IfTrue_step : forall b p1 p2 sig phi,
    (<{ if b {p1} {p2} }>, sig, phi) =>s (p1, sig, BAnd phi (Bapply sig b))
| IfFalse_step : forall b p1 p2 sig phi,
    (<{ if b {p1} {p2} }>, sig, phi) =>s (p2 , sig, BAnd phi (BNot (Bapply sig b)))
| WhileTrue_step : forall b p sig phi,
    (<{ while b {p} }>, sig, phi) =>s (<{ p ; while b {p}}>, sig, BAnd phi (Bapply sig b))
| WhileFalse_step : forall b p sig phi,
    (<{ while b {p}}>, sig, phi) =>s (SSkip, sig, BAnd phi (BNot (Bapply sig b)))
| Skip_step : forall p sig phi,
    (<{skip ; p}>, sig, phi) =>s (p, sig, phi)
| Seq_step : forall p p' q sig sig' phi phi',
    (p, sig, phi) =>s (p', sig', phi') ->
    (<{p ; q}>, sig, phi) =>s (<{p' ; q}>, sig', phi')
  where " c '=>s' c' " := (Sstep c c').

Definition multi_Sstep := clos_refl_trans_n1 _ Sstep.
Notation " c '=>*' c' " := (multi_Sstep c c') (at level 40).

Lemma direct_if_trace_step: forall p p' t t' phi,
    red__S (t, p) (t', p') ->
    denot__B phi = denot__B (acc_pc t id_sub) ->
    (exists phi', (p, acc_subst t id_sub, phi) =>s (p', acc_subst t' id_sub, phi')
                                           /\ denot__B phi' = denot__B (acc_pc t' id_sub)).
Proof.
  intros. dependent induction H; subst.
  - exists phi. split.
    + rewrite acc_subst_asgn_last. constructor.
    + rewrite acc_pc_asgn_last; auto.
  - exists (BAnd phi (Bapply (acc_subst t id_sub) b)). split.
    + rewrite acc_subst_cond_last.
      apply IfTrue_step.
    + rewrite acc_pc_cond_last, 2 denotB_and, H0. auto.
  - exists (BAnd phi (BNot (Bapply (acc_subst t id_sub) b))). split.
    + rewrite acc_subst_cond_last.
      apply IfFalse_step.
    + rewrite acc_pc_cond_last, 2 denotB_and, H0. auto.
  - exists (BAnd phi (Bapply (acc_subst t id_sub) b)). split.
    + rewrite acc_subst_cond_last.
      apply WhileTrue_step.
    + rewrite acc_pc_cond_last, 2 denotB_and, H0. auto.
  - exists (BAnd phi (BNot (Bapply (acc_subst t id_sub) b))). split.
    + rewrite acc_subst_cond_last.
      apply WhileFalse_step.
    + rewrite acc_pc_cond_last, 2 denotB_and, H0. auto.
  - exists phi. split.
    + apply Skip_step.
    + assumption.
  - destruct (IHred__S p0 p'0 t t' eq_refl eq_refl H0) as (phi' & ? & ?).
    exists phi'. split; [apply Seq_step|]; assumption.
Qed.

(* Proposition 1a *)
Lemma direct_if_trace: forall p p' t t' phi,
    (t, p) ->* (t', p') ->
    denot__B phi = denot__B (acc_pc t id_sub) ->
    (exists phi', (p, acc_subst t id_sub, phi) =>* (p', acc_subst t' id_sub, phi')
            /\ denot__B phi' = denot__B (acc_pc t' id_sub)).
Proof.
  intros. dependent induction H.
  - exists phi. split.
    + constructor.
    + auto.
  - destruct y.
    destruct (IHclos_refl_trans_n1 p s t t0 eq_refl eq_refl H1) as (phi' & ? & ?).
    destruct (direct_if_trace_step _ _ _ _  phi' H H3) as (phi'' & ? & ?).
    exists phi''. split.
    + econstructor.
      * apply H4.
      * apply H2.
    + auto.
Qed.

Lemma trace_if_direct_step: forall p p' t sig phi sig' phi',
    (p, sig, phi) =>s (p', sig', phi') ->
    acc_subst t id_sub = sig ->
    denot__B (acc_pc t id_sub) = denot__B phi ->
    exists t', red__S (t, p) (t', p')
          /\ acc_subst t' id_sub = sig'
          /\ denot__B (acc_pc t' id_sub) = denot__B phi'.
Proof.
  intros. dependent induction H; subst.
  - exists (t ++ [Asgn x e]). repeat split.
    + constructor.
    + rewrite acc_subst_asgn_last. auto.
    + rewrite acc_pc_asgn_last. auto.
  - exists (t ++ [Cond b]). repeat split.
    + constructor.
    + rewrite acc_subst_cond_last. auto.
    + rewrite acc_pc_cond_last, 2 denotB_and, H1. auto.
  - exists (t ++ [Cond <{~ b}>]). repeat split.
    + constructor.
    + rewrite acc_subst_cond_last. auto.
    + rewrite acc_pc_cond_last, 2 denotB_and, H1. auto.
  - exists (t ++ [Cond b]). repeat split.
    + constructor.
    + rewrite acc_subst_cond_last. auto.
    + rewrite acc_pc_cond_last, 2 denotB_and, H1. auto.
  - exists (t ++ [Cond <{~ b}>]). repeat split.
    + constructor.
    + rewrite acc_subst_cond_last. auto.
    + rewrite acc_pc_cond_last, 2 denotB_and, H1. auto.
  - exists t. repeat split.
    + constructor.
    + assumption.
  - destruct (IHSstep p0 p'0 (acc_subst t id_sub) phi sig' phi' JMeq_refl JMeq_refl eq_refl H1)
      as (t' & ? & ? & ?).
    exists t'. repeat split; [constructor| |]; assumption.
Qed.

(* Proposition 1b *)
Lemma trace_if_direct: forall p p' t sig phi sig' phi',
    (p, sig, phi) =>* (p', sig', phi') ->
    acc_subst t id_sub = sig ->
    denot__B (acc_pc t id_sub) = denot__B phi ->
    exists t', (t, p) ->* (t', p')
          /\ acc_subst t' id_sub = sig'
          /\ denot__B (acc_pc t' id_sub) = denot__B phi'.
Proof.
  intros. dependent induction H.
  - exists t. repeat split;
      [constructor| |]; assumption.
  - destruct y, p0.
    destruct (IHclos_refl_trans_n1 _ _ _ _ _ _ JMeq_refl JMeq_refl H1 H2)
      as (t' & ? & ? & ?).
    destruct (trace_if_direct_step _ _ _ _ _ _ _ H H4 H5) as (t'' & ? & ? & ?).
    exists t''. repeat split; try assumption.
    + econstructor; [apply H6 | apply H3].
Qed.

(* Corollary 1 *)
Corollary correctness: forall p sig phi,
    (p, id_sub, BTrue) =>* (SSkip, sig, phi) ->
    forall V, Beval V phi = true ->
         denot_fun p V = Some (denot_sub sig V).
Proof.
  intros. apply (trace_if_direct _ _ []) in H; auto.
  destruct H as (t' & Hcomp & ? & ?).
  assert (tfeasible: feasible t'). { exists V. rewrite H1. apply H0. }
  specialize (small_to_big _ _ Hcomp tfeasible). intro.
  destruct (correct p (denot_sub (acc_subst t' id_sub)) (denot__B (acc_pc t' id_sub)) V H2)
    as (V' & <- & ?).
  - rewrite H1. apply H0.
  - rewrite <- H. apply H3.
Qed.

(* Corollary 2 *)
Corollary completeness: forall p V V',
    denot_fun p V = Some V' ->
    exists sig phi, (p, id_sub, BTrue) =>* (SSkip, sig, phi) /\ Beval V phi = true.
Proof.
  intros. destruct (complete _ _ _ H) as (F & B & ? & ? & ?).
  assert (Inhabited _ B) by (exists V; auto).
  destruct (big_to_small _ _ _ H0 H3) as (t & ? & ?).
  destruct (direct_if_trace _ _ _ _ BTrue H4) as (phi & ? & ?); auto.
  exists (acc_subst t id_sub), phi. split.
  - apply H6.
  - inversion H5; subst.
    rewrite <- H7 in H2. apply H2.
Qed.
