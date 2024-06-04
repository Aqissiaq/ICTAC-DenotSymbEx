From Coq Require Import
                 Strings.String
                 Bool.Bool
                 Init.Datatypes
                 Lists.List
                 Logic.FunctionalExtensionality (* for equality of substitutions *)
                 Ensembles
                 Psatz
                 Classes.RelationClasses.

From BigStepSymbEx Require Import
Expr
Maps
Syntax
Utils.

Import Trace TraceNotations.
Open Scope com_scope.

(** Concrete semantics *)
Fixpoint denot_fun (p: Trc) (V: Valuation): option Valuation :=
  match p with
  | <{skip}> => Some V
  | <{x := e}> => Some (x !-> Aeval V e ; V)
  | <{b?}> => if Beval V b then Some V else None
  | <{p1 ; p2}> => option_bind (denot_fun p1 V) (denot_fun p2)
  end.

(** Symbolic Semantics *)
(* TODO: cleanup *)
Fixpoint trace_denot__S (t:Trc): sub * Bexpr :=
  match t with
  | <{skip}> => (id_sub, BTrue)
  | <{x := e}> => ((x !-> e ; id_sub), BTrue)
  | <{ b? }> => (id_sub, b)
  | <{t1 ; t2}> =>
      let (s1, b1) := trace_denot__S t1 in
      let (s2, b2) := trace_denot__S t2 in
      (compose_subs s1 s2, BAnd b1 (Bapply s1 b2))
  end.

Definition Sub (t:Trc) := fst (trace_denot__S t).

Inductive Sub_spec: Trc -> sub -> Prop :=
| Sub_spec_empty: Sub_spec TSkip id_sub
| Sub_spec_asrt: forall b, Sub_spec <{b?}> id_sub
| Sub_spec_asgn: forall x e, Sub_spec <{x := e}> (x !-> e ; id_sub)
| Sub_spec_seq: forall t1 t2 s1 s2,
    Sub_spec t1 s1 ->
    Sub_spec t2 s2 ->
    Sub_spec <{t1 ; t2}> (compose_subs s1 s2).

Lemma Sub_spec_correct: forall t s,
    Sub t = s <-> Sub_spec t s.
Proof.
  intros.
  split.
  - generalize dependent s.
    induction t; cbn in *; intros;
      rewrite <- H; try constructor.
    unfold Sub in *; cbn in *.
    destruct (trace_denot__S t1), (trace_denot__S t2); cbn in *.
    pose proof IHt1 s0 eq_refl.
    pose proof IHt2 s1 eq_refl.
    constructor; auto.
  - intro.
    induction H;
      try easy.
    unfold Sub in *; cbn in *.
    destruct (trace_denot__S t1), (trace_denot__S t2); cbn in *.
    now subst.
Qed.

Lemma Sub_unit_l: forall t,
    Sub (TSeq TSkip t) = Sub t.
Proof.
  destruct t; cbn; auto.
  - now rewrite compose_subs_id.
  - unfold Sub; cbn.
    destruct (trace_denot__S t1), (trace_denot__S t2); cbn.
    now rewrite compose_subs_id.
Qed.

Lemma Sub_unit_r: forall t,
    Sub (TSeq t TSkip) = Sub t.
Proof.
  destruct t; cbn; auto.
  unfold Sub; cbn.
  destruct (trace_denot__S t1), (trace_denot__S t2); cbn.
  now rewrite compose_subs_id'.
Qed.

Definition PC (t:Trc) := snd (trace_denot__S t).
Inductive PC_spec: Trc -> Bexpr -> Prop :=
| PC_spec_empty: PC_spec TSkip BTrue
| PC_spec_asrt: forall b, PC_spec <{b?}> b
| PC_spec_asgn: forall x e, PC_spec <{x := e}> BTrue
| PC_spec_seq: forall t1 t2 b1 b2,
    PC_spec t1 b1 ->
    PC_spec t2 b2 ->
    PC_spec <{t1 ; t2}> (BAnd b1 (Bapply (Sub t1) b2)).

Lemma PC_spec_correct: forall t b,
    PC t = b <-> PC_spec t b.
Proof.
  intros.
  split.
  - generalize dependent b.
    induction t; cbn in *; intros;
      rewrite <- H; try constructor.
    unfold PC, Sub in *; cbn in *.
    destruct (trace_denot__S t1) eqn:?, (trace_denot__S t2); cbn in *.
    pose proof IHt1 b0 eq_refl.
    pose proof IHt2 b1 eq_refl.
    assert (s = Sub t1) as ->. {
      unfold Sub.
      now rewrite Heqp.
    }
    econstructor; auto.
  - intro.
    induction H;
      try easy.
    unfold PC in *; cbn in *.
    destruct (trace_denot__S t1) eqn:?, (trace_denot__S t2); cbn in *.
    assert (s = Sub t1) as ->. {
      unfold Sub.
      now rewrite Heqp.
    }
    now subst.
Qed.

Lemma not_none_monotone: forall V t1 t2,
    denot_fun <{t1 ; t2}> V <> None ->
    denot_fun t1 V <> None.
Proof.
  cbn; unfold option_bind; intros.
  destruct (denot_fun t1 V); easy.
Qed.

Lemma not_none_monotone': forall V V' t1 t2,
    denot_fun <{t1 ; t2}> V <> None ->
    denot_fun t1 V = Some V' ->
    denot_fun t2 V' <> None.
Proof.
  cbn; unfold option_bind; intros.
  now rewrite H0 in H.
Qed.

Lemma asgn_sound': forall V x e,
    (Comp V (x !-> e ; id_sub)) = (x !-> Aeval V e ; V).
Proof.
  intros.
  pose proof asgn_sound V id_sub x e.
  rewrite comp_id, Aapply_id in H.
  apply H.
Qed.

(** Lemma 4 *)
Lemma trace_sub_correct: forall t V,
    denot_fun t V <> None ->
    denot_fun t V = Some (denot_sub (Sub t) V).
Proof.
  induction t; intros;
    unfold denot_sub, Sub; cbn.
  - now rewrite comp_id.
  - now rewrite (asgn_sound' V x e).
  - cbn in H.
    destruct (Beval V b).
    + now rewrite comp_id.
    + contradiction.
  - destruct (trace_denot__S t1) eqn:?, (trace_denot__S t2) eqn:?.
    pose proof not_none_monotone _ _ _ H.
    apply IHt1 in H0.
    pose proof not_none_monotone' _ _ _ _ H H0.
    apply IHt2 in H1.
    cbn in H.
    destruct (denot_fun t1 V) eqn:?; simpl; [ |contradiction].
    inv H0.
    unfold denot_sub, Sub in *;
      rewrite Heqp, Heqp0 in *;
      cbn in *.
    now rewrite H1, compose_comp.
Qed.

Notation "V |= b" := (Beval V b = true) (at level 90).

(** Lemma 5 *)
Lemma trace_correspondence_aux: forall t V,
    denot_fun t V <> None <-> V |= PC t.
Proof.
  split.
  - destruct (denot_fun t V) eqn:?; [ |contradiction].
    generalize dependent v.
    generalize dependent V.
    induction t; intros.
    + easy.
    + easy.
    + cbn in Heqo.
      destruct (Beval V b) eqn:?; easy.
    + cbn in *.
      destruct (option_inversion Heqo) as (?V & ? & ?).
      pose proof IHt1 _ _ H0 (some_not_none V0).
      pose proof IHt2 _ _ H1 (some_not_none v).
      unfold PC in *; cbn.
      destruct (trace_denot__S t1) eqn:?, (trace_denot__S t2).
      simpl in *.
      apply andb_true_iff.
      split; auto.
      rewrite <- comp_subB.
      assert (denot_fun t1 V <> None) by (rewrite H0; easy).
      replace s with (Sub t1) by (unfold Sub; now rewrite Heqp).
      replace (Comp V (Sub t1)) with V0 by
        (rewrite (trace_sub_correct t1 V H4) in H0; now inv H0).
      apply H3.
  - destruct (denot_fun t V) eqn:?; intros.
    + easy.
    + generalize dependent V.
      induction t;intros; cbn; try easy.
      * inv Heqo.
        destruct (Beval V b) eqn:?.
        -- discriminate.
        -- unfold PC in H.
           cbn in H.
           rewrite H in Heqb0.
           discriminate.
      * cbn in Heqo.
        destruct (option_inversion_none _ _ Heqo) as [? | (?V & ? & ?)].
        -- apply (IHt1 _ H0).
           unfold PC in *.
           cbn in H.
           destruct (trace_denot__S t1), (trace_denot__S t2).
           cbn in *.
           apply andb_true_iff in H.
           destruct H.
           apply H.
        -- apply (IHt2 _ H1).
           unfold PC in *.
           cbn in H.
           destruct (trace_denot__S t1) eqn:?, (trace_denot__S t2).
           cbn in *.
           apply andb_true_iff in H.
           destruct H.
           rewrite <- comp_subB in H2.
           replace s with (Sub t1) in H2 by (unfold Sub; now rewrite Heqp).
           replace V0 with (Comp V (Sub t1)) in *.
           apply H2.

           rewrite (trace_sub_correct) in H0.
           now inv H0.
           now rewrite H0.
Qed.

(** Theorem 1 *)
Theorem trace_correspondence: forall t V V',
    denot_fun t V = Some V' <-> (V |= PC t) /\ denot_sub (Sub t) V = V'.
Proof.
  intros.
  pose proof trace_correspondence_aux t V.
  split; intros.
  - split.
    + apply H.
      now rewrite H0.
    + assert (denot_fun t V <> None) by now rewrite H0.
      pose proof trace_sub_correct _ _ H1.
      destruct (denot_fun t V); [ |contradiction].
      inv H0.
      now inv H2.
  - destruct H0.
    apply H in H0.
    rewrite (trace_sub_correct _ _ H0).
    now rewrite H1.
Qed.

Print Assumptions trace_correspondence.

(*TODO: The DL stuff? *)
