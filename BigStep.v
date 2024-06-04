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
Limits
Expr
Maps
Syntax
Utils.

Import Trace.
Open Scope com_scope.

Fixpoint loop_fuel__C (fuel: nat) (f: Valuation -> option Valuation) (b: Bexpr) (V: Valuation): option Valuation :=
         match fuel with
        | 0 => None
        | S n => if Beval V b
                then option_bind (f V) (loop_fuel__C n f b)
                else Some V
        end.

Lemma loop_mono: forall i j f b V,
    i <= j -> loop_fuel__C i f b V <<= loop_fuel__C j f b V.
Proof.
    induction i; intros; simpl.
    - constructor.
    - destruct j.
      + inversion H.
      + simpl; destruct (Beval V b).
        * apply option_bind_mono.
          -- apply lessdef_refl.
          -- intro. apply IHi. lia.
        * constructor.
Qed.

(** Concrete semantics *)
Definition loop__C (f: Valuation -> option Valuation) (b: Bexpr) (V: Valuation) : option Valuation :=
         limit (fun n => loop_fuel__C n f b V) (fun i j => loop_mono i j f b V).

Fixpoint denot_fun (p: Trc) (V: Valuation): option Valuation :=
  match p with
  | <{skip}> => Some V
  | <{x := e}> => Some (x !-> Aeval V e ; V)
  | <{p1 ; p2}> => option_bind (denot_fun p1 V) (denot_fun p2)
  | <{b?}> => if Beval V b then Some V else None
  end.

(* Characterizing the concrete denotation *)
Lemma loop_charact__C: forall f b V, exists i, forall j, i <= j -> loop_fuel__C j f b V = loop__C f b V.
Proof. intros. apply limit_charact. Qed.

Lemma loop_unique__C: forall f b V i lim,
    (forall j, i <= j -> loop_fuel__C j f b V = lim) ->
    loop__C f b V = lim.
Proof.
    intros. destruct (loop_charact__C f b V) as [i' LIM].
    set (j := Nat.max i i').
    rewrite <- (H j). rewrite (LIM j). reflexivity.
    all: lia.
Qed.

Lemma denot_seq: forall p1 p2 V,
    denot_fun <{p1 ; p2}> V = option_bind (denot_fun p1 V) (denot_fun p2).
Proof. reflexivity. Qed.

Lemma denot_loop: forall f b V,
    loop__C f b V = if Beval V b then option_bind (f V) (loop__C f b) else Some V.
Proof.
    intros.
    destruct (f V) eqn:H.
    - destruct (loop_charact__C f b v) as [i LIM].
      apply loop_unique__C with (i := (S i)). intros.
      destruct j; [lia|].
      simpl. destruct (Beval V b);
        try reflexivity.
      rewrite H; cbn. apply LIM. lia.
    - destruct (loop_charact__C f b V) as [i LIM].
      apply loop_unique__C with (i := (S i)). intros.
      destruct j; [lia|].
      simpl. destruct (Beval V b);
        [rewrite H|]; reflexivity.
Qed.

Lemma loop_false: forall f b V, Beval V b = false -> loop__C f b V = Some V.
Proof. intros. rewrite denot_loop. rewrite H. reflexivity. Qed.

(** Symbolic Semantics *)
Definition Branch: Type := (Valuation -> Valuation) * (Ensemble Valuation).

Definition denot_sub (phi: sub): Valuation -> Valuation := fun V => Comp V phi.

Lemma denot_id_sub: denot_sub id_sub = fun V => V.
Proof. unfold denot_sub. extensionality V. rewrite comp_id. reflexivity. Qed.

Definition denot__B (b: Bexpr): Ensemble Valuation := fun V => Beval V b = true.

(* Characterizing denot__B *)
Lemma denotB_true: forall V b, In _ (denot__B b) V <-> Beval V b = true.
Proof. split; intros; apply H. Qed.

Lemma denotB_false: forall V b, In _ (Complement _ (denot__B b)) V <-> Beval V b = false.
Proof.
    split; intros.
    - apply (not_true_is_false _ H).
    - unfold Complement, In, denot__B. intro. rewrite H in H0. discriminate.
Qed.

Lemma denotB_top: denot__B (BTrue) = Full_set _.
Proof.
  apply Extensionality_Ensembles. split; intros V _.
  - apply Full_intro.
  - unfold denot__B, In. reflexivity.
Qed.

Lemma denotB_bot: denot__B BFalse = Empty_set _.
Proof. apply Extensionality_Ensembles. split; intros V H; inversion H. Qed.

Lemma denotB_neg: forall b, denot__B <{~ b}> = Complement _ (denot__B b).
Proof.
  intros. apply Extensionality_Ensembles. split; intros V H.
  - intro contra. inversion H. inversion contra.
    rewrite negb_true_iff in H1. rewrite H1 in H2. discriminate.
  - unfold denot__B, Ensembles.In. simpl. rewrite negb_true_iff.
    apply not_true_is_false in H. apply H.
Qed.

Lemma denotB_and: forall b1 b2,
    denot__B <{b1 && b2}> = Intersection _ (denot__B b1) (denot__B b2).
Proof.
  intros. apply Extensionality_Ensembles. split; intros V H.
  - inversion H. apply andb_true_iff in H1. destruct H1.
    split; assumption.
  - destruct H.
    unfold denot__B, Ensembles.In. simpl. rewrite andb_true_iff.
    split; assumption.
Qed.

(* Equation (1) *)
Lemma denot_sub_sound: forall sigma V e,
    Aeval (denot_sub sigma V) e = Aeval V (Aapply sigma e).
Proof. unfold denot_sub. intros. apply comp_sub. Qed.

(* Equation (2) *)
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

Definition compose_subs (s s': sub): sub := fun x => Aapply s (s' x).

Lemma compose_subs_id: forall s, compose_subs id_sub s = s.
Proof.
  intros.
  unfold compose_subs.
  extensionality x.
  now rewrite Aapply_id.
Qed.

Lemma compose_subs_id': forall s, compose_subs s id_sub = s.
Proof.
  intros.
  unfold compose_subs.
  extensionality x.
  easy.
Qed.

Lemma compose_comp: forall V s s',
    Comp V (compose_subs s s') = (fun x => Comp (Comp V s) s' x).
Proof.
  intros.
  extensionality x.
  unfold Comp, compose_subs.
  induction (s' x); simpl; auto.
Qed.

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
    destruct (denot_fun t1 V) eqn:?; simpl; [|contradiction].
    inv H0.
    unfold denot_sub, Sub in *;
      rewrite Heqp, Heqp0 in *;
      cbn in *.
    now rewrite H1, compose_comp.
Qed.

(** Lemma 5 *)
Lemma trace_correspondence_aux: forall t V,
    denot_fun t V <> None <-> V |= PC t.
Proof.
  split.
  - destruct (denot_fun t V) eqn:?; [|contradiction].
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
      destruct (denot_fun t V); [|contradiction].
      inv H0.
      now inv H2.
  - destruct H0.
    apply H in H0.
    rewrite (trace_sub_correct _ _ H0).
    now rewrite H1.
Qed.
