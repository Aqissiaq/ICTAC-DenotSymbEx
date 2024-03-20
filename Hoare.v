From BigStepSymbEx Require Import
  Limits
  Expr
  Maps
  Syntax
  BigStep .

Import While.
Open Scope com_scope.

(*** Axiomatic Semantics *)
(** We define an axiomatic semantics for While and use it to derive verification
conditions for Hoare quadruples (Hoare triples with updates). Then there is some
nice correspondence between pieces (F, B) and paths through the proof tree. *)

(* Bunch of utils that should go elsewhere *)
Ltac forward H :=
  match type of H with
  | ?x -> _ =>
      let name := fresh in assert x as name; [| specialize (H name); clear name]
  end.

Ltac forward_ H name :=
  match type of H with
  | ?x -> _ => assert x as name
  end.

Tactic Notation "forward" ident(H) :=
  forward H.
Tactic Notation "forward" ident(H) "as" ident(name) :=
  forward_ H name.
Tactic Notation "forward" ident(H) "with" uconstr(o1) :=
  specialize (H o1); forward H.
Tactic Notation "forward" ident(H) "with" uconstr(o1) uconstr(o2) :=
  specialize (H o1 o2); forward H.

Lemma subst_one_Aexpr: forall a V x e,
    (Aeval V (Aapply (x !-> e; id_sub) a)) = (Aeval (x !-> Aeval V e; V) a).
Proof.
  induction a; intros; auto.
  - unfold update; simpl.
    now destruct (String.eqb x0 x); subst.
  - simpl; now rewrite IHa1, IHa2.
Qed.

Lemma subst_one_Bexpr: forall P V x e,
    Beval V (Bapply (x !-> e ; id_sub) P) = Beval (x !-> Aeval V e ; V) P.
Proof.
  induction P; intros; auto; simpl.
  - now rewrite IHP.
  - now rewrite IHP1, IHP2.
  - now rewrite 2 subst_one_Aexpr.
Qed.

Notation Assertion := Bexpr.

Notation "A ⊆ B" := (Included _ A B) (at level 90).
Notation "A ∩ B" := (Intersection _ A B) (at level 90).
Notation "¬ A" := (Complement _ A) (at level 90).
Notation "s |= P" := (In _ P s) (at level 90).
Notation "V |= P" := (Beval V P = true) (at level 90).
Notation "P =>> Q" := (denot__B P ⊆ denot__B Q) (at level 90).

Section HoareTriples.

  Inductive triple_derivable: Assertion -> Stmt -> Assertion -> Prop :=
  | triple_skip: forall P, triple_derivable P <{skip}> P
  | triple_seq: forall P p Q' q Q,
      triple_derivable P p Q' ->
      triple_derivable Q' q Q ->
      triple_derivable P <{p ; q}> Q
  | triple_assign: forall P x e,
      triple_derivable (Bapply (x !-> e ; id_sub) P) <{x := e}> P
  | triple_cond: forall P b p q Q,
      triple_derivable <{P && b}> p Q ->
      triple_derivable <{P && ~ b}> q Q ->
      triple_derivable P <{if b {p} {q}}> Q
  | triple_loop: forall P b p,
      triple_derivable <{P && b}> p P ->
      triple_derivable P <{while b {p}}> <{P && ~ b}>
  | triple_adjust: forall P P' p Q Q',
      triple_derivable P' p Q' ->
      P =>> P' ->
      Q' =>> Q ->
      triple_derivable P p Q
  .

  Notation "⊢ {{ P }} p {{ Q }}" := (triple_derivable P p Q) (at level 91).

  Lemma strengthen_triple: forall P P' p Q,
      P =>> P' ->
      ⊢ {{P'}} p {{Q}} ->
      ⊢ {{P}} p {{Q}}.
  Proof.
    intros.
    apply triple_adjust with (P':=P') (Q' := Q); intuition.
  Qed.

  Lemma weaken_triple: forall P p Q' Q,
      ⊢ {{P}} p {{Q'}} ->
      Q' =>> Q ->
      ⊢ {{P}} p {{Q}}.
  Proof.
    intros.
    apply triple_adjust with (P':=P) (Q' := Q'); intuition.
  Qed.

  Definition triple_valid (P: Assertion) (p: Stmt) (Q: Assertion) : Prop :=
    forall V V', V |= P -> denot_fun p V = Some V' -> V' |= Q.

  Lemma denot_while_spec : forall b p s s',
      denot_fun <{ while b {p} }> s = Some s' ->
      exists i,
        forall j, i <= j -> loop_fuel__C i (denot_fun p) b s = Some s'.
  Proof.
    cbn;intros.
    destruct (loop_charact__C (denot_fun p) b s) as [i LIM].
    exists i.
    now rewrite LIM.
  Qed.

  Lemma denot_while_falsifies: forall b p s s',
      denot_fun <{ while b {p} }> s = Some s' ->
      Beval s' b = false.
  Proof.
    intros.
    destruct (denot_while_spec _ _ _ _ H) as (i& ?).
    clear H.
    generalize dependent s.
    induction i; intros.
    - specialize (H0 0).
      forward H0; auto.
      discriminate.
    - cbn in H0.
      destruct (Beval s b) eqn:?; auto.
      + specialize (H0 (S i)).
        forward H0; auto.
        destruct (option_inversion H0) as (s'' & ? & ?).
        eapply IHi.
        intros.
        apply H1.
      + specialize (H0 (S i)).
        forward H0; auto.
        now inversion H0; subst.
  Qed.

  Lemma loop_invariant: forall P b p s s',
      triple_valid <{P && b}> p P ->
      loop__C (denot_fun p) b s = Some s' ->
      s' |= P.
  Proof.
  Admitted.

  Theorem concrete_soundness: forall P p Q,
      ⊢ {{P}} p {{Q}} -> triple_valid P p Q.
  Proof.
    intros.
    induction H; intros s s' PRE COMP;
      inversion COMP; subst; eauto.
    - destruct (option_inversion H2) as (s'' & ? & ?).
      eapply IHtriple_derivable2; eauto.
    - now rewrite <- subst_one_Bexpr.
    - destruct (Beval s b) eqn:?.
      + eapply IHtriple_derivable1; eauto.
        apply andb_true_iff; eauto.
      + eapply IHtriple_derivable2; eauto.
        apply andb_true_iff; split; auto.
        apply negb_true_iff; auto.
    - pose proof denot_while_falsifies b p s s' H1.
      apply andb_true_iff; split.
      + apply loop_invariant with (p:=p) (b:=b) (s:=s); auto.
      + apply negb_true_iff; auto.
    - apply H1.
      eapply IHtriple_derivable; eauto.
      now apply H0.
  Qed.

  Theorem symbolic_soundness: forall P p Q σ ϕ,
      In _ (denot__S p) (σ, ϕ) ->
      ⊢ {{P}} p {{Q}} ->
      forall V, V |= P -> In _ ϕ V ->
           σ V |= Q.
  Proof.
    intros.
    epose proof correct _ _ _ _ H H2 as (V' & <- & COMP).
    pose proof concrete_soundness _ _ _ H0 as VALID.
    apply (VALID _ _ H1 COMP).
  Qed.

  (* the "possible and even instructive" case *)
  Theorem symbolic_soundness': forall P p Q σ ϕ,
      In _ (denot__S p) (σ, ϕ) ->
      ⊢ {{P}} p {{Q}} ->
      forall V, V |= P -> In _ ϕ V ->
           σ V |= Q.
  Proof.
    intros P p Q σ ϕ ? ?.
    generalize dependent ϕ.
    generalize dependent σ.
    induction H0; intros.
    - now inversion H; subst.
    - destruct H as (?F & ?F & ?B & ?B & ? & ? & ? & ?).
      simpl in H3, H4; subst.
      destruct H1.
      eapply IHtriple_derivable2; eauto.
    - inversion H; subst.
      now rewrite <- subst_one_Bexpr.
    - destruct H as [(F & B & ? & ? & ?) | (F & B & ? & ? & ?)].
      + simpl in H2, H3; subst.
        destruct H1.
        eapply IHtriple_derivable1; eauto.
        apply andb_true_iff; auto.
      + simpl in H2, H3; subst.
        destruct H1.
        eapply IHtriple_derivable2; eauto.
        apply andb_true_iff;split; auto.
        apply negb_true_iff.
        now rewrite denotB_false in H2.

    - admit. (* loop case: maybe later *)

    - apply H1.
      eapply IHtriple_derivable; eauto.
      now apply H.
  Admitted.

End HoareTriples.

Section HoareQuadruples.
  (*|
Intuition: a quadruple {P} [σ] s {Q} holds if
V is a state that satisfies P, we start s in σ(V) and if it terminates, the result satisfies Q

|*)

  Definition quad_valid (P: Assertion) (σ: sub) (s: Stmt) (Q: Assertion) : Prop :=
    forall V V',
      V |= P ->
      denot_fun s (denot_sub σ V) = Some V' ->
      V' |= Q.

  Notation "P ->> Q" := (forall V, V |= P -> V |= Q) (at level 90).
  (* Based on KeY book (fig. 17.2)*)
  Inductive quad_derivable: Assertion -> sub -> Stmt -> Assertion -> Prop :=
  | H_exit: forall P σ Q,
      P ->> Bapply σ Q ->
      quad_derivable P σ <{skip}> Q
  | H_seq : forall P σ s1 Q s2 R,
      quad_derivable P σ s1 Q ->
      quad_derivable Q id_sub s2 R ->
      quad_derivable P σ <{s1 ; s2}> R
  | H_asgn: forall P σ x e Q,
      quad_derivable P (x !-> Aapply σ e ; σ) <{skip}> Q ->
      quad_derivable P σ <{x:=e}> Q
  | H_cond: forall P σ b s1 s2 Q,
      quad_derivable (BAnd P (Bapply σ b)) σ s1 Q ->
      quad_derivable (BAnd P (Bapply σ <{~ b}>)) σ s2 Q ->
      quad_derivable P σ <{if b {s1} {s2}}> Q
  | H_loop: forall P I σ b s1 Q,
      P ->> (Bapply σ I) ->
      quad_derivable (BAnd I (Bapply σ b)) id_sub s1 I ->
      quad_derivable (BAnd I (Bapply σ <{~ b}>)) id_sub <{skip}> Q ->
      quad_derivable P σ <{while b {s1}}> Q.

  Notation "⊢ {{ P }} [ σ ] s {{ Q }}" := (quad_derivable P σ s Q) (at level 90).

  (* Some testing *)
  Example branch_example: Stmt := <{
     X := X + 1 ;
        if X <= 10
              {if Y <= 5 {X := 42} {X := 0} }
              {if 4 <= Y {X := 42} {X := 1} }
      }>.

  Fact branch_example_valid: quad_valid (<{X <= 9 && Y <= 5}>) id_sub branch_example <{X <= 42 && 42 <= X}>.
  Proof.
    intros V V' ? ?.
    apply andb_true_iff in H.
    destruct H.
    apply PeanoNat.Nat.leb_le in H, H1.
    cbn in H, H0, H1.
    apply PeanoNat.Nat.leb_le in H, H1.
    rewrite denot_id_sub, PeanoNat.Nat.add_1_r in *.
    assert (PeanoNat.Nat.leb (S (V X)) 10 = true) by auto.
    rewrite H1, H2 in H0.
    now inversion H0; subst.
  Qed.

  Ltac unfold_derivable :=
    match goal with
    | |- quad_derivable _ _ _ _ => econstructor
    end.

  Fact branch_example_derivable: quad_derivable (<{X <= 9 && Y <= 5}>) id_sub branch_example <{X <= 42 && 42 <= X}>.
  Proof.
    eapply H_seq with (Q:= <{X <= 10 && Y <= 5}>).
    repeat unfold_derivable.
  Admitted.

  Theorem hoare_sound: forall P σ s Q,
      quad_derivable P σ s Q -> quad_valid P σ s Q.
  Proof.
  Admitted.

  (* This may not be true, due to nondeterminism *)
  Theorem hoare_complete: forall P σ s Q,
      quad_valid P σ s Q -> quad_derivable P σ s Q.
  Proof.
  Admitted.

End HoareQuadruples.
