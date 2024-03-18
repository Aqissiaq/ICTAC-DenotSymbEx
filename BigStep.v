From Coq Require Export
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
Syntax .

Import While.
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

Fixpoint denot_fun (p: Stmt) (V: Valuation): option Valuation :=
         match p with
        | <{skip}> => Some V
        | <{x := e}> => Some (x !-> Aeval V e ; V)
        | <{p1 ; p2}> => option_bind (denot_fun p1 V) (denot_fun p2)
        | <{if b {p1} {p2}}> => if Beval V b then (denot_fun p1 V) else (denot_fun p2 V)
        | <{while b {p}}> => loop__C (denot_fun p) b V
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

Lemma denot_loop_seq: forall p b V,
    denot_fun <{while b {p}}> V = denot_fun <{if b {p ; while b {p}} {skip}}> V.
Proof.
    intros. simpl. rewrite denot_loop.
    destruct (Beval V b); reflexivity.
Qed.

Lemma loop_false: forall f b V, Beval V b = false -> loop__C f b V = Some V.
Proof. intros. rewrite denot_loop. rewrite H. reflexivity. Qed.

(** Symbolic Semantics *)

Section EnsembleHelpers.
  Context {X: Type}.
  Context (A B C: Ensemble X).

  Lemma intersect_full: Intersection X (Full_set _) A = A.
  Proof.
    intros. apply Extensionality_Ensembles. split; intros x H.
    - destruct H; assumption.
    - split; [constructor | assumption].
  Qed.

  Lemma intersect_comm: Intersection _ A B = Intersection _ B A.
  Proof.
    intros. apply Extensionality_Ensembles. split; intros x H;
      destruct H; split; assumption.
  Qed.

  Lemma intersect_assoc: Intersection _ A (Intersection _ B C) = Intersection _ (Intersection _ A B) C.
  Proof.
    intros. apply Extensionality_Ensembles. split; intros x H; repeat split;
      try (destruct H; destruct H0; assumption);
      destruct H; destruct H; assumption.
  Qed.

  Definition inverse_image (F: X -> X) (B: Ensemble X): Ensemble X := fun x => B (F x).

  (* characterizing inverse images *)
  Lemma inverse_id: forall (A: Ensemble X), inverse_image (fun x => x)  A = A.
  Proof. intros. apply Extensionality_Ensembles. split; intros V H; assumption. Qed.

  Lemma inverse_full : forall F, inverse_image F (Full_set _) = Full_set X.
  Proof. intros. apply Extensionality_Ensembles. split; intros V _; constructor. Qed.

  Lemma inverse_empty : forall F, inverse_image F (Empty_set _) = Empty_set X.
  Proof. intros. apply Extensionality_Ensembles. split; intros V H; inversion H. Qed.

  Lemma inverse_complement : forall F B,
      inverse_image F (Complement _ B) = Complement X (inverse_image F B).
  Proof.
      intros. apply Extensionality_Ensembles. split; intros V H.
      - intro contra. apply H. apply contra.
      - apply H.
  Qed.

  Lemma inverse_intersection : forall F B1 B2,
      inverse_image F (Intersection _ B1 B2) = Intersection X (inverse_image F B1) (inverse_image F B2).
  Proof.
      intros. apply Extensionality_Ensembles. split; intros V H.
      - inversion H; subst. split; assumption.
      - destruct H. split; assumption.
  Qed.

  Lemma inverse_inverse : forall F F' (B: Ensemble X),
      inverse_image F (inverse_image F' B) = inverse_image (fun x => F' (F x)) B.
  Proof.
      intros. apply Extensionality_Ensembles. split; intros V H.
      - apply H.
      - apply H.
  Qed.
End EnsembleHelpers.

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

Fixpoint n_fold {X: Type} (n: nat) (f: X -> X): X -> X :=
         match n with
        | 0 => fun x => x
        | S n => fun x => f (n_fold n f x)
         end.

Lemma n_fold_inversion {X:Type}: forall n f (x: X), f (n_fold n f x) = n_fold (S n) f x.
Proof. reflexivity. Qed.

Lemma n_fold_step {X:Type}: forall n f (x y: X), n_fold (S n) f x = y -> exists z, n_fold n f x = z /\ f z = y.
Proof.
    induction n; intros; simpl in *.
    - exists x. split; [reflexivity | apply H].
    - exists (f (n_fold n f x)). split; [reflexivity | apply H].
Qed.

Lemma n_fold_construct {X:Type}: forall n f (x y z: X),
    n_fold n f x = y -> f y = z -> n_fold (S n) f x = z.
Proof.
    induction n; intros; simpl in *.
    - rewrite H. apply H0.
    - rewrite (IHn f x (n_fold n f x) y).
      + assumption.
      + reflexivity.
      + assumption.
Qed.

Definition loop_helper (body: Ensemble Branch) (b: Bexpr) (p: Stmt): Ensemble Branch -> Ensemble Branch :=
       fun big_F => fun X => exists F B Fp Bp,
           In _ big_F (F, B)
           /\ In _ body (Fp, Bp)
           /\ fst X = (fun V => F (Fp V))
           /\ snd X = Intersection _ (denot__B b) (Intersection _ Bp (inverse_image Fp B)).

Lemma loop_helper_step: forall n body b p F B X0,
    In _ (n_fold (S n) (loop_helper body b p) X0) (F, B) ->
    exists F' B', In _ (n_fold n (loop_helper body b p) X0) (F', B')
             /\ loop_helper body b p (Singleton _ (F', B')) (F, B)
.
Proof.
    intros.
    destruct (n_fold_step n (loop_helper body b p) X0 (n_fold (S n) (loop_helper body b p) X0))
      as [Y [H0 H1]]; [reflexivity|].
    destruct H as [F' [B' [Fp [Bp [Hbody [Hloop [tmp0 tmp1]]]]]]].
    simpl in tmp0, tmp1; subst.
    exists F'. exists B'. repeat split.
    - apply Hbody.
    - exists F'. exists B'. exists Fp. exists Bp.
      repeat split. apply Hloop.
Qed.

Inductive Union_Fam {X I} (Fs: I -> Ensemble X): Ensemble X :=
  | Fam_intro: forall {i x}, In _ (Fs i) x -> In _ (Union_Fam Fs) x.

Fixpoint denot__S (p: Stmt): Ensemble Branch := match p with
        | <{skip}> => Singleton _ (fun V => V, Full_set _)
        | <{x := e}> => Singleton _ (fun V => (x !-> Aeval V e ; V), Full_set _)
        | <{p ; q}> =>
            fun X => exists Fp Fq Bp Bq,
                In _ (denot__S p) (Fp, Bp)
                /\ In _ (denot__S q) (Fq, Bq)
                /\ (fst X = fun V => Fq (Fp V))
                /\ snd X = Intersection _ Bp (inverse_image Fp Bq)
        | <{if b {p} {q}}> =>
            fun X =>
              (exists F B,
                  In _ (denot__S p) (F, B)
                  /\ fst X = F
                  /\ snd X = Intersection _ B (denot__B b))
              \/
                (exists F B,
                    In _ (denot__S q) (F, B)
                    /\ fst X = F
                    /\ snd X = Intersection _ B (Complement _ (denot__B b)))
        | <{while b {p}}> =>
            Union_Fam (fun m => n_fold m (loop_helper (denot__S p) b p) (Singleton _ (fun V => V, Complement _ (denot__B b))))
         end.

Lemma denot_seq__S: forall p1 p2 F1 F2 B1 B2,
    In _ (denot__S p1) (F1, B1) ->
    In _ (denot__S p2) (F2, B2) ->
    In _ (denot__S <{p1 ; p2}>) (fun V => F2 (F1 V), Intersection _ B1 (inverse_image F1 B2)).
Proof.
    intros.
    exists F1. exists F2. exists B1. exists B2.
    repeat split; assumption.
Qed.

Lemma denot_if__S: forall b p1 p2 F1 F2 B1 B2,
    In _ (denot__S p1) (F1, B1) ->
    In _ (denot__S p2) (F2, B2) ->
    In _ (denot__S <{if b {p1} {p2}}>) (F1, Intersection _ B1 (denot__B b))
    /\ In _ (denot__S <{if b {p1} {p2}}>) (F2, Intersection _ B2 (Complement _ (denot__B b))).
Proof.
    intros. split.
    - left. exists F1. exists B1. repeat split. assumption.
    - right. exists F2. exists B2. repeat split. assumption.
Qed.

Lemma denot_while0__S: forall b p,
    In _ (denot__S <{while b {p}}>) (fun V => V, Complement _ (denot__B b)).
Proof. intros. exists 0. constructor. Qed.

Lemma denot_while1__S: forall b p F B,
    In _ (denot__S p) (F, B) ->
    In _ (denot__S <{while b {p}}>) (F,
       Intersection _ (denot__B b) (Intersection _ B (inverse_image F (Complement _ (denot__B b))))).
Proof.
    intros. exists 1.
    simpl.
    exists (fun V => V). exists (Complement _ (denot__B b)).
    exists F. exists B. repeat split.
    apply H.
Qed.

Lemma denot_while__S: forall b p F B Floop Bloop,
    In _ (denot__S p) (F, B) ->
    In _ (denot__S <{while b {p}}>) (Floop, Bloop) ->
    In _ (denot__S <{while b {p}}>)
   (fun V => Floop (F V), Intersection _ (denot__B b) (Intersection _ B (inverse_image F Bloop))).
Proof.
    intros. inversion H0; subst.
    apply Fam_intro with (i := S i).
    exists Floop. exists Bloop. exists F. exists B.
    repeat split;
      assumption.
Qed.

Lemma loop_complete: forall i p b V V',
    loop_fuel__C (S i) (denot_fun p) b V = Some V' ->
    (forall Vbody Vbody',
        denot_fun p Vbody = Some Vbody' ->
      exists F B,
        In _ (denot__S p) (F, B)
        /\ F Vbody = Vbody'
        /\ In _ B Vbody) ->
    exists F B,
      In _ (Union_Fam (fun m => n_fold m (loop_helper (denot__S p) b p) (Singleton _ (fun V => V, Complement _ (denot__B b))))) (F, B)
      /\ F V = V'
      /\ In _ B V
.
Proof.
    induction i; intros.
    - simpl in H. destruct (Beval V b) eqn:Hbeval, (denot_fun p V); cbn in H;
        inversion H.
      + exists (fun V => V). exists (Complement _ (denot__B b)). repeat split.
        * apply Fam_intro with (i := 0). simpl.
          constructor.
        * rewrite denotB_false. rewrite <- H2. apply Hbeval.
      + exists (fun V => V). exists (Complement _ (denot__B b)). repeat split.
        * apply Fam_intro with (i := 0). simpl.
          constructor.
        * rewrite denotB_false. rewrite <- H2. apply Hbeval.
    - simpl in H. destruct (Beval V b) eqn:Hbeval; destruct (denot_fun p V) eqn:Hbody; cbn in *.
      + destruct (IHi _ _ _ _ H H0) as [F [B [Hin [HF HB]]]].
        inversion Hin as [i' [? ?]]; subst.
        destruct (H0 V v Hbody) as [F' [B' [Hin' [HF' HB']]]].
        exists (fun V => F (F' V)). eexists.
        repeat split.
        * apply Fam_intro with (i := S i').
          exists F. exists B. exists F'. exists B'.
          repeat split.
          -- apply H1.
          -- apply Hin'.
        * rewrite HF'. reflexivity.
        * repeat split.
          -- rewrite denotB_true. apply Hbeval.
          -- apply HB'.
          -- unfold inverse_image, In.
             rewrite HF'.
             apply HB.
      + inversion H.
      + inversion H; subst.
        specialize (IHi p b V' V').
        rewrite Hbeval in IHi.
        destruct (IHi H H0) as [F [B [Hin [HF HB]]]].
        inversion Hin as [i' [? ?]]; subst.
        exists F. exists B. repeat split.
        * apply Hin.
        * apply HF.
        * apply HB.
      + inversion H; subst.
        specialize (IHi p b V' V').
        rewrite Hbeval in IHi.
        destruct (IHi H H0) as [F [B [Hin [HF HB]]]].
        inversion Hin as [i' [? ?]]; subst.
        exists F. exists B. repeat split.
        * apply Hin.
        * apply HF.
        * apply HB.
Qed.

Lemma complete: forall p V V',
    denot_fun p V = Some V' ->
    exists F B,
      In _ (denot__S p) (F, B)
      /\ F V = V'
      /\ In _ B V.
Proof.
    induction p; intros.
    (* skip *)
    - exists (fun V => V).
      exists (Full_set _).
      simpl in *. repeat split;
        inversion H; reflexivity.
    (* assign *)
    - exists (fun V => (x !-> Aeval V e ; V)).
      exists (Full_set _).
      simpl in *. repeat split;
        inversion H; reflexivity.
    (* sequence *)
    - inversion H; subst.
      destruct (option_inversion H1) as [V1 [? ?]].
      destruct (IHp1 _ _ H0) as [F1 [B1 [Hbranch1 [Hresult1 Hpart1]]]].
      destruct (IHp2 _ _ H2) as [F2 [B2 [Hbranch2 [Hresult2 Hpart2]]]].
      exists (fun V => F2 (F1 V)).
      exists (Intersection _ B1 (inverse_image F1 B2)).
      simpl in *. split; try split.
      + exists F1. exists F2. exists B1. exists B2. repeat split;
          assumption.
      + rewrite Hresult1. apply Hresult2.
      + split.
        * apply Hpart1.
        * unfold inverse_image, In.
          rewrite Hresult1. apply Hpart2.
    (* if... *)
    - inversion H; subst. destruct (Beval V b) eqn:Hbeval.
      (*... true*)
      + destruct (IHp1 _ _ H1) as [F1 [B1 [Hbranch [Hresult Hpart]]]].
        exists F1. exists (Intersection _ B1 (denot__B b)). split; try split.
        * left. exists F1. exists B1. repeat split.
          apply Hbranch.
        * apply Hresult.
        * split.
          -- apply Hpart.
          -- rewrite denotB_true. apply Hbeval.
      (*... false*)
      + destruct (IHp2 _ _ H1) as [F2 [B2 [Hbranch [Hresult Hpart]]]].
        exists F2. exists (Intersection _ B2 (Complement _ (denot__B b))). split; try split.
        * right. exists F2. exists B2. repeat split.
          apply Hbranch.
        * apply Hresult.
        * split.
          -- apply Hpart.
          -- rewrite denotB_false. apply Hbeval.
    (* while *)
    - inversion H; subst; destruct (Beval V b) eqn:Hbeval.
      (* looping *)
      + rewrite denot_loop in H1. rewrite Hbeval in H1.
        destruct (option_inversion H1) as [? [? ?]].
        destruct (IHp _ _ H0) as [F [B [Hbody [HF HB]]]].
        destruct (loop_charact__C (denot_fun p) b x) as [i LIM].
        rewrite <- LIM with (j := S i) in H2; [|lia].
        destruct (loop_complete _ _ _ _ _ H2 IHp) as [F' [B' [Hhelp [HF' HB']]]].
        exists (fun V => F' (F V)). exists (Intersection _ (denot__B b) (Intersection _ B (inverse_image F B'))).
        split; try split.
        * apply denot_while__S.
          -- apply Hbody.
          -- simpl. apply Hhelp.
        * rewrite HF. apply HF'.
        * split.
          -- rewrite denotB_true. apply Hbeval.
          -- split.
             ++ apply HB.
             ++ unfold inverse_image, In. rewrite HF. apply HB'.
      (* end of loop *)
      + rewrite denot_loop in H1.
        rewrite Hbeval in H1.
        exists (fun V => V). exists (Complement _ (denot__B b)). repeat split.
        * apply Fam_intro with (i := 0).
          simpl. constructor.
        * inversion H1. reflexivity.
        * rewrite denotB_false. apply Hbeval.
Qed.

Lemma loop_correct: forall i p b F B V0,
    In _ (n_fold i (loop_helper (denot__S p) b p)
         (Singleton _ (fun V => V, Complement Valuation (denot__B b))))
   (F, B) ->
    (forall F' B' V,
        In _ (denot__S p) (F', B') ->
        In _ B' V ->
        exists V', F' V = V'
              /\ denot_fun p V = Some V') ->
    In _ B V0 ->
    exists V,
      F V0 = V
      /\ loop__C (denot_fun p) b V0 = Some V.
Proof.
    induction i; intros.
    - simpl in H. inversion H; subst.
      exists V0. split.
      + reflexivity.
      + apply loop_false. rewrite <- denotB_false. apply H1.
    - destruct (loop_helper_step _ _ _ _ _ _ _ H) as [F' [B' [Hsofar H2]]].
      inversion H2 as [F0 [B0 [Fp [Bp [? [? [? ?]]]]]]].
      simpl in H5, H6. inversion H3. subst.
      inversion H1; inversion H6; subst.
      destruct (H0 Fp Bp V0 H4 H8) as [V' [? ?]].
      destruct (IHi _ _ _ _  (Fp V0) Hsofar H0 H9) as [V'' [? ?]].
      exists V''. split.
      + apply H11.
      + rewrite denot_loop. rewrite H5. rewrite H10; cbn.
        rewrite <- H7. apply H12.
Qed.

Lemma correct: forall p F B V,
    In _ (denot__S p) (F, B) ->
    In _ B V ->
    exists V', F V = V' /\ denot_fun p V = Some V'.
Proof.
    induction p; intros.
    - inversion H; subst.
      exists V. split; reflexivity.
    - inversion H; subst.
      exists (x !-> Aeval V e; V). split; reflexivity.
    - destruct H as [F1 [F2 [B1 [B2 [H1 [H2 [HF HB]]]]]]].
      exists (F2 (F1 V)). split.
      + simpl in HF. rewrite HF. reflexivity.
      + simpl in *.
        rewrite HB in H0. inversion H0; subst.
        destruct (IHp1 F1 B1 V H1 H) as [V1 [? HV1]]. rewrite HV1.
        destruct (IHp2 F2 B2 (F1 V) H2 H3) as [V2 [? HV2]].
        simpl.
        rewrite <- H4. rewrite HV2. rewrite H5.
        reflexivity.
    - simpl. destruct H; destruct (Beval V b) eqn:Hcond.
      (* condition true, left branch*)
      + destruct H as [F1 [B1 [H1 [HF HB]]]].
        simpl in HB. rewrite HB in H0. inversion H0; subst.
        destruct (IHp1 F B1 V H1 H) as [V1 [HF1 HV1]].
        exists V1. split; assumption.
      (* condition false, left branch => contradiction *)
      + destruct H as [F1 [B1 [H1 [HF HB]]]].
        simpl in HB. rewrite HB in H0. inversion H0; subst.
        unfold denot__B, In in H2. rewrite H2 in Hcond.
        discriminate.
      (* condition true, right branch => contradiction*)
      + destruct H as [F2 [B2 [H2 [HF HB]]]].
        simpl in HB. rewrite HB in H0. inversion H0; subst.
        unfold denot__B, In, Complement in H1.
        exfalso. apply H1. apply Hcond.
      (* condition false, right branch *)
      + destruct H as [F2 [B2 [H2 [HF HB]]]].
        simpl in HB. rewrite HB in H0. inversion H0; subst.
        destruct (IHp2 F B2 V H2 H) as [V2 [HF2 HV2]].
        exists V2. split; assumption.
    - inversion H; subst; cbn.
      apply (loop_correct _ _ _ _ _ V H1 IHp H0).
Qed.

(** definition of big step symbolic as partial function *)
Section PartialSymbEx.
  (* Lemma 1 *)
  Hypothesis pairwise_disjoint_preconditions: forall p F B F' B',
      In _ (denot__S p) (F, B) ->
      In _ (denot__S p) (F', B') ->
      Inhabited _ (Intersection _ B B') ->
      (F, B) = (F', B').

  (* Definition 1 *)
  Inductive big_step_partial (p: Stmt):  Valuation -> Valuation -> Prop :=
    | big_step_intro: forall F B v,
        In _ (denot__S p) (F, B) ->
        In _ B v ->
        big_step_partial p v (F v).

  Definition partial_function {X: Type} (R: X -> X -> Prop) :=
           forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

  Lemma complement_disjoint {X: Type}: forall (A: Ensemble X), Disjoint _ A (Complement _ A).
  Proof.
      intros. constructor. intros x contra.
      inversion contra; subst.
      apply H0. apply H.
  Qed.

  Lemma disjoint_not_inhabited {X: Type}: forall (A B: Ensemble X),
      Disjoint _ A B ->
      Inhabited _ (Intersection _ A B) ->
      False.
  Proof.
      intros. inversion H. inversion H0.
      apply (H1 x). apply H2.
  Qed.

  Theorem big_step_is_partial_function: forall p, partial_function (big_step_partial p).
  Proof.
      unfold partial_function. intros.
      inversion H; subst. inversion H0; subst.
      assert (Inhabited _ (Intersection _ B B0)) by
        (apply (Inhabited_intro _ _ x); split; assumption).
      specialize (pairwise_disjoint_preconditions _ _ _ _ _ H1 H3 H5); intros.
      inversion pairwise_disjoint_preconditions.
      reflexivity.
  Qed.

  (* Theorem 1 *)
  Theorem concrete_symbolic_correspondence: forall p v v',
      denot_fun p v = Some v' <-> big_step_partial p v v'.
  Proof.
      split; intros.
      - apply complete in H. destruct H as (F & B & Hin & HF & HB).
        rewrite <- HF.
        apply (big_step_intro p F B v Hin HB).
      - inversion H; subst.
        destruct (correct _ _ _ _ H0 H1) as (v' & HF & Heval).
        subst. apply Heval.
  Qed.
End PartialSymbEx.
