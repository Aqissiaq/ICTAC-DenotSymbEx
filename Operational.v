From Coq Require Import
  Program.Equality
  Relations
  Classes.RelationClasses
  Logic.FunctionalExtensionality
  Ensembles.

From BigStepSymbEx Require Import
  Utils
  Expr
  Syntax
  Maps
  Programs
  Traces
.
Import Trace.
Import NonDet NonDetNotations.

Open Scope com_scope.

Definition SConfig : Type := Prg * sub * Bexpr.

Reserved Notation " c '->s' c' " (at level 40).

(* Figure 3 *)
Inductive Sstep : relation SConfig :=
| Asgn_step : forall x e sig phi,
    (<{ x := e }>, sig , phi) ->s (PSkip, (update sig x (Aapply sig e)), phi)
| Asrt_step : forall b sig phi,
    (<{ b? }>, sig, phi) ->s (PSkip, sig, BAnd phi (Bapply sig b))
| Skip_step : forall p sig phi,
    (<{skip ; p}>, sig, phi) ->s (p, sig, phi)
| Seq_step : forall p p' q sig sig' phi phi',
    (p, sig, phi) ->s (p', sig', phi') ->
    (<{p ; q}>, sig, phi) ->s (<{p' ; q}>, sig', phi')
| Ndet_step_l : forall p q sig phi,
    (<{p (+) q}>, sig, phi) ->s (p, sig, phi)
| Ndet_step_r : forall p q sig phi,
    (<{p (+) q}>, sig, phi) ->s (q, sig, phi)
| Loop_step_halt : forall p sig phi,
    (<{p*}>, sig, phi) ->s (PSkip, sig, phi)
| Loop_step_unfold: forall p sig phi,
    (<{p*}>, sig, phi) ->s (<{p ; p*}>, sig, phi)
  where " c '->s' c' " := (Sstep c c').

Lemma Asgn': forall p q σ σ' φ φ' x e,
    p = <{x := e}> ->
    q = PSkip ->
    σ' = (update σ x (Aapply σ e)) ->
    φ' = φ ->
    (p, σ, φ) ->s (q, σ', φ').
Proof.
  intros.
  subst.
  apply Asgn_step.
Qed.

Lemma Asrt': forall p q σ σ' φ φ' b,
    p = <{b?}> ->
    q = PSkip ->
    σ' = σ ->
    φ' = BAnd φ (Bapply σ b) ->
    (p, σ, φ) ->s (q, σ', φ').
Proof.
  intros.
  subst.
  apply Asrt_step.
Qed.

Definition multi_Sstep := clos_refl_trans_n1 _ Sstep.
Notation " c '->*' c' " := (multi_Sstep c c') (at level 40).

(* Lemma 10 *)
Lemma if_T: forall b p q sig phi,
    (encode (If b p q), sig, phi) ->* (encode p, sig, BAnd phi (Bapply sig b)).
Proof.
  cbn;intros.
  apply clos_rt1n_rtn1.
  econstructor.
  { apply Ndet_step_l. }
  econstructor.
  { do 2 constructor. }
  econstructor.
  { do 2 constructor. }
  constructor.
Qed.

Lemma if_F: forall b p q sig phi,
    (encode (If b p q), sig, phi) ->* (encode q, sig, BAnd phi (Bapply sig <{~b}>)).
Proof.
  cbn;intros.
  apply clos_rt1n_rtn1.
  econstructor.
  { apply Ndet_step_r. }
  econstructor.
  { do 2 constructor. }
  econstructor.
  { do 2 constructor. }
  constructor.
Qed.

Lemma while_T: forall b p sig phi,
    (encode (While b p), sig, phi) ->* (encode (Seq p (While b p)), sig, BAnd phi (Bapply sig b)).
Proof.
  cbn;intros.
  apply clos_rt1n_rtn1.
  econstructor.
  { econstructor; apply Loop_step_unfold. }
  econstructor.
  { do 3 econstructor.
    apply Asrt_step.
  }
  econstructor.
  { do 3 constructor. }
  rewrite Prg_assoc. (*<- note this dependence on syntactic associativity of Seq *)
  constructor.
Qed.

Lemma while_F: forall b p sig phi,
    (encode (While b p), sig, phi) ->* (encode Skip, sig, BAnd phi (Bapply sig <{~b}>)).
Proof.
  cbn;intros.
  apply clos_rt1n_rtn1.
  econstructor.
  { econstructor; apply Loop_step_halt. }
  econstructor.
  { constructor. }
  econstructor.
  { constructor. }
  now constructor.
Qed.

Definition In': Ensemble Branch -> Branch -> Prop :=
  fun F '(σ, φ) => exists φ', In _ F (σ, φ') /\ {| φ |} = {| φ' |}.

Definition multi_Sstep': relation SConfig :=
  fun '(p, σ, φ) '(q, σ', φ') => exists φ'', (p, σ, φ) ->* (q, σ', φ'') /\ {| φ'' |} = {| φ' |}.
Notation " c '=>*' c' " := (multi_Sstep' c c') (at level 40).

Lemma step_to_step': forall p q σ σ' φ φ',
    (p, σ, φ) ->* (q, σ', φ') ->
    (p, σ, φ) =>* (q, σ', φ').
Proof.
  intros.
  exists φ'.
  split; auto.
Qed.

(*NOTE: Erik claims iff, but I don't think the condition on φ is strong enough *)
Lemma canonical_SE_step: forall p q σ σ' φ φ',
    (p, σ, φ) ->s (q, σ', φ') -> exists σc φc,
        (p, id_sub, BTrue) ->s (q, σc, φc)
      /\ (σ' = compose_subs σ σc)
      /\ ({| φ' |} = {| BAnd φ (Bapply σ φc) |}).
Proof.
  intros.
  dependent induction H.
  + eexists. eexists.
    splits.
    * constructor.
    * rewrite Aapply_id.
      now rewrite asgn_compose.
    * cbn.
      now rewrite denotB_and, denotB_top, intersect_comm, intersect_full.
  + eexists. exists (BAnd BTrue (Bapply id_sub b)).
    splits.
    * constructor.
    * now rewrite compose_subs_id'.
    * cbn.
      now rewrite Bapply_id, 3 denotB_and, denotB_top, intersect_full.
  + eexists. eexists.
    splits.
    * constructor.
    * now rewrite compose_subs_id'.
    * cbn.
      now rewrite denotB_and, denotB_top, intersect_comm, intersect_full.
  + pose proof IHSstep _ _ _ _ _ _ JMeq_refl JMeq_refl as (σc & φc & ? & ? & ?).
    eexists. eexists.
    splits.
    * constructor; eauto.
    * assumption.
    * assumption.
  + eexists. eexists.
    splits.
    * apply Ndet_step_l.
    * now rewrite compose_subs_id'.
    * cbn.
      now rewrite denotB_and, denotB_top, intersect_comm, intersect_full.

  + eexists. eexists.
    splits.
    * apply Ndet_step_r.
    * now rewrite compose_subs_id'.
    * cbn.
      now rewrite denotB_and, denotB_top, intersect_comm, intersect_full.

  + eexists. eexists.
    splits.
    * apply Loop_step_halt.
    * now rewrite compose_subs_id'.
    * cbn.
      now rewrite denotB_and, denotB_top, intersect_comm, intersect_full.

  + eexists. eexists.
    splits.
    * apply Loop_step_unfold.
    * now rewrite compose_subs_id'.
    * cbn.
      now rewrite denotB_and, denotB_top, intersect_comm, intersect_full.
Qed.

Lemma SE_canonical_step: forall p q σ σ' φ φ',
    (exists σc φc,
        (p, id_sub, BTrue) ->s (q, σc, φc)
                            /\ (σ' = compose_subs σ σc)
                            /\ ({| φ' |} = {| BAnd φ (Bapply σ φc) |})) ->
    (p, σ, φ) ->s (q, σ', φ').
Proof.
  intros.
  destruct H as (?σ & ?φ & ? & ? & ?).
  dependent induction H.
  - eapply Asgn'; eauto.
    + rewrite H0, Aapply_id.
      now rewrite asgn_compose.
    + cbn in H1.
    (* we need *equal* path conditions, but hypothesis only gives equivalent *)
Abort.

Lemma canonical_soundness_step: forall p q σ φ σ' φ',
    (p, id_sub, BTrue) ->s (q, σ, φ) ->
    In _ (denot__S q) (σ', φ') ->
    In' (denot__S p) (compose_subs σ σ', BAnd φ (Bapply σ φ')).
Proof.
  induction p; intros; inv H.
  - destruct H0 as (?t & ? & -> & ->).
    inv H0; cbn in *.
    exists BTrue.
    splits.
    exists (TAsgn x e).
    splits; cbn.
    now rewrite asgn_compose, compose_subs_id, compose_subs_id'.

  - destruct H0 as (?t & ? & -> & ->).
    inv H0; cbn in *.
    exists <{ b }>.
    split.
    + exists (TAsrt b).
      splits.
    + now rewrite 2 denotB_and, Bapply_id, denotB_top, intersect_full, intersect_comm, intersect_full.

  - exists <{BTrue && φ'}>.
    split.
    + rewrite compose_subs_id.
      destruct H0 as (?t & ? & -> & ->).
      exists (TSeq TSkip t).
      splits.
      exists TSkip, t.
      splits; auto.
      now rewrite Sub_skip_unit_l.
      rewrite pc_trace_app; cbn.
      now rewrite Bapply_id.
    + now rewrite Bapply_id, denotB_and, denotB_top, intersect_full.

  - destruct H0 as (?t & ? & -> & ->).
    destruct H0 as (?u & ?v & ? & ? & ->).
    assert (In _ (denot__S p') (Sub u, PC u)). {
      eexists; splits; eauto.
    }
    epose proof IHp1 _ _ _ _ _ H2 H3 as (?φ & ? & ?).
    destruct H4 as (?t & ? & ? & ->).
    exists (PC (TSeq t v)).
    split.
    + exists (TSeq t v).
      splits.
      * exists t,v.
        splits; auto.
      * now rewrite 2 sub_trace_app, <- H6, compose_subs_assoc.
    + rewrite 2 pc_trace_app.
      rewrite 2 denotB_and.
      rewrite <- H5, <- H6.
      rewrite denotB_and.
      rewrite 3 inverse_denotB.
      rewrite denotB_and.
      rewrite inverse_denotB.
      rewrite compose_sub_spec.
      rewrite <- intersect_assoc.
      rewrite inverse_intersection.
      now rewrite inverse_inverse.
  (* ^eww, but it works *)

  - exists φ'.
    split.
    + rewrite compose_subs_id.
      destruct H0 as (?t & ? & -> & ->).
      exists t.
      splits.
      left; auto.
    + now rewrite Bapply_id, denotB_and, denotB_top, intersect_full.

  - exists φ'.
    split.
    + rewrite compose_subs_id.
      destruct H0 as (?t & ? & -> & ->).
      exists t.
      splits.
      right; auto.
    + now rewrite Bapply_id, denotB_and, denotB_top, intersect_full.

  - destruct H0 as (?t & ? & -> & ->).
    inv H0.
    rewrite compose_subs_id.
    exists BTrue.
    splits.
    eexists.
    splits; auto.
    exists 0; auto.


  - exists φ'.
    split.
    + rewrite compose_subs_id.
      destruct H0 as (?t & ? & -> & ->).
      rewrite denotS_spec_unfold.
      right.
      exists t.
      splits; auto.
    + now rewrite Bapply_id, denotB_and, denotB_top, intersect_full.
Qed.

(* Corollary 1 *)
Corollary canonical_soundness: forall p q σ σ' φ φ',
    (p, id_sub, BTrue) ->* (q, σ, φ) ->
    In _ (denot__S q) (σ', φ') ->
    In' (denot__S p) (compose_subs σ σ', BAnd φ (Bapply σ φ')).
Proof.
  intros p q σ σ' φ φ' ? ?.
  generalize dependent σ'.
  generalize dependent φ'.
  dependent induction H; intros.
  - destruct H0 as (?t & ? & -> & ->).
    exists (PC t).
    splits.
    exists t.
    splits; auto.
    + now rewrite compose_subs_id.
    + now rewrite Bapply_id, denotB_and, denotB_top, intersect_full.
  - destruct y as ((? & ?) & ?).
    apply canonical_SE_step in H.
    destruct H as (?σ & ?φ & ? & -> & ?).
    epose proof canonical_soundness_step _ _ _ _ _ _ H H1 as (?φ & ? & ?).
    epose proof IHclos_refl_trans_n1 _ _ _ _ JMeq_refl JMeq_refl _ _ H3 as (?φ & ? & ?).
    exists φ2.
    split.
    + now rewrite <- compose_subs_assoc.
    + rewrite <- H6.
      rewrite 2 denotB_and.
      rewrite 2 inverse_denotB.
      rewrite <- H4, H2.
      rewrite 2 denotB_and.
      rewrite 2 inverse_denotB.
      rewrite inverse_intersection.
      rewrite inverse_inverse.
      rewrite compose_sub_spec.
      now rewrite <- intersect_assoc.
Qed.

(* Theorem 4 *)
Theorem soundness: forall p σ φ,
    (p, id_sub, BTrue) ->* (PSkip, σ, φ) ->
    In' (denot__S p) (σ, φ).
Proof.
  intros.
  assert (In _ (denot__S <{ skip }>) (id_sub, BTrue)) by (exists TSkip; split; easy).
  epose proof canonical_soundness _ _ _ _ _ _ H H0 as (?φ & ? & ?).
  eexists φ0.
  split; eauto.
  rewrite <- H2; cbn.
  now rewrite denotB_and, denotB_top, intersect_comm, intersect_full.
Qed.

Lemma trace_to_denotS: forall p t,
    In _ (traces_of p) t ->
    In _ (denot__S p) (Sub t, PC t).
Proof.
  intros.
  exists t; now splits.
Qed.

Lemma seq_star: forall p1 p2 q σ1 σ2 φ1 φ2,
    (p1, σ1, φ1) ->* (p2, σ2, φ2) ->
    (<{p1 ; q}>, σ1, φ1) ->* (<{p2 ; q}>, σ2, φ2).
Proof.
  intros.
  dependent induction H.
  - constructor.
  - destruct y as ((? & ?) &?).
    econstructor.
    + now apply Seq_step; eauto.
    + now apply IHclos_refl_trans_n1.
Qed.

Lemma equiv_pc_step: forall p p' σ σ' φ1 φ1' φ2,
    (p, σ, φ1) ->s (p', σ', φ2) ->
    {| φ1 |} = {| φ1' |} ->
    exists φ2',
      (p, σ, φ1') ->s (p', σ', φ2') /\ {| φ2 |} = {| φ2' |}.
Proof.
  induction p; intros; inv H;
    try (now eexists; split; [econstructor | auto]).
  - eexists.
    split.
    + eapply Asrt'; eauto.
    + now rewrite 2 denotB_and, H0.
  - epose proof IHp1 _ _ _ _ _ _ H2 H0 as (?φ & ? & ?).
    eexists.
    split.
    + econstructor.
      apply H1.
    + auto.
Qed.

Lemma compose_step: forall p p' σ σ' φ φ',
    (p, σ, φ) ->s (p', σ', φ') ->
    forall σ0 φ0,
      (p, compose_subs σ0 σ, BAnd φ0 (Bapply σ0 φ)) ->s (p', compose_subs σ0 σ', BAnd φ0 (Bapply σ0 φ')).
Proof.
  induction p; intros; inv H;
    try (econstructor).
  - eapply Asgn'; eauto.
    now rewrite asgn_compose'.
  - eapply Asrt'; eauto.
    cbn.
    rewrite Bapply_compose.
    now apply BAnd_assoc. (*<- note reliance on syntactic associativity *)
  - apply IHp1; auto.
Qed.

(* this is the remark(s) at the bottom of page 16 *)
Lemma SE_semantic_step: forall p p' p'' σ σ' σ'' φ φ' φ'',
    (p, σ, φ) =>* (p', σ', φ') ->
    (p', σ', φ') ->s (p'', σ'', φ'') ->
    (p, σ, φ) =>* (p'', σ'', φ'').
Proof.
  intros; inv H0;
    (* solves the trivial steps *)
    try (destruct H as (?φ & STAR & PC);
         eexists;
         split;
         [ econstructor; [ |apply STAR ]; constructor
         | apply PC]).
  - destruct H as (?φ & STAR & PC).
    eexists.
    split.
    + econstructor; [ |apply STAR ].
      eapply Asrt'; eauto.
    + now rewrite 2 denotB_and, PC.
  - destruct H as (?φ & STAR & PC).
    destruct (equiv_pc_step _ _ _ _ _ φ0 _ H2) as (?φ & ? & ?); auto.
    eexists.
    split.
    + etransitivity; [ apply STAR| ].
      econstructor; [ | reflexivity ].
      econstructor; eauto.
    + auto.
Qed.

Corollary SE_semantic_trans: forall p p' p'' σ σ' σ'' φ φ' φ'',
    (p, σ, φ) =>* (p', σ', φ') ->
    (p', σ', φ') ->* (p'', σ'', φ'') ->
    (p, σ, φ) =>* (p'', σ'', φ'').
Proof.
  intros.
  induction H0; auto.
  destruct y as ((?& ?) &?), z as ((?& ?) &?).
  eapply SE_semantic_step; eauto.
Qed.

Lemma SE_canonical_step: forall p0 p q s b σ σ0 φ φ0,
    (p0, s, b) ->s (q, σ, φ) ->
    (p, σ0, φ0) =>* (p0, compose_subs σ0 s, BAnd φ0 (Bapply σ0 b)) ->
    (p, σ0, φ0) =>* (q, compose_subs σ0 σ, BAnd φ0 (Bapply σ0 φ)).
  Proof.
    intros.
    generalize dependent p.
    dependent induction H;intros;
      (* solves the trivial steps *)
      try (destruct H0 as (?φ & STAR & PC);
           eexists;
           split;
           [ econstructor; [ |apply STAR ]; constructor
           | apply PC]).

    (* asgn *)
    - destruct H0 as (?φ & STAR & PC).
      eexists.
      split.
      + econstructor; [ |apply STAR ].
        eapply Asgn'; auto.
        now rewrite asgn_compose'.
      + apply PC.
    (* asrt *)
    - destruct H0 as (?φ & STAR & PC).
      eexists.
      split.
      + econstructor; [ |apply STAR ].
        eapply Asrt'; eauto.
      + rewrite 2 denotB_and, PC.
        rewrite denotB_and.
        rewrite 3 inverse_denotB.
        rewrite denotB_and.
        rewrite inverse_intersection.
        rewrite inverse_denotB.
        rewrite inverse_inverse, compose_sub_spec.
        now rewrite intersect_assoc.
    (* sequencing *)
Admitted.

Lemma SE_canonical: forall p q σ φ,
    (p, id_sub, BTrue) ->* (q, σ, φ) ->
    forall σ0 φ0,
      (p, σ0, φ0) =>* (q, compose_subs σ0 σ, BAnd φ0 (Bapply σ0 φ)).
Proof.
  intros.
  dependent induction H.
  - exists φ0.
    split.
    + rewrite compose_subs_id'.
      reflexivity.
    + cbn.
      now rewrite denotB_and, denotB_top, intersect_comm, intersect_full.
  - destruct y as ((? & ?) &?).
    pose proof IHclos_refl_trans_n1 _ _ _ _ JMeq_refl JMeq_refl.
    destruct (H1 σ0 φ0) as (?φ & STAR & PC).
    eapply SE_semantic_step; eauto.
    now apply compose_step.
Qed.

Lemma seq_canonical: forall p1 p2 σ1 σ2 φ1 φ2,
    (p1, id_sub, BTrue) ->* (PSkip, σ1, φ1) ->
    (p2, id_sub, BTrue) ->* (PSkip, σ2, φ2) ->
    (<{ p1; p2 }>, id_sub, BTrue) =>*
      (<{ skip }>, compose_subs σ1 σ2, BAnd φ1 (Bapply σ1 φ2)).
Proof.
  intros.
  revert H0.
  dependent induction H; intros.
  - rewrite compose_subs_id, Bapply_id.
    exists φ2.
    split.
    + apply clos_rt1n_rtn1.
      econstructor.
      * apply Skip_step.
      * apply clos_rtn1_rt1n.
        apply H0.
    + now rewrite denotB_and, denotB_top, intersect_full.
  - destruct y as ((?&?)&?).
    pose proof SE_canonical _ _ _ _ H1 σ1 φ1 as (?φ & ? & ?).
    eexists.
    split.
    + epose proof seq_star _ _ _ _ _ _ _ H0.
      transitivity (<{skip ; p2}>, σ1, φ1).
      * econstructor; [ |apply H4].
        now constructor.
      * apply clos_rt1n_rtn1.
        econstructor.
        apply Skip_step.
        apply clos_rtn1_rt1n.
        apply H2.
    + auto.
Qed.

Lemma loop_complete: forall p t,
    (forall (σ : sub) (φ : Bexpr),
        In _ (denot__S p) (σ, φ) -> (p, id_sub, BTrue) =>* (<{ skip }>, σ, φ)) ->
    In Trc (traces_of <{ p * }>) t ->
    (<{ p * }>, id_sub, BTrue) =>* (<{ skip }>, Sub t, PC t).
Proof.
  intros p t IH H.
  destruct H.
  generalize dependent x.
  induction i; intros.
  - inv H; cbn.
    eexists.
    split.
    + econstructor; [ |reflexivity ].
      apply Loop_step_halt.
    + auto.
  - destruct H as (u & v & ? & ? & ->).
    pose proof IHi _ H0.
    apply trace_to_denotS in H.
    apply IH in H.
    destruct H as (?φ & ? & ?).
    destruct H1 as (?φ & ? & ?).
    pose proof seq_canonical _ _ _ _ _ _ H H1 as (?φ & ? & ?).
    eexists φ1.
    split.
    + transitivity (<{ p ; p* }>, id_sub, BTrue).
      { econstructor; [ |reflexivity ]. constructor. }
      rewrite sub_trace_app.
      apply H4.
    + rewrite pc_trace_app.
      rewrite H5.
      rewrite 2 denotB_and.
      rewrite H2.
      rewrite 2 inverse_denotB.
      now rewrite H3.
Qed.

(* Theorem 5 *)
Theorem completeness : forall p σ φ,
    In _ (denot__S p) (σ, φ) ->
    (p, id_sub, BTrue) =>* (PSkip, σ, φ).
Proof.
  induction p; intros.
  - destruct H as (t & DENOT & -> & ->).
    inv DENOT.
    eexists.
    split; eauto.
    cbn; constructor.
  - destruct H as (t & DENOT & -> & ->).
    inv DENOT.
    eexists.
    split; auto.
    cbn.
    econstructor; [ | reflexivity ].
    eapply Asgn' with (σ:=id_sub); eauto.
    now rewrite Aapply_id.
  - destruct H as (t & DENOT & -> & ->).
    inv DENOT.
    exists <{BTrue && b}>.
    split; auto.
    cbn.
    econstructor; [ | reflexivity ].
    eapply Asrt' with (φ:=BTrue) (b:=b); eauto.
    now rewrite Bapply_id.
  - rewrite denotS_spec_seq in H.
    destruct H as (σp & σq & φp & φq & ? & ? & -> & ->).
    apply IHp1 in H.
    apply IHp2 in H0.
    destruct H as (?φ & ? & ?).
    destruct H0 as (?φ & ? & ?).
    assert (In _ (denot__S <{ skip }>) (id_sub, BTrue)) as SKIP by (exists TSkip; split; easy).
    pose proof canonical_soundness _ _ _ _ _ _ H SKIP as (?φ & ? & ?).
    pose proof canonical_soundness _ _ _ _ _ _ H0 SKIP as (?φ & ? & ?).
    pose proof seq_canonical _ _ _ _ _ _ H H0 as (?φ & ? & ?).
    eexists φ3.
    split.
    + apply H7.
    + rewrite H8.
      rewrite 2 denotB_and.
      rewrite H1.
      rewrite 2 inverse_denotB.
      now rewrite H2.
  - destruct H as (t & DENOT & -> & ->).
    inv DENOT.
    + apply trace_to_denotS in H.
      apply IHp1 in H.
      destruct H as (?φ & ? & ?).
      exists φ.
      split; auto.
      etransitivity; [ | apply H ].
      econstructor; [ |reflexivity ].
      apply Ndet_step_l.
    + apply trace_to_denotS in H.
      apply IHp2 in H.
      destruct H as (?φ & ? & ?).
      exists φ.
      split; auto.
      etransitivity; [ | apply H ].
      econstructor; [ |reflexivity ].
      apply Ndet_step_r.
  - destruct H as (t & DENOT & -> & ->).
    now apply loop_complete.
Qed.

Print Assumptions soundness.
Print Assumptions completeness.
