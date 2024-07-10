(** Section 8: Weakest Preconditions for Programs*)

From Coq Require Import Ensembles
  Bool.Bool
  Init.Nat
  Ensembles
  Classical.

From BigStepSymbEx Require Import
  Utils
  Maps
  Expr
  Syntax
  Programs.
Import NonDet NonDetNotations.
Open Scope com_scope.

Inductive DLexpr : Type :=
| DLTrue
| DLFalse
| DLNot (b:DLexpr)
| DLAnd (b1 b2:DLexpr)
| DLLeq (a1 a2:Aexpr)
| DLImpl (b1 b2: DLexpr)
| DLBox (p: Prg) (b: DLexpr).


Notation "x –> y"  := (DLImpl x y) (in custom com at level 70, no associativity).
Notation "[ t ] b"  := (DLBox t b) (in custom com at level 70, no associativity).

Definition DLdiamond (t: Prg) (b: DLexpr) := DLNot (DLBox t (DLNot b)).
Notation "< t > b"  := (DLdiamond t b) (in custom com at level 70, no associativity).

(* Note that this type is equivalent to DLeval e: Ensemble Valuation *)
Fixpoint DLeval (e:DLexpr) (V:Valuation) : Prop :=
  match e with
  | DLTrue => True
  | DLFalse => False
  | DLNot b => ~ (DLeval b V)
  | DLAnd b1 b2 => (DLeval b1 V) /\ (DLeval b2 V)
  | DLImpl b1 b2 => (DLeval b1 V) -> (DLeval b2 V)
  | DLLeq a1 a2 => ((Aeval V a1) <=? (Aeval V a2)) = true
  | <{[p] b}> => forall V', In _ (denot_fun_nondet p V) V' -> DLeval b V'
  end.

(* This lemma is necessarily non-constructive since it involves determining whether p(V) is inhabited*)
Lemma DLeval_diamond: forall V p b,
    DLeval <{<p> b}> V <-> (exists V', In _ (denot_fun_nondet p V) V' /\ DLeval b V').
Proof.
  split.
  - intros.
    cbn in H.
    apply not_all_ex_not in H.
    destruct H as (?V & ?).
    destruct (imply_to_and _ _ H).
    exists V0; split.
    + assumption.
    + apply NNPP; auto.
  - intros (?V & ? & ?).
    cbn.
    intro.
    eapply H1; eauto.
Qed.

Fixpoint DLapply (s:sub) (e:DLexpr) : DLexpr :=
  match e with
  | DLTrue => DLTrue
  | DLFalse => DLFalse
  | DLNot b => DLNot (DLapply s b)
  | DLAnd b1 b2 => DLAnd (DLapply s b1) (DLapply s b2)
  | DLImpl b1 b2 => DLImpl (DLapply s b1) (DLapply s b2)
  | DLLeq a1 a2 => DLLeq (Aapply s a1) (Aapply s a2)
  | <{[t] b}> => DLBox t (DLapply s b)
  end.

(* Same trick as the trace-case *)
Fixpoint embed (b:Bexpr) : DLexpr :=
  match b with
  | BTrue => DLTrue
  | BFalse => DLFalse
  | BNot b => DLNot (embed b)
  | BAnd b1 b2 => DLAnd (embed b1) (embed b2)
  | BImpl b1 b2 => DLImpl (embed b1) (embed b2)
  | BLeq a1 a2 => DLLeq a1 a2
  end.

Lemma DLeval_embed: forall b V,
    DLeval (embed b) V <-> V |= b.
Proof.
  induction b; intros; try easy.
  - cbn.
    now rewrite IHb, negb_true_iff, not_true_iff_false.
  - cbn.
    rewrite IHb1, IHb2.
    now rewrite andb_true_iff.
  - cbn.
    rewrite IHb1, IHb2.
    now rewrite implb_true_iff.
Qed.

Lemma DLapply_embed: forall b s,
    DLapply s (embed b) = embed (Bapply s b).
Proof.
  induction b; intros; try easy.
  - cbn.
    now rewrite IHb.
  - cbn.
    now rewrite IHb1, IHb2.
  - cbn.
    now rewrite IHb1, IHb2.
Qed.

Definition big_conjunction (F:Ensemble Branch) (ψ: Bexpr): Ensemble Valuation :=
  fun V => forall '(σ, φ), In _ F (σ, φ) -> DLeval (DLImpl (embed φ) (DLapply σ (embed ψ))) V.

(* Theorem 5 *)
Lemma box_weakest_precond: forall p ψ,
    DLeval (DLBox p (embed ψ)) = big_conjunction (denot__S p) ψ.
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; intros ?V ?.
  - intros (σ & φ) ?.
    intro.
    rewrite DLeval_embed in H1.
    pose proof SE_correct _ V _ _ H0 H1 as CORRECT.
    cbn in H.
    apply H in CORRECT.
    rewrite DLeval_embed in CORRECT.
    rewrite DLapply_embed, DLeval_embed.
    rewrite <- comp_subB.
    apply CORRECT.
  - intros ?V ?.
    rewrite DLeval_embed.
    pose proof SE_complete _ _ _ H0 as (σ & φ & ? & ? & <-).
    unfold big_conjunction, In in H, H1.
    pose proof H (σ, φ) H1.
    cbn in H3.
    rewrite DLeval_embed in H3.
    apply H3 in H2.
    rewrite DLapply_embed, DLeval_embed in H2.
    rewrite <- comp_subB in H2.
    apply H2.
Qed.

Definition big_disjunction (F: Ensemble Branch) (ψ: Bexpr): Ensemble Valuation :=
  fun V => exists '(σ, φ), In _ F (σ, φ) /\ DLeval (DLAnd (embed φ) (DLapply σ (embed ψ))) V.

(* Theorem 6 *)
Lemma diamond_weakest_precond: forall p ψ,
    DLeval (DLdiamond p (embed ψ)) = big_disjunction (denot__S p) ψ.
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; intros ?V ?.
  - apply DLeval_diamond in H.
    destruct H as (?V & ? & ?).
    pose proof SE_complete _ _ _ H as (σ & φ & ? & ? & <-).
    exists (σ, φ).
    split; auto.
    cbn.
    rewrite DLapply_embed, 2 DLeval_embed.
    split; auto.
    rewrite DLeval_embed in H0.
    rewrite <- comp_subB.
    apply H0.
  - destruct H as ((?σ&?φ) & ? & ?).
    cbn in H0.
    destruct H0.
    rewrite DLeval_embed in H0.
    pose proof SE_correct _ _ _ _ H H0.
    apply DLeval_diamond.
    exists ([|σ|] V).
    split; auto.
    rewrite DLeval_embed.
    rewrite DLapply_embed, DLeval_embed in H1.
    rewrite <- comp_subB in H1.
    apply H1.
Qed.

(* Corollary 2 *)
Corollary arbitrary_precond: forall W p ψ,
    Included _ W (denot__S p) ->
    Included _ (big_disjunction W ψ) (DLeval (DLdiamond p (embed ψ))).
Proof.
  intros.
  intros ?V ((σ&φ) & ? & ?).
  apply H in H0.
  rewrite (diamond_weakest_precond p ψ).
  exists (σ, φ).
  split; auto.
Qed.

Type diamond_weakest_precond.
Print Assumptions diamond_weakest_precond.

Type box_weakest_precond.
Print Assumptions box_weakest_precond.
