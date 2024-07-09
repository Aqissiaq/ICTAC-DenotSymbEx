(** Section 4: Weakest Preconds*)

From Coq Require Import Ensembles
         Bool.Bool
  Init.Nat.

From BigStepSymbEx Require Import
  Utils
  Maps
  Expr
  Syntax
  Traces.
Import Trace.

Inductive DLexpr : Type :=
| DLTrue
| DLFalse
| DLNot (b:DLexpr)
| DLAnd (b1 b2:DLexpr)
| DLLeq (a1 a2:Aexpr)
| DLImpl (b1 b2: DLexpr)
| DLBox (t: Trc) (b: DLexpr).


Notation "x –> y"  := (DLImpl x y) (in custom com at level 70, no associativity).
Notation "[ t ] b"  := (DLBox t b) (in custom com at level 70, no associativity).

Definition DLdiamond (t: Trc) (b: DLexpr) := DLNot (DLBox t (DLNot b)).
Notation "< t > b"  := (DLdiamond t b) (in custom com at level 70, no associativity).

Fixpoint DLeval (V:Valuation) (e:DLexpr) : bool :=
  match e with
  | DLTrue => true
  | DLFalse => false
  | DLNot b => negb (DLeval V b)
  | DLAnd b1 b2 => (DLeval V b1) && (DLeval V b2)
  | DLImpl b1 b2 => implb (DLeval V b1) (DLeval V b2)
  | DLLeq a1 a2 => (Aeval V a1) <=? (Aeval V a2)
  | <{[t] b}> => match denot_fun t V with
                | None => true
                | Some V' => DLeval V' b
                end
  end.

Lemma DLdiamond_charact: forall V t b,
    DLeval V <{<t> b}> = match denot_fun t V with
                         | None => false
                         | Some V' => DLeval V' b
                         end.
Proof.
  intros.
  cbn.
  destruct (denot_fun t V); auto.
  apply negb_involutive.
Qed.

Lemma DLeval_diamond: forall V t b,
    DLeval V <{<t> b}> = true <-> (exists V', denot_fun t V = Some V' /\ DLeval V' b = true).
Proof.
  split; intros.
  - cbn in H.
    destruct (denot_fun t V).
    + apply negb_true_iff in H.
      apply negb_false_iff in H.
      now exists v.
    + discriminate.
  - cbn.
    now destruct H as (?V & -> & ->).
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

(* This is not exactly elegant, but it lets us reuse results about Beval and
Bapply and easily restrict to non-modal formulae *)
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
    DLeval V (embed b) = Beval V b.
Proof.
  induction b; intros; try easy.
  - cbn.
    now rewrite IHb.
  - cbn.
    now rewrite IHb1, IHb2.
  - cbn.
    now rewrite IHb1, IHb2.
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

(* Lemma 6 *)
Lemma box_weakest_precond: forall t ψ V,
    DLeval V (DLBox t (embed ψ)) = DLeval V (DLImpl (embed (PC t)) (DLapply (Sub t) (embed ψ))).
Proof.
  induction t; intros; cbn;
    rewrite  DLapply_embed, 2 DLeval_embed.
  - now rewrite Bapply_id.
  - rewrite <- comp_subB.
    now rewrite <- asgn_sound'.
  - destruct (Beval V b); auto.
    rewrite Bapply_id.
    now rewrite DLeval_embed.
  - PC_spec_unfold (TSeq t1 t2).
    apply PC_spec_correct in H3, H4; subst.
    Sub_spec_unfold  (TSeq t1 t2).
    apply Sub_spec_correct in H5, H6; subst.
    destruct (denot_fun t1 V) as [?V | ] eqn:?; cbn.
    + pose proof trace_correspondence t1 V V0 as (SOUND1 &_).
      destruct (SOUND1 Heqo) as (? & ?).
      destruct (denot_fun t2 V0) as [?V | ] eqn:?; cbn.
      * pose proof trace_correspondence t2 V0 as (SOUND2 &_).
        destruct (SOUND2 Heqo0) as (? & ?).
        specialize (IHt1 ψ V).
        specialize (IHt2 ψ V0).
        cbn in IHt1, IHt2.
        cbn.
        rewrite <- comp_subB.
        unfold denot_sub in H3; subst.
        rewrite H1, H5.
        cbn.
        rewrite DLeval_embed.
        rewrite <- Bapply_compose.
        unfold denot_sub.
        now rewrite 2 comp_subB.
      * pose proof trace_correspondence_none t2 V0 as (SOUND2 &_).
        specialize (IHt1 ψ V).
        specialize (IHt2 ψ V0).
        cbn in IHt1, IHt2.
        unfold denot_sub in H3; subst.
        apply SOUND2 in Heqo0.
        rewrite <- comp_subB.
        now rewrite H1, Heqo0.
    + pose proof trace_correspondence_none t1 V as (SOUND1 &_).
      rewrite SOUND1; auto.
Qed.

(* Lemma 6 *)
Lemma diamond_weakest_precond: forall t ψ V,
    DLeval V (DLdiamond t (embed ψ)) = DLeval V (DLAnd (embed (PC t)) (DLapply (Sub t) (embed ψ))).
Proof.
  induction t; intros; cbn;
    rewrite  DLapply_embed, 2 DLeval_embed.
  - now rewrite Bapply_id, negb_involutive.
  - rewrite <- comp_subB, <- asgn_sound'.
    now rewrite negb_involutive.
  - destruct (Beval V b); auto.
    now rewrite Bapply_id, negb_involutive, DLeval_embed.
  - PC_spec_unfold (TSeq t1 t2).
    apply PC_spec_correct in H3, H4; subst.
    Sub_spec_unfold  (TSeq t1 t2).
    apply Sub_spec_correct in H5, H6; subst.
    destruct (denot_fun t1 V) as [?V | ] eqn:?; cbn.
    + pose proof trace_correspondence t1 V V0 as (SOUND1 &_).
      destruct (SOUND1 Heqo) as (? & ?).
      destruct (denot_fun t2 V0) as [?V | ] eqn:?; cbn.
      * pose proof trace_correspondence t2 V0 as (SOUND2 &_).
        destruct (SOUND2 Heqo0) as (? & ?).
        specialize (IHt1 ψ V).
        specialize (IHt2 ψ V0).
        cbn in IHt1, IHt2.
        cbn.
        rewrite <- comp_subB.
        unfold denot_sub in H3; subst.
        rewrite H1, H5.
        cbn.
        rewrite negb_involutive, DLeval_embed.
        rewrite <- Bapply_compose.
        unfold denot_sub.
        now rewrite 2 comp_subB.
      * pose proof trace_correspondence_none t2 V0 as (SOUND2 &_).
        specialize (IHt1 ψ V).
        specialize (IHt2 ψ V0).
        cbn in IHt1, IHt2.
        unfold denot_sub in H3; subst.
        apply SOUND2 in Heqo0.
        rewrite <- comp_subB.
        now rewrite H1, Heqo0.
    + pose proof trace_correspondence_none t1 V as (SOUND1 &_).
      rewrite SOUND1; auto.
Qed.

(*TODO: Prop 1? *)
