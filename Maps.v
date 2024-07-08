(** * Substitutions and Valuations *)

From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Logic.FunctionalExtensionality. (* for equality of substitutions *)

From BigStepSymbEx Require Import Expr.

Class HasEqb (X: Type) :=
  { eqb : X -> X -> bool ;
    eqb_spec : forall x y, reflect (x = y) (eqb x y)
  }.

#[global] Instance string_eqb: HasEqb string :=
  { eqb := String.eqb ;
    eqb_spec := String.eqb_spec
  }.

#[global] Instance nat_eqb: HasEqb nat :=
  { eqb := Nat.eqb ;
    eqb_spec := Nat.eqb_spec
  }.

Lemma eqb_refl {X:Type} `{HasEqb X}: forall (x:X), eqb x x = true.
Proof. intros. destruct (eqb_spec x x).
       - reflexivity.
       - contradiction.
Qed.

Lemma eqb_neq {X:Type} `{HasEqb X}: forall x y, eqb x y = false <-> x <> y.
Proof. intros. destruct (eqb_spec x y); split;
         [discriminate | contradiction | auto | auto ].
Qed.

Section TotalMaps.
  Context {X A: Type}
    `{HasEqb X}.

  Definition total_map: Type := X -> A.

  Definition update (s: total_map) (x:X) (e:A) : total_map :=
    fun y => if eqb x y then e else s y.

  Notation "x '!->' v ';' m" := (update m x v) (at level 100, v at next level, right associativity).

  Definition empty_map (x:A): total_map := fun _ => x.
  Notation "'_' '!->' v" := (empty_map v) (at level 100, right associativity).

  Lemma apply_empty : forall x v,
      (_ !-> v) x = v.
  Proof. intros. unfold empty_map. reflexivity. Qed.

  Lemma update_eq : forall x m v,
      (x !-> v ; m) x = v.
  Proof. intros. unfold update. rewrite eqb_refl. reflexivity. Qed.

  Theorem update_neq : forall (m : total_map) x y v,
      x <> y ->
      (x !-> v ; m) y = m y.
  Proof.
    intros. unfold update. destruct (eqb_spec x y).
    - contradiction.
    - reflexivity.
  Qed.

  Lemma equal_maps {m m' : total_map} :
    m = m' -> forall x, m x = m' x.
  Proof. intros. subst. reflexivity. Qed.

  Lemma update_shadow : forall (m : total_map) x v1 v2,
      (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
  Proof.
    intros. extensionality y. unfold update.
    destruct (eqb x y); reflexivity.
  Qed.

  Lemma update_comm: forall m x1 x2 v1 v2,
      x1 <> x2 -> (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m).
  Proof.
    intros. extensionality y. unfold update.
    destruct (eqb_spec x1 y); destruct (eqb_spec x2 y);
      try reflexivity.
    exfalso. apply H0. rewrite e, e0. reflexivity.
  Qed.
End TotalMaps.

(* notation is not allowed to escape sections atm *)
(*https://github.com/coq/coq/issues/11672*)
Notation "x '!->' v ';' m" := (update m x v) (at level 100, v at next level, right associativity).
Notation "'_' '!->' v" := (empty_map v) (at level 100, right associativity).

(* substitions map to (Arithmetic) expressions*)
Definition sub : Type := @total_map string Aexpr.
Definition id_sub : sub := fun x => x.

(* valuations map to concrete values *)
Definition Valuation := @total_map string nat.

Fixpoint Aapply (s:sub) (e:Aexpr) : Aexpr :=
  match e with
  | AConst n => AConst n
  | AVar x => s x
  | APlus a1 a2 => APlus (Aapply s a1) (Aapply s a2)
  end.

Lemma Aapply_id : forall e,
    Aapply id_sub e = e.
Proof.
  induction e; try reflexivity.
  simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Fixpoint Bapply (s:sub) (e:Bexpr) : Bexpr :=
  match e with
  | BTrue => BTrue
  | BFalse => BFalse
  | BNot b => BNot (Bapply s b)
  | BAnd b1 b2 => BAnd (Bapply s b1) (Bapply s b2)
  | BLeq a1 a2 => BLeq (Aapply s a1) (Aapply s a2)
  end.

Lemma Bapply_id : forall e,
    Bapply id_sub e = e.
Proof.
  induction e; simpl;
    try (rewrite IHe);
    try (rewrite IHe1; rewrite IHe2);
    try (repeat rewrite Aapply_id);
    try reflexivity.
Qed.

Fixpoint Aeval (V:Valuation) (e:Aexpr) : nat :=
  match e with
  | AConst n => n
  | AVar x => V x
  | APlus a1 a2 => (Aeval V a1) + (Aeval V a2)
  end.

Fixpoint Beval (V:Valuation) (e:Bexpr) : bool :=
  match e with
  | BTrue => true
  | BFalse => false
  | BNot b => negb (Beval V b)
  | BAnd b1 b2 => (Beval V b1) && (Beval V b2)
  | BLeq a1 a2 => (Aeval V a1) <=? (Aeval V a2)
  end.

Notation "V |= b" := (Beval V b = true) (at level 90).
Notation "V |/= b" := (Beval V b = false) (at level 90).

(** We can update a valuation with a substitution by composition
      and prove some useful properties *)

Definition Comp (V:Valuation) (s:sub) : Valuation :=
  fun x => Aeval V (s x).

Lemma comp_sub : forall V s e,
    Aeval (Comp V s) e = Aeval V (Aapply s e).
Proof.
  induction e; simpl;
    try (rewrite IHe1; rewrite IHe2); reflexivity.
Qed.

Lemma comp_subB : forall V s e,
    Beval (Comp V s) e = Beval V (Bapply s e).
Proof.
  induction e; simpl;
    try (rewrite IHe1; rewrite IHe2);
    try (rewrite IHe);
    try (repeat (rewrite comp_sub));
    reflexivity.
Qed.

Lemma comp_id : forall V,
    Comp V id_sub = V.
Proof. intros. extensionality x. reflexivity. Qed.

Lemma asgn_sound : forall V s x e,
    Comp V (update s x (Aapply s e)) = update (Comp V s) x (Aeval (Comp V s) e).
Proof. intros. extensionality y.
       unfold Comp. unfold update. destruct (eqb x y);
         try (rewrite <- comp_sub; unfold Comp);
         reflexivity.
Qed.

Lemma asgn_sound': forall V x e,
    (Comp V (x !-> e ; id_sub)) = (x !-> Aeval V e ; V).
Proof.
  intros.
  pose proof asgn_sound V id_sub x e.
  rewrite comp_id, Aapply_id in H.
  apply H.
Qed.

Definition denot_sub (phi: sub): Valuation -> Valuation := fun V => Comp V phi.
Notation "[| s |]" := (denot_sub s).

Lemma denot_id_sub: denot_sub id_sub = fun V => V.
Proof. unfold denot_sub. extensionality V. rewrite comp_id. reflexivity. Qed.

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

Lemma compose_subs_assoc: forall σ1 σ2 σ3,
    compose_subs σ1 (compose_subs σ2 σ3) = compose_subs (compose_subs σ1 σ2) σ3.
Proof.
  intros.
  extensionality y.
  unfold compose_subs.
  induction (σ3 y); cbn; auto.
  now rewrite IHa1, IHa2.
Qed.

Lemma compose_comp: forall V s s',
    Comp V (compose_subs s s') = (fun x => Comp (Comp V s) s' x).
Proof.
  intros.
  extensionality x.
  unfold Comp, compose_subs.
  induction (s' x); simpl; auto.
Qed.

Lemma compose_sub_spec: forall s1 s2,
    [| compose_subs s1 s2 |] = fun V => [| s2 |] ([| s1 |] V).
Proof.
  intros.
  extensionality V.
  unfold denot_sub.
  now rewrite compose_comp.
Qed.

Lemma asgn_compose: forall σ x e,
    (update σ x (Aapply σ e)) = compose_subs σ (x !-> e ; id_sub).
Proof.
  intros.
  extensionality y.
  unfold compose_subs, update.
  now destruct (eqb x y).
Qed.

Lemma asgn_compose': forall σ σ' x e,
    (x !-> Aapply (compose_subs σ σ') e; compose_subs σ σ') = compose_subs σ (x !-> Aapply σ' e; σ').
Proof.
  intros.
  extensionality y.
  unfold compose_subs, update.
  destruct (eqb x y); auto.
  induction e; cbn; auto.
  now rewrite IHe1, IHe2.
Qed.

Lemma Aapply_compose: forall σ σ' e,
    Aapply σ (Aapply σ' e) = Aapply (compose_subs σ σ') e.
Proof.
  intros.
  induction e; auto; cbn.
  now rewrite IHe1, IHe2.
Qed.

Lemma Bapply_compose: forall σ σ' b,
    Bapply σ (Bapply σ' b) = Bapply (compose_subs σ σ') b.
Proof.
  intros.
  induction b; cbn; auto.
  - now rewrite IHb.
  - now rewrite IHb1, IHb2.
  - now rewrite 2 Aapply_compose.
Qed.

From Coq Require Import Ensembles.
Definition denot__B (b: Bexpr): Ensemble Valuation := fun V => Beval V b = true.
Notation "{| b |}" := (denot__B b).
Open Scope com_scope.

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

Create HintDb denotB.

#[export] Hint Rewrite denotB_true denotB_false denotB_top denotB_bot denotB_neg denotB_and
  : denotB.
