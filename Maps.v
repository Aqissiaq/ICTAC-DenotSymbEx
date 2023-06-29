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

Lemma asgn_sound : forall V s x e,
    Comp V (update s x (Aapply s e)) = update (Comp V s) x (Aeval (Comp V s) e).
Proof. intros. extensionality y.
       unfold Comp. unfold update. destruct (eqb x y);
         try (rewrite <- comp_sub; unfold Comp);
         reflexivity.
Qed.

Lemma comp_id : forall V,
    Comp V id_sub = V.
Proof. intros. extensionality x. reflexivity. Qed.
