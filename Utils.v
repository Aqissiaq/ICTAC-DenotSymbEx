From Coq Require Import
  Ensembles.

From BigStepSymbEx Require Import
  Maps.

Ltac inv H := inversion H; subst.
Ltac splits := repeat split.

Section EnsembleHelpers.
  Context {X Y Z: Type}.

  Definition set_compose (f: X -> Ensemble Y) (g: Y -> Ensemble Z): X -> Ensemble Z :=
    fun x z => exists y, In _ (f x) y /\ In _ (g y) z.

  Variable A B C: Ensemble X.

  Lemma intersect_full: Intersection X (Full_set _) A = A.
  Proof.
    intros. apply Extensionality_Ensembles. split; intros x H.
    - destruct H; assumption.
    - split; [constructor | assumption].
  Qed.

  Lemma intersect_full': Intersection X A (Full_set _) = A.
  Proof.
    intros. apply Extensionality_Ensembles. split; intros x H.
    - destruct H; assumption.
    - split; [assumption | constructor].
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

  Definition inverse_image {X: Type} (F: X -> X) (B: Ensemble X): Ensemble X := fun x => B (F x).

  (* characterizing inverse images *)
  Lemma inverse_id : forall (A: Ensemble X), inverse_image (fun x => x)  A = A.
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

  Inductive Union_Fam {X I} (Fs: I -> Ensemble X): Ensemble X :=
    | Fam_intro: forall {i x}, In _ (Fs i) x -> In _ (Union_Fam Fs) x.

Lemma set_compose_singleton (f: X -> Ensemble Y) (g: Y -> Ensemble Z):
  forall x y z, f x = Singleton _ y -> g y = Singleton _ z ->
           set_compose f g x = Singleton _ z.
Proof.
  intros.
  apply Extensionality_Ensembles.
  split; intros ? ?.
  - inv H1.
    destruct H2.
    rewrite H in H2.
    inv H2.
    rewrite H0 in H3.
    inv H3.
    easy.
  - inv H1.
    unfold set_compose.
    unfold In.
    exists y.
    split.
    + now rewrite H.
    + now rewrite H0.
Qed.

Lemma singleton_inv: forall x x', Singleton X x = Singleton X x' <-> x = x'.
Proof.
  split; intro.
  - assert (Same_set _ (Singleton _ x) (Singleton _ x')). {
      split; intros ? ?.
      + inv H0.
        now rewrite <- H.
      + now rewrite H, H0.
    }
    inv H0.
    assert (In _ (Singleton _ x') x). {
      now apply (H1 x).
    }
    now inv H3.
  - now rewrite H.
Qed.

End EnsembleHelpers.

#[export] Hint Rewrite (@intersect_comm Valuation) (@intersect_full Valuation) : denotB.

From Coq Require Import
  Relations
  Classes.RelationClasses
  Relations.Operators_Properties.
Section RelationHelpers.
  Variable A: Type.
  Variable R: relation A.

  Lemma clos_rtn1_rt1n: forall x y,
      clos_refl_trans_n1 _ R x y -> clos_refl_trans_1n _ R x y.
  Proof. intros. apply clos_rt_rt1n. apply clos_rtn1_rt. apply H. Qed.

  Lemma clos_rt1n_rtn1: forall x y,
      clos_refl_trans_1n _ R x y -> clos_refl_trans_n1 _ R x y.
  Proof. intros. apply clos_rt_rtn1. apply clos_rt1n_rt. apply H. Qed.

  Lemma clos_rt1n_rtn1_iff: forall x y,
      clos_refl_trans_1n _ R x y <-> clos_refl_trans_n1 _ R x y.
  Proof. split; [apply clos_rt1n_rtn1 | apply clos_rtn1_rt1n]. Qed.

  Global Instance clos_rtn1_trans: Transitive (clos_refl_trans_n1 _ R).
  Proof.
    intros x y z H0 H1.
    apply clos_rtn1_rt in H0, H1.
    apply clos_rt_rtn1.
    apply rt_trans with (y := y); assumption.
  Qed.

  Global Instance clos_rtn1_refl: Reflexive (clos_refl_trans_n1 _ R).
  Proof.
    intro. constructor.
  Qed.
End RelationHelpers.

From Coq Require Import
  Init.Datatypes
  Lists.List.

Section ListHelpers.
  Import ListNotations.
  Open Scope list_scope.
  Variable A : Type.

  Lemma app_tail_inj: forall (t1 t2 t2': list A),
      t1 ++ t2 = t1 ++ t2' -> t2 = t2'.
  Proof.
    induction t1; intros.
    - apply H.
    - simpl in H. inversion H.
      apply IHt1; assumption.
  Qed.

  Lemma app_nil_unique_r: forall (t1 t2: list A),
      t1 = t1 ++ t2 -> t2 = [].
  Proof.
    induction t1; intros.
    - rewrite H. auto.
    - inversion H. apply IHt1; assumption.
  Qed.

  Lemma app_nil_unique_l: forall (t1 t2: list A),
      t1 = t2 ++ t1 -> t2 = [].
  Proof.
    induction t1; intros.
    - rewrite app_nil_r in H. auto.
    - destruct t2; auto.
      inversion H; subst. replace (t2 ++ a0 :: t1) with ((t2 ++ [a0]) ++ t1) in H2.
      + apply IHt1 in H2. destruct (app_eq_nil _ _ H2); subst; assumption.
      + rewrite <- app_assoc. auto.
  Qed.
End ListHelpers.

Definition option_bind {X Y: Type} (m : option X) (f: X -> option Y): option Y :=
  match m with None => None | Some x => f x end.

Definition option_compose {X Y Z: Type} (f: X -> option Y) (g: Y -> option Z): X -> option Z :=
  fun x => option_bind (f x) g.

Definition option_lift {X Y: Type} (f: X -> Y): X -> option Y := fun x => Some (f x).

(* Lemma option_bind_mono: forall (X Y: Type) (x x': option X) (f f': X -> option Y), *)
(*     x <<= x' -> (forall x, f x <<= f' x) -> option_bind x f <<= option_bind x' f'. *)
(* Proof. intros. destruct H; cbn; auto with lessdef. Qed. *)

Lemma option_inversion {X Y: Type} {x: option X} {f: X -> option Y} {y: Y}:
  option_bind x f = Some y ->
  exists x', x = Some x' /\ f x' = Some y.
Proof.
  destruct x; simpl; intros.
  - exists x. split; auto.
  - inversion H.
Qed.
Lemma some_not_none {X:Type}: forall (x:X), Some x <> None.
Proof. easy. Qed.

Lemma option_inversion_none {X Y: Type}: forall (x: option X) (f: X -> option Y),
    option_bind x f = None ->
    x = None \/ exists y, x = Some y /\ f y = None.
Proof.
  intros.
  destruct x.
  - cbn in H.
    right.
    exists x.
    split; auto.
  - now left.
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
    - rewrite (IHn f x (n_fold n f x) y); auto.
Qed.

Fixpoint n_fold_set {X: Type} (n: nat) (f: X -> Ensemble X): X -> Ensemble X :=
  match n with
  | 0 => Singleton _
  | S n => set_compose f (n_fold_set n f)
  end.
