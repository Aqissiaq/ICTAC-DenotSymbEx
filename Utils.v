From Coq Require Import
  Psatz
  Arith
  Ensembles.

From BigStepSymbEx Require Import
  Maps.

Ltac inv H := inversion H; subst.
Ltac splits := repeat split.

Lemma nat_eq_dec: forall (n m: nat), n = m \/ n <> m.
Proof.
  induction n; destruct m.
  - now left.
  - now right.
  - now right.
  - destruct (IHn m); subst.
    + now left.
    + right.
      intros contra.
      now inv contra.
Qed.

Definition sub_singleton {X:Type}: Ensemble X -> Prop :=
  fun A => A = Empty_set _ \/ exists x, A = Singleton _ x.

Lemma sub_singleton_empty {X:Type}: sub_singleton (Empty_set X).
Proof.
  now left.
Qed.

Lemma sub_singleton_singleton{X:Type}: forall x, sub_singleton (Singleton X x).
Proof.
  right.
  now exists x.
Qed.

Lemma singleton_not_empty{X:Type}: forall x, Empty_set _ <> Singleton X x.
Proof.
  intros x ?.
  assert (In _ (Singleton _ x) x) by easy.
  rewrite <- H in H0.
  inv H0.
Qed.

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

  Lemma union_fam_singleton{I:Type} (I_eq_dec: forall (i0 i1: I), i0 = i1 \/ i0 <> i1) :
    forall (F: I -> Ensemble X) x,
      (exists i, F i = Singleton _ x /\ forall j, j <> i -> F j = Empty_set _) ->
      Union_Fam F = Singleton _ x.
  Proof.
    intros F x (?i & ? & ?).
    apply Extensionality_Ensembles.
    split; intros ?y ?.
    - inv H1.
      destruct (I_eq_dec i i0) as [-> | ?].
      + rewrite H in H2.
        now inv H2.
      + rewrite H0 in H2; auto.
        inv H2.
    - exists i.
      inv H1.
      now rewrite H.
  Qed.

  Lemma union_fam_empty {I:Type}: forall (F: I -> Ensemble X),
      (forall i, F i = Empty_set _) -> Union_Fam F = Empty_set _.
  Proof.
    intros.
    apply Extensionality_Ensembles.
    split; intros ?y ?.
    - inv H0.
      rewrite (H i) in H1.
      inv H1.
    - inv H0.
  Qed.

  Lemma union_fam_sub_singleton{I:Type}(I_eq_dec: forall (i0 i1: I), i0 = i1 \/ i0 <> i1):
    forall (F: I -> Ensemble X),
      (exists x i, F i = Singleton _ x /\ forall j, j <> i -> F j = Empty_set _)
      \/ (forall i, F i = Empty_set _) ->
      sub_singleton (Union_Fam F).
  Proof.
    intros F [(?x & ?i & ? & ?) | ?].
    - right.
      exists x.
      apply union_fam_singleton; auto.
      exists i.
      split; auto.
    - left.
      now apply union_fam_empty.
  Qed.

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

  Lemma set_compose_empty: forall (f:X -> Ensemble Y) (g:Y -> Ensemble Z) (x:X),
      f x = Empty_set _ ->
      set_compose f g x = Empty_set _.
  Proof.
    intros.
    unfold set_compose.
    apply Extensionality_Ensembles.
    split; intros ? ?.
    - destruct H0 as (? & ? & ?).
      rewrite H in H0.
      exfalso. inv H0.
    - exfalso. inv H0.
  Qed.

  Lemma set_compose_inv: forall (f:X -> Ensemble Y) (g:Y -> Ensemble Z) x z,
      set_compose f g x = Singleton _ z ->
      forall y, In _ (f x) y -> Included _ (g y)  (Singleton _ z).
  Proof.
    intros.
    intros ?z ?.
    rewrite <- H.
    exists y.
    split; auto.
  Qed.

  Lemma set_compose_inv': forall (f:X -> Ensemble Y) (g:Y -> Ensemble Z) x z,
      set_compose f g x = Singleton _ z ->
      exists y, In _ (f x) y /\ Included _ (g y) (Singleton _ z).
  Proof.
    intros.
    assert (In _ (set_compose f g x) z) by (rewrite H; easy).
    destruct H0 as (?y & ? & ?).
    exists y.
    split; auto.
    eapply set_compose_inv; eauto.
  Qed.

  Lemma set_compose_singleton_first: forall (f:X -> Ensemble Y) (g:Y -> Ensemble Z) x y,
      f x = Singleton _ y ->
      set_compose f g x = g y.
  Proof.
    intros.
    unfold set_compose.
    apply Extensionality_Ensembles.
    split; intros ? ?.
    - destruct H0 as (? & ? & ?).
      rewrite H in H0.
      now inv H0.
    - exists y.
      split; auto.
      rewrite H; constructor.
  Qed.

  Lemma union_unit_r: forall A,
      Union X A (Empty_set _) = A.
  Proof.
    intros.
    apply Extensionality_Ensembles.
    split; intros ? ?.
    - destruct H; auto.
      inv H.
    - now left.
  Qed.

  Lemma union_unit_l: forall A,
      Union X (Empty_set _) A = A.
  Proof.
    intros.
    apply Extensionality_Ensembles.
    split; intros ? ?.
    - destruct H; auto.
      inv H.
    - now right.
  Qed.

  Lemma sub_singleton_set_compose_first: forall (f: X -> Ensemble Y) (g: Y -> Ensemble Z) x,
      sub_singleton (f x) ->
      (forall y, sub_singleton (g y)) ->
      sub_singleton (set_compose f g x).
  Proof.
    intros.
    destruct H as [? | (?V & ?)].
    - rewrite set_compose_empty; auto.
      apply sub_singleton_empty.
    - erewrite set_compose_singleton_first; eauto.
  Qed.

  Lemma sub_singleton_set_compose_snd: forall (f: X -> Ensemble Y) (g: Y -> Ensemble Z) x y,
      f x = Singleton _ y ->
      sub_singleton (g y) ->
      sub_singleton (set_compose f g x).
  Proof.
    intros.
    erewrite set_compose_singleton_first; eauto.
  Qed.

  Lemma sub_singleton_if: forall (b:bool) (x:X),
      sub_singleton (if b then Singleton _ x else Empty_set _).
  Proof.
    intros.
    destruct b.
    - apply sub_singleton_singleton.
    - apply sub_singleton_empty.
  Qed.

  Lemma sub_singleton_if': forall (b:bool) (x:X),
      sub_singleton (if b then Empty_set _ else Singleton _ x).
  Proof.
    intros.
    destruct b.
    - apply sub_singleton_empty.
    - apply sub_singleton_singleton.
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

  Lemma head_app : forall (xs:list A) (x: A),
      xs <> [] ->
      forall d,
        hd d (xs ++ [x]) = hd d xs.
  Proof.
    induction xs; auto.
    intros.
    exfalso.
    now apply H.
  Qed.

  Lemma last_cons : forall (xs:list A) (x: A),
      xs <> [] ->
      forall d,
        last (x::xs) d = last xs d.
  Proof.
    destruct xs; intros.
    - exfalso.
      now apply H.
    - pose proof exists_last H as (?l & ?x & ->).
      replace (x :: l ++ [x0]) with ((x :: l) ++ [x0]) by auto.
      now rewrite 2 last_last.
  Qed.

  Lemma last_non_empty : forall (xs:list A),
      xs <> [] ->
      forall d d',
        last xs d = last xs d'.
  Proof.
    intros.
    pose proof exists_last H as (?l & ? & ->).
    now rewrite 2 last_last.
  Qed.

  Lemma head_non_empty : forall (xs:list A),
      xs <> [] ->
      forall d d',
        hd d xs = hd d' xs.
  Proof.
    destruct xs; auto.
    intros.
    exfalso.
    now apply H.
  Qed.

  Lemma nth_cons : forall (xs:list A) j x,
      xs <> [] ->
      forall d,
        nth j xs d = nth (S j) (x::xs) d.
  Proof.
    induction xs; intros.
    - exfalso.
      now apply H.
    - destruct j; auto.
  Qed.

  Lemma nth_last : forall (xs: list A),
    forall d,
      last xs d = nth (pred (length xs)) xs d.
  Proof.
    induction xs; intros; auto.
    destruct xs; auto.
    replace (length (a :: a0 :: xs)) with (S (S (length xs))); auto.
    rewrite Nat.pred_succ.
    rewrite <- nth_cons.
    rewrite last_cons.
    apply IHxs.
    all: easy.
  Qed.

  Lemma nth_length_cons: forall (xs: list A) x,
      xs <> [] ->
      forall d,
        (nth (length xs) (x :: xs) d) = last xs d.
  Proof.
    induction xs using rev_ind; intros.
    - exfalso.
      now apply H.
    - rewrite app_length, last_last.
      replace (length xs + length [x]) with (S (length xs)).
      rewrite <- nth_cons, app_nth2.
      now replace (length xs - length xs) with 0 by lia.
      all: auto; cbn; lia.
  Qed.

  Lemma nth_length_app: forall (xs: list A) x,
      xs <> [] ->
      forall d,
        (nth (length xs) (xs ++ [x]) d) = x.
  Proof.
    induction xs; intros.
    - exfalso.
      now apply H.
    - cbn.
      rewrite app_nth2; auto.
      now replace (length xs - length xs) with 0 by lia.
  Qed.

  Lemma length_one_iff_singl (l : list A):
    length l = 1 <-> (exists a, l = [a]).
  Proof.
    split.
    - destruct l; intros; inv H.
      apply length_zero_iff_nil in H1.
      exists a.
      now rewrite H1.
    - now intros (?a & ->).
  Qed.

  (* getting silly now *)
  Lemma length_two_iff (l : list A):
    length l = 2 <-> (exists a1 a2, l = [a1 ; a2]).
  Proof.
    split.
    - destruct l; intros; inv H.
      apply length_one_iff_singl in H1.
      destruct H1 as (?a & ->).
      now exists a, a0.
    - now intros (?a & ?a & ->).
  Qed.

  Lemma length_SSm_iff (l : list A) m:
    length l = S (S m) <-> (exists a1 a2 l', l = [a1] ++ l' ++ [a2] /\ length l' = m).
  Proof.
    split.
    - generalize dependent l.
      induction m; intros.
      + apply length_two_iff in H.
        destruct H as (?a & ?a & ->).
        exists a, a0, [].
        easy.
      + destruct l; inv H.
        pose proof IHm l H1 as (?a & ?a & ?l & -> & ?).
        exists a, a1, (a0 ::l0).
        split; auto.
        cbn.
        now rewrite H0.
    - intros (a1 & a2 & l' & -> & ?).
      rewrite 2 app_length.
      cbn.
      rewrite H.
      lia.
  Qed.

End ListHelpers.

Definition option_bind {X Y: Type} (m : option X) (f: X -> option Y): option Y :=
  match m with None => None | Some x => f x end.

Definition option_compose {X Y Z: Type} (f: X -> option Y) (g: Y -> option Z): X -> option Z :=
  fun x => option_bind (f x) g.

Definition option_lift {X Y: Type} (f: X -> Y): X -> option Y := fun x => Some (f x).

Lemma option_inversion {X Y: Type} {x: option X} {f: X -> option Y} {y: Y}:
  option_bind x f = Some y ->
  exists x', x = Some x' /\ f x' = Some y.
Proof.
  destruct x; simpl; intros.
  - exists x. split; auto.
  - inversion H.
Qed.

Lemma option_inversion' {X Y: Type} {x: option X} {f: X -> option Y} {y: Y}:
  ( exists x', x = Some x' /\ f x' = Some y) ->
  option_bind x f = Some y.
Proof.
  intros (?x & ? & ?).
  rewrite H; now cbn.
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

Lemma sub_singleton_n_fold_set{X:Type}: forall n f (x:X),
    (forall x, sub_singleton (f x)) ->
    sub_singleton (n_fold_set n f x).
Proof.
  induction n; intros.
  - apply sub_singleton_singleton.
  - cbn.
    apply sub_singleton_set_compose_first; auto.
Qed.
