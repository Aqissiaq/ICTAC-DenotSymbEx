From Coq Require Import
                 Init.Datatypes
                 Psatz
                 ZArith.

(* We need Constructive Definite Description – a relatively weak omniscience principle *)
(*https://coq.inria.fr/stdlib/Coq.Logic.Description.html*)
(*https://www.cs.princeton.edu/courses/archive/fall07/cos595/stdlib/html/Coq.Logic.ChoiceFacts.html*)
From Coq Require Import Classical Description.

(* Trick from Leroy *)
(*https://xavierleroy.org/cdf-mech-sem/CDF.Divergence.html*)
Inductive lessdef {A: Type}: option A -> option A -> Prop :=
| lessdef_none: forall oa, lessdef None oa
| lessdef_some: forall a, lessdef (Some a) (Some a).

Notation "x <<= y" := (lessdef x y) (at level 70, no associativity).

#[export]
Hint Constructors lessdef : lessdef.

Lemma lessdef_refl {X:Type}: forall (x:option X), x <<= x.
Proof. destruct x; constructor. Qed.

Definition option_bind {X Y: Type} (m : option X) (f: X -> option Y): option Y :=
  match m with None => None | Some x => f x end.

Definition option_compose {X Y Z: Type} (f: X -> option Y) (g: Y -> option Z): X -> option Z :=
  fun x => option_bind (f x) g.

Definition option_lift {X Y: Type} (f: X -> Y): X -> option Y := fun x => Some (f x).

Lemma option_bind_mono: forall (X Y: Type) (x x': option X) (f f': X -> option Y),
    x <<= x' -> (forall x, f x <<= f' x) -> option_bind x f <<= option_bind x' f'.
Proof. intros. destruct H; cbn; auto with lessdef. Qed.

Lemma option_inversion {X Y: Type} {x: option X} {f: X -> option Y} {y: Y}:
  option_bind x f = Some y ->
  exists x', x = Some x' /\ f x' = Some y.
Proof.
  destruct x; simpl; intros.
  - exists x. split; auto.
  - inversion H.
Qed.

Section LIMIT.

  Context {A: Type} (f: nat -> option A).

  Hypothesis f_mono: forall i j, i <= j -> f i <<= f j.

  Lemma limit_exists:
    { lim : option A | exists i, forall j, i <= j -> f j = lim }.
  Proof.
      apply constructive_definite_description.
      destruct (classic (forall i, f i = None)) as [DIV|TERM].
      - exists None; split.
        + exists O; auto.
        + intros lim (i & LIM). rewrite <- (DIV i). apply LIM; lia.
      - apply not_all_ex_not in TERM. destruct TERM as (i & TERM).
        exists (f i); split.
        + exists i; intros. destruct (f_mono i j H). congruence. auto.
        + intros lim (i2 & LIM2). set (j := Nat.max i i2).
          rewrite <- (LIM2 j) by lia.
          destruct (f_mono i j). lia. congruence. auto.
  Qed.

  Definition limit : option A := proj1_sig limit_exists.

  Lemma limit_charact: exists i, forall j, i <= j -> f j = limit.
  Proof. unfold limit. apply proj2_sig. Qed.

End LIMIT.
