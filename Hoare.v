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
(*|
Intuition: a quadruple {P} [σ] s {Q} holds if
V is a state that satisfies P, we start s in σ(V) and if it terminates, the result satisfies Q

|*)

(* Overloading here to exploit Coq's logic *)
Notation Assertion := (Ensemble Valuation).
(* Notation "{{ P }} [ σ ] s {{ Q }}" := (valid_hoare_quadruple P σ s Q) *)
(*                                         (at level 90, s custom com at level 99). *)

Definition valid (P: Assertion) (σ: sub) (s: Stmt) (Q: Assertion) : Prop :=
  forall V V',
    P V ->
    denot_fun s (denot_sub σ V) = Some V' ->
    Q V'.

Variant Image {X Y:Type} (f: X -> Y) (A: Ensemble X): Ensemble Y :=
  | Image_intro: forall x, A x -> Image _ _ (f x).

(* Based on KeY book (fig. 17.2)*)
Inductive derivable: Assertion -> sub -> Stmt -> Assertion -> Prop :=
| H_exit: forall P σ Q,
    Included _ (Image (denot_sub σ) P) Q ->
    derivable P σ <{skip}> Q
| H_skip: forall P σ s Q,
    derivable P σ s Q ->
    derivable P σ <{skip ; s}> Q
| H_skip': forall P σ s Q,
    derivable P σ s Q ->
    derivable P σ <{s ; skip}> Q
| H_asgn: forall P σ x e s Q,
    derivable P (x !-> Aapply σ e ; σ) s Q ->
    derivable P σ <{x:=e; s}> Q
| H_cond: forall P σ b s1 s2 s Q,
    derivable (Intersection _ P (denot__B b)) σ <{s1 ; s}> Q ->
    derivable (Intersection _ P (Complement _ (denot__B b))) σ <{s2 ; s}> Q ->
    derivable P σ <{if b {s1} {s2} ; s}> Q
| H_loop: forall P I σ b s1 s Q,
    Included _ P (Image (denot_sub σ) I) ->
    derivable (Intersection _ I (denot__B b)) id_sub s1 I ->
    derivable (Intersection _ I (Complement _ (denot__B b))) id_sub s Q ->
    derivable P σ <{while b {s1} ; s}> Q.

Example branch_example: Stmt := <{
    if X <= 10
           {if Y <= 5 {X := 42} {X := 0} ; skip}
           {if 4 <= Y {X := 42} {X := 1} ; skip}
    ; skip
    }>.

Fact branch_example_valid: valid (fun V => V X <= 10 /\ V Y <= 5) id_sub branch_example (fun V => V X = 42).
Proof.
  intros V V' (?&?) ?.
  apply PeanoNat.Nat.leb_le in H, H0.
  simpl in H1.
  rewrite denot_id_sub, H, H0 in *.
  now inversion H1; subst.
Qed.

Fact branch_example_derivable: derivable (fun V => V X <= 10 /\ V Y <= 5) id_sub branch_example (fun V => V X = 42).
Proof.
  repeat (econstructor; econstructor); econstructor.
  - intros A ?.
    destruct H as (?V &?).
    easy.
  - intros A ?.
    destruct H as (?V &?).
    destruct H as (?V, ?, ?).
    destruct H as (?V, ?, ?).
    destruct H.
    exfalso.
    apply H0.
    now apply PeanoNat.Nat.leb_le.
  - intros A ?.
    destruct H as (?V &?).
    easy.
  - intros A ?.
    destruct H as (?V &?).
    destruct H as (?V, ?, ?).
    destruct H as (?V, ?, ?).
    destruct H.
    exfalso.
    apply H1.
    now apply PeanoNat.Nat.leb_le.
Qed.
