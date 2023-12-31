From Coq Require Import Strings.String.
From BigStepSymbEx Require Import Expr.

Module While.
  Inductive Stmt : Type :=
  | SSkip
  | SAsgn (x:string) (e:Aexpr)
  | SSeq (s1 s2:Stmt)
  | SIf (b:Bexpr) (s1 s2:Stmt)
  | SWhile (b:Bexpr) (s:Stmt).

  Notation "'skip'" := SSkip (in custom com at level 80) : com_scope.
  Notation "x := y"  :=
          (SAsgn x y)
              (in custom com at level 0, x constr at level 0,
              y at level 85, no associativity) : com_scope.
  Notation "x ; y" :=
          (SSeq x y)
            (in custom com at level 90, right associativity) : com_scope.
  Notation "'if' x '{' y '}' '{' z '}'" :=
          (SIf x y z)
            (in custom com at level 89, x at level 99,
              y at level 99, z at level 99) : com_scope.
  Notation "'while' x '{' y '}'" :=
          (SWhile x y)
            (in custom com at level 89, x at level 99,
              y at level 99) : com_scope.

  Open Scope com_scope.

  Lemma seq_discriminate1: forall p q, p <> <{p ; q}>.
  Proof. intros p q contra. induction p;
           try discriminate.
         inversion contra; subst. apply IHp1; assumption.
  Qed.

  Lemma seq_discriminate2: forall p q, q <> <{p ; q}>.
  Proof. intros p q contra. induction q;
           try discriminate.
         inversion contra; subst. apply IHq2; assumption.
  Qed.

  Definition X: string := "x".
  Definition Y: string := "y".
  Definition Z: string := "z".

End While.
