From Coq Require Import Strings.String.
From BigStepSymbEx Require Import Expr.

Module Trace.
  Inductive Trc : Type :=
  | TSkip
  | TAsgn (x:string) (e:Aexpr)
  | TAsrt (b:Bexpr)
  | TSeq (t1 t2: Trc).
End Trace.

Module TraceNotations.
  Import Trace.

  Notation "'skip'" := TSkip (in custom com at level 80) : com_scope.
  Notation "x := y"  :=
    (TAsgn x y)
      (in custom com at level 0, x constr at level 0,
          y at level 85, no associativity) : com_scope.
  Notation "b ?" :=
    (TAsrt b)
      (in custom com at level 90, right associativity) : com_scope.
  Notation "x ; y" :=
    (TSeq x y)
      (in custom com at level 90, right associativity) : com_scope.
End TraceNotations.

Module NonDet.
  Inductive Prg : Type :=
  | PSkip
  | PAsgn (x:string) (e:Aexpr)
  | PAsrt (b:Bexpr)
  | PSeq (p1 p2: Prg)
  | PChoice (p1 p2: Prg)
  | PStar (p: Prg)
  .

  Axiom Prg_assoc: forall p q r, PSeq p (PSeq q r) = PSeq (PSeq p q) r.
End NonDet.

Module NonDetNotations.
  Import NonDet.

  Notation "'skip'" := PSkip (in custom com at level 80) : com_scope.
  Notation "x := y"  :=
    (PAsgn x y)
      (in custom com at level 0, x constr at level 0,
          y at level 85, no associativity) : com_scope.
  Notation "b ?" :=
    (PAsrt b)
      (in custom com at level 90, right associativity) : com_scope.
  Notation "x ; y" :=
    (PSeq x y)
      (in custom com at level 90, right associativity) : com_scope.
  Notation "x (+) y" :=
    (PChoice x y)
      (in custom com at level 90, right associativity) : com_scope.
  Notation "x *" :=
    (PStar x)
      (in custom com at level 90, right associativity) : com_scope.
  Open Scope com_scope.
End NonDetNotations.

Section While.
Import NonDet NonDetNotations.

Inductive Stmt: Type :=
| Skip
| Asgn (x:string) (e:Aexpr)
| Seq (s1 s2: Stmt)
| If (b:Bexpr) (s1 s2: Stmt)
| While (b:Bexpr) (s: Stmt).

Fixpoint encode (s:Stmt): Prg :=
  match s with
  | Skip => PSkip
  | Asgn x e => PAsgn x e
  | Seq s1 s2 => PSeq (encode s1) (encode s2)
  | If b s1 s2 => PChoice (PSeq <{b?}> (encode s1)) (PSeq <{~b?}> (encode s2))
  | While b s => PSeq (PStar (PSeq <{b?}> (encode s))) <{~b?}>
  end.
End While.

Module WhileNotations.

  Notation "'skip'" := Skip (in custom com at level 80) : com_scope.
  Notation "x := y"  :=
    (Asgn x y)
      (in custom com at level 0, x constr at level 0,
          y at level 85, no associativity) : com_scope.
  Notation "x ; y" :=
    (Seq x y)
      (in custom com at level 90, right associativity) : com_scope.
  Notation "'if' x '{' y '}' '{' z '}'" :=
    (If x y z)
      (in custom com at level 89, x at level 99,
          y at level 99, z at level 99) : com_scope.
  Notation "'while' x '{' y '}'" :=
    (While x y)
      (in custom com at level 89, x at level 99,
          y at level 99) : com_scope.
End WhileNotations.
