From mathcomp Require Import all_ssreflect.
Require Import Ensembles.
Require Import Relations.
Require Import Equivalence.
Require Import Tactics.

Set Implicit Arguments.
Unset Strict Implicit.

Section Pretopology.

Arguments In {U}.
Arguments Included {U}.
Arguments Singleton {U}.
Arguments Union {U}.
Arguments Add {U}.
Arguments Intersection {U}.
Arguments Couple {U}.
Arguments Triple {U}.
Arguments Complement {U}.
Arguments Setminus {U}.
Arguments Subtract {U}.
Arguments Disjoint {U}.
Arguments Inhabited {U}.
Arguments Strict_Included {U}.
Arguments Same_set {U}.
Arguments Extensionality_Ensembles {U}.
Arguments Empty_set {U}.
Arguments Full_set {U}.

Notation "A >= B" := (Included B A).
Notation "A <= B" := (Included A B).
Notation "A == B" := (Same_set A B).
Notation "A && B" := (Intersection A B).
Notation "A || B" := (Union A B).
Notation "~~ A" := (Complement A).
Notation "x /in A" := (In A x) (at level 50).
Let total {U: Type} := Full_set (U:=U).
Let empty {U: Type} := Empty_set (U:=U).
Let P := Ensemble.

Definition nonempty {X} (A: P X) := exists x, x /in A.
Definition fixpoint {X} (x: X) (f: X -> X) := x = f x. 
Definition upward {X} {R: relation X} (p: P X) (x y: X) := R x y -> p x -> p y. (* where R is preorder *)
Definition monotone {X} {R: relation X} (f: X -> X) (x y: X) := R x y -> R (f x) (f y). (* where R is preorder *)
Definition proper {X} (F: P (P X)) := ~ In F empty.
Definition idempotent {X} (p: X -> X) (x: X) := p (p x) = p (x).

Variable X: Type.
Arguments X: default implicits.

Definition isotonic (op: P X -> P X) := forall A B: P X, A <= B -> op A <= op B.
Definition expansive (cl: P X -> P X) := forall A: P X, A <= cl A.
Definition intensive (int: P X -> P X) := forall A: P X, int A <= A.
Definition subadditive (cl: P X -> P X) := forall A B: P X, cl (A || B) <= (cl A) || (cl B).
Definition supermulticative (int: P X -> P X) := forall A B: P X, (int A) && (int B) <= int (A && B).
