From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

Definition Has {T} (s:T->Prop) (x:T) := s x. 
Notation "s \has x" := (Has s x) (at level 60).
Definition Includes {T} (s:T->Prop) (t:T->Prop) := forall x:T, t x -> s x.
Notation "s =) t" := (Includes s t) (at level 20).
Notation "s (= t" := (Includes t s) (at level 20).
Definition Complement {T} (s:T->Prop) := fun x:T => ~ s x.
Notation "s ^c" := (Complement s) (at level 0).

Inductive Empty {T} : T -> Prop :=.

Inductive Total {T} : T -> Prop :=
  Total_intro: forall x:T, Total \has x.

Inductive Singleton {T} (x: T) : T -> Prop :=
  Singleton_intro : Singleton x \has x.

Inductive Intersection {T} (A: T->Prop) (B: T->Prop) : T -> Prop :=
  Intersection_intro : forall x: T, A \has x -> B \has x -> (Intersection A B) \has x.
Notation "a |-| b" := (Intersection a b) (at level 10).

Inductive Union {T} (A: T->Prop) (B: T->Prop) : T->Prop :=
  | Union_introl : forall x: T, A \has x -> (Union A B) \has x
  | Union_intror : forall x: T, B \has x -> (Union A B) \has x.
Notation "a |_| b" := (Union a b) (at level 20).


Definition Equiv {T} (A: T->Prop) (B: T->Prop) : Prop :=
  A =) B /\ B =) A.
Notation "a (=) b" := (Equiv a b) (at level 20).


Theorem intersection_left_includes {T} (A B: T->Prop) : A =) (Intersection A B).
Proof.
  move=> x AB_has_x.
  by case: AB_has_x => A_has_x B_has_x.
Qed.

Theorem intersection_right_includes {T} (A B: T->Prop) : B =) (Intersection A B).
Proof.
  move=> x AB_has_x.
  by case: AB_has_x => A_has_x B_has_x.
Qed.

Theorem total_includes {T} (A: T->Prop) : Total =) A.
Proof.
  move=> x A_has_x.
  by apply: Total_intro.
Qed.

Section Pretopologies.
Variable X: Type.
Arguments X : default implicits.
Definition SX := X -> Prop.
Definition SSX := SX -> Prop.

Class Filter (f: SSX) := {
  filter_has_some : exists a, f \has a;
  filter_superset_law : forall a b : SX, a =) b -> f \has b -> f \has a;
  filter_intersection_law : forall a b : SX, f \has a -> f \has b -> f \has a |-| b;
}.

Theorem filter_has_total (f: SSX) : Filter f -> f \has Total.
Proof.
  move => filter.
  case: filter => has_some superset intersection.
  case: has_some => c f_has_c.
  apply: (superset Total c).
  - by apply: total_includes.
  - by apply: f_has_c.
Qed.

Class Neighborhood v := {
  neighborhood_filter :> forall x: X, Filter (v x);
  neighborhood_has_point : forall (x: X) (s: SX), v x \has s -> s \has x; 
}.

Class Interior (i: SX->SX) := {
  interior_preserve_total : Total (=) i Total;
  interior_intensive_law : forall (s: SX), s =) i s;
  interior_intersection_law: forall s t: SX, i (s |-| t) (=) (i s) |-| (i t); 
}.

Definition n2i (v: X -> SSX) := fun s:SX => fun x:X => v x \has s.
Definition i2n i := fun x:X => fun s:SX => i s \has x.

Theorem neighborhood_derives_interior (v: X->SSX): Neighborhood v -> Interior (n2i v).
Proof.
move => neighborhood_v.
case: neighborhood_v => filters has_point.
apply: Build_Interior.
- apply: conj.
  + by apply: total_includes.
  + move => x total_has_x.
    by apply: (filter_has_total (f:=(v x)) (filters x)).
- move => s x interior_has_s.
  case: (filters x) => has_some superset intersection .
  apply: has_point.
  by apply: interior_has_s.
- move => s t.
  constructor.
  + move => x ab_has_x.
    case: (filters x) => has_some superset intersection.
    apply: intersection.
    * by case: ab_has_x => y a b.
    * by case: ab_has_x => y a b.
  + move => x ab_has_x.
    constructor.
    * case: (filters x) => exist superset intersecion.
      apply: (superset s (s |-| t)).
      - by apply: intersection_left_includes.
      - by [].
    * case: (filters x) => exist superset intersecion.
      apply: (superset t (s |-| t)).
      - by apply: intersection_right_includes.
      - by [].
Qed.



