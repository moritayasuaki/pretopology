From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

Section Subsets.

Variable X: Type.
Arguments X : default implicits.

Let SX := X -> Prop.

Definition Has {X} (s: X->Prop) (x:X) := s x.
Notation "s `has` x" := (Has s x) (at level 50).

Definition Includes (s:SX) (t:SX) := forall x:X, t x -> s x.
Notation "s `includes` t" := (Includes s t) (at level 50).

Definition Complement (s:SX) := fun x:X => ~ s x.
Notation "s ^c" := (Complement s) (at level 10).

Inductive Empty : SX :=.

Inductive Total : SX :=
  Total_intro: forall x:X, Total  x.

Inductive Singleton (x: X) : SX :=
  Singleton_intro : Singleton x `has` x.

Inductive Intersection (A B: SX) : SX :=
  Intersection_intro : forall x: X, A `has` x -> B `has` x -> Intersection A  B `has` x.
Notation "a `and` b" := (Intersection a b) (at level 0).

Inductive Union (A B: SX) : SX :=
  | Union_introl : forall x: X, A `has` x -> Union A B `has` x
  | Union_intror : forall x: X, B `has` x -> Union A B `has` x.
Notation "a `or` b" := (Union a b) (at level 20).


Definition Equiv (A: SX) (B: SX) : Prop :=
  A `includes` B /\ B `includes` A.
Notation "a `equiv` b" := (Equiv a b) (at level 20).


Theorem intersection_left_includes (A B: SX) : A `includes` (A `and` B).
Proof.
  move=> x AB_has_x.
  by case: AB_has_x => A_has_x B_has_x.
Qed.

Theorem intersection_right_includes (A B: SX) : B `includes` (A `and` B).
Proof.
  move=> x AB_has_x.
  by case: AB_has_x => A_has_x B_has_x.
Qed.

Theorem includsion_intersection (A B: SX) : A `includes` B -> (A `and` B) `equiv` B.
Proof.
  move => a_includes_b.
  constructor.
  - move => x ab_has_x.
    constructor.
    + by apply: a_includes_b.
    + by apply: ab_has_x.
  - by apply: intersection_right_includes.
Qed.

Theorem total_includes (A: SX) : Total `includes` A.
Proof.
  move=> x A_has_x.
  by apply: Total_intro.
Qed.
End Subsets.

Notation "s `has` x" := (Has s x) (at level 50).
Notation "s `includes` t" := (Includes s t) (at level 50).
Notation "a `and` b" := (Intersection a b) (at level 0).
Notation "a `or` b" := (Union a b) (at level 20).
Notation "a `equiv` b" := (Equiv a b) (at level 20).


Section Pretopologies.
Variable X : Type.
Let SX := (X -> Prop).
Let SSX := (X -> Prop) -> Prop.
Let TX := Total (X:=X).

Class Filter (f: SSX) := {
  filter_has_some : exists s : SX, f `has` s;
  filter_superset_law : forall s t : SX, s `includes` t -> f `has` t -> f `has` s;
  filter_intersection_law : forall s t : SX, f `has` s -> f `has` t -> f `has` s `and` t;
}.

Theorem filter_has_total (f: SSX) : Filter f -> f `has` TX.
Proof.
  move => filter.
  case: filter => has_some superset intersection.
  case: has_some => c f_has_c.
  apply: (superset TX c).
  - by apply: total_includes.
  - by apply: f_has_c.
Qed.

Class Neighborhood v := {
  neighborhood_filter :> forall x: X, Filter (v x);
  neighborhood_has_point : forall (x: X) (s: SX), v x `has` s -> s `has` x; 
}.

Class Interior (i: SX->SX) := {
  interior_preserve_total : TX `equiv` i TX;
  interior_intensive_law : forall (s: SX), s `includes` i s;
  interior_intersection_law: forall s t: SX, i (s `and` t) `equiv` (i s) `and` (i t); 
}.

(*
Theorem p (i: SX->SX) (s t: SX): Interior i -> s `includes` t -> 
*)
Definition n2i (v: X -> SSX) := fun s:SX => fun x:X => (v x) `has` s.
Definition i2n i := fun x:X => fun s:SX => (i s) `has` x.

Theorem neighborhood_derives_interior (v: X->SSX): Neighborhood v -> Interior (n2i v).
Proof.
move => neighborhood.
case: neighborhood => filters has_point.
constructor.
- constructor.
  + by apply: total_includes.
  + move => x total_has_x.
    by apply: (filter_has_total (f:=(v x)) (filters x)).
- move => s x interior_has_s.
  case: (filters x) => has_some superset intersection .
  apply: has_point.
  by apply: interior_has_s.
- move => s t.
  constructor.
  + move => x si_and_ti_has_x.
    case: (filters x) => has_some superset intersection.
    apply: intersection.
    * by case: si_and_ti_has_x.
    * by case: si_and_ti_has_x.
  + move => x st_has_x.
    constructor.
    * case: (filters x) => exist superset intersecion.
      apply: (superset s (s `and` t) _ st_has_x).
      by apply: intersection_left_includes.
    * case: (filters x) => exist superset intersecion.
      apply: (superset t (s `and` t) _ st_has_x).
      by apply: intersection_right_includes.
Qed.

Hypothesis extensionality : forall (s t: SX), s `equiv` t -> s = t.

Theorem interior_derives_neighborhood (i: SX->SX): Interior i -> Neighborhood (i2n i).
Proof.
move => interior.
case: interior => preserve_total intensive intersection.
constructor.
- move => x.
  constructor.
  + exists (TX).
    apply: (proj2 preserve_total).
    by constructor.
  + move => s t s_includes_t ti_has_x.
    apply: (intersection_left_includes (A:=(i s)) (B:=(i t)) (x:=x)).
    apply: ((proj2 (intersection s t)) x).
    move: (extensionality (includsion_intersection s_includes_t)) => st_eq_t. (* use extensionality *)
    by rewrite st_eq_t.
  + move => s t si_has_x ti_has_x.
    apply: ((proj1 (intersection s t)) x).
    constructor.
    * by apply si_has_x.
    * by apply ti_has_x.
- move => x s si_has_x.
  by apply: intensive.
Qed.

End Pretopologies.
