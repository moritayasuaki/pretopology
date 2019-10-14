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

Class Upperset (u: SSX) := {
  upperset_nonempty : exists s : SX, u `has` s;
  upperset: forall (s t: SX), s `includes` t -> u `has` t -> u `has` s;
}.

Theorem upperset_has_total (u: SSX) : Upperset u -> u `has` TX.
Proof.
  case => nonempty upper.
  case: nonempty => s u_has_s.
  apply: (upper TX s).
  - by apply: total_includes.
  - by apply: u_has_s.
Qed.

Class Downward (d: SSX) := {
  downward: True;
}.

Class Filter (f: SSX) := {
  filter_upperset :> Upperset f;
  filter_downward :> Downward f;
}.


Class Neighborhood v := {
  neighborhood_filter :> forall x: X, Filter (v x);
  neighborhood_has_point : forall (x: X) (s: SX), v x `has` s -> s `has` x;
}.

Class Interior (i: SX->SX) := {
  interior_preserve_total : TX `equiv` i TX;
  interior_intensive_law : forall (s: SX), s `includes` i s;
  interior_functor_law: forall s t: SX, (s `includes` t) -> (i s) `includes` (i t); 
}.


Definition n2i (v: X -> SSX) := fun s:SX => fun x:X => (v x) `has` s.
Definition i2n i := fun x:X => fun s:SX => (i s) `has` x.

Theorem neighborhood_derives_interior (v: X->SSX): Neighborhood v -> Interior (n2i v).
Proof.
  case => filters has_point.
  constructor.
  - constructor.
    + by apply: total_includes.
    + move => x total_has_x.
      move: (filters x) => filter.
      case: filter => upper downward.
      by apply: (upperset_has_total (u:=(v x)) upper).
  - move => s x interior_has_s.
    case: (filters x) => upper downward.
    apply: has_point.
    by apply: interior_has_s.
  - move => s t s_includes_t x vx_has_t.
    case: (filters x) => upper downward.
    case: upper => nonempty upper.
    by apply: (upper s t s_includes_t).
Qed.

Theorem interior_derives_neighborhood (i: SX->SX): Interior i -> Neighborhood (i2n i).
Proof.
  move => interior.
  case: interior => preserve_total intensive functor.
  constructor.
  - move => x.
    constructor.
    + constructor.
      exists (TX).
      apply: (proj2 preserve_total).
      by constructor.
    + move => s t s_includes_t ti_has_x.
      by apply: (functor s t s_includes_t).
    + by constructor.
  - move => x s si_has_x.
    by apply: intensive.
Qed.

Class Filter2 (f: SSX) := {
  filter2_upperset :> Upperset f;
  filter2_intersection_law : forall s t : SX, f `has` s -> f `has` t -> f `has` s `and` t;
}.

Theorem ext_multiply (f: SSX) : (forall (s t : SX), f `has` s -> f `has` t -> f `has` s `and` t) -> (forall (s t: SX), f `has` s -> f `has` t -> exists u, (s `includes` u) /\ (t `includes` u))  .
Proof.
  - move => mul s t fs ft.
    apply: (ex_intro (fun u => s `includes` u /\ t `includes` u) (s `and` t)).
    constructor.
    
  - move => alpo s t f_has_s f_has_t.
    move: (alpo s t f_has_s f_has_t) => asdf.
    case: asdf => s_and_t P.
    case: P => l r.
    move: (Intersection_intro (X:=X) (A:=s) (B:=t)) => g.
    compute in g.
    compute in l.
    compute in r.
    compute.

Class Neighborhood2 v := {
  neighborhood2_filter :> forall x: X, Filter2 (v x);
  neighborhood2_has_point : forall (x: X) (s: SX), v x `has` s -> s `has` x; 
}.

Theorem neighborhood2_derives_interior (v: X->SSX): Neighborhood2 v -> Interior (n2i v).
Proof.
case => filters has_point.
constructor.
- constructor.
  + by apply: total_includes.
  + move => x total_has_x.
    case: (filters x) => upper intersection.
    by apply: upperset_has_total.
- move => s x interior_has_s.
  case: (filters x) => upper intersection.
  apply: has_point.
  by apply: interior_has_s.
- move => s t s_includes_t x vx_has_t.
  case: (filters x) => upper intersection.
  case: upper => nonempty upper.
  by apply: (upper s t s_includes_t).
Qed.

Hypothesis extensionality : forall (s t: SX), s `equiv` t -> s = t.

Class Interior2 (i: SX->SX) := {
  interior2_preserve_total : TX `equiv` i TX;
  interior2_intensive_law : forall (s: SX), s `includes` i s;
  interior2_intersection_law: forall s t: SX, i (s `and` t) `equiv` (i s) `and` (i t); 
}.

Theorem neighborhood2_derives_interior2 (v: X->SSX): Neighborhood2 v -> Interior2 (n2i v).
Proof.
move => neighborhood.
case: neighborhood => filters has_point.
constructor.
- constructor.
  + by apply: total_includes.
  + move => x total_has_x.
    case: (filters x) => upper intersection.
    by apply: upperset_has_total.
- move => s x interior_has_s.
  case: (filters x) => upper intersection.
  apply: has_point.
  by apply: interior_has_s.
- move => s t.
  constructor.
  + move => x si_and_ti_has_x.
    case: (filters x) => upper intersection.
    apply: intersection.
    * by case: si_and_ti_has_x.
    * by case: si_and_ti_has_x.
  + move => x st_has_x.
    constructor.
    * case: (filters x) => upper intersecion.
      case: upper => nonempty upper.
      apply: (upper s (s `and` t) _ st_has_x).
      by apply: intersection_left_includes.
    * case: (filters x) => upper intersection.
      case: upper => nonempty upper.
      apply: (upper t (s `and` t) _ st_has_x).
      by apply: intersection_right_includes.
Qed.

Theorem interior2_derives_neighborhood2 (i: SX->SX): Interior2 i -> Neighborhood2 (i2n i).
Proof.
move => interior.
case: interior => preserve_total intensive intersection.
constructor.
- move => x.
  constructor.
  + constructor.
    exists (TX).
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
