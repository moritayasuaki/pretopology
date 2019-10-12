From mathcomp Require Import all_ssreflect.
Require Export Ensembles.
Require Export Constructive_sets.
Require Export Classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Pretopologies.
Notation "^ X" := (Ensemble X) (at level 0). 


Theorem any_subsets_included_by_fullset {X: Type} (v: ^X) : Included _ v (Full_set _).
Proof.
move =>  x x_in_v.
apply: Full_intro.
Qed.

Theorem any_subsets_included_by_complement_of_emptyset {X: Type} : forall v: ^X, Included X v (Complement _ (Empty_set _)) .
move=> v x x_in_v x_in_empty.
by case: x_in_empty.
Qed.

Theorem compl_union_included_by_intersection_compl {X: Type} (A B: ^X) : Included _ (Complement _ (Union _ A B)) (Intersection _ (Complement _ A) (Complement _ B)).
Proof.
move => x x_in_complement_of_union.
apply: Intersection_intro.
- move => ax.
  apply: x_in_complement_of_union.
  by apply: Union_introl.
- move => bx.
  apply: x_in_complement_of_union.
  by apply: Union_intror.
Qed.

Theorem intersection_included_l {X: Type} (A B: ^X) : Included _ (Intersection _ A B) A.
Proof.
move => x x_in_ab.
by case: x_in_ab => x_in_a x_in_b.
Qed.

Theorem intersection_included_r {X: Type} (A B: ^X) : Included _ (Intersection _ A B) B.
Proof.
move => x x_in_ab.
by case: x_in_ab => x_in_a x_in_b.
Qed.


Class Filter {X: Type} (F: ^^X) := {
  filter_nonempty: exists x, In _ F x;
  filter_superset: forall A B: ^X, In _ F A -> Included _ A B -> In _ F B;
  filter_intersection: forall A B: ^X, In _ F A -> In _ F B -> In _ F (Intersection _ A B);
}.

Theorem fullset_in_filter {X: Type} (F: ^^X) : Filter F -> In _ F (Full_set _).
Proof.
move=> f_is_filter.
case: f_is_filter => nonempty superset intersection.
case: nonempty => v v_in_f.
apply: (superset v).
- by apply: v_in_f.
- by apply: any_subsets_included_by_fullset.
Qed.


Theorem complement_of_empty_in_filter {X: Type} (F: ^^X) : Filter F -> In _ F (Complement _ (Empty_set _)).
Proof.
move=> F_is_filter.
case: F_is_filter => nonempty superset intersection.
case: nonempty => v v_in_f.
apply: (superset v).
- by apply: v_in_f.
- by apply: any_subsets_included_by_complement_of_emptyset.
Qed.

Class Neighborhood {X: Type} (V: X -> ^^X) := {
  neighborhood_filters :> forall x: X, Filter (V x);
  neighborhood_elem : forall (x: X) (v: ^X), In _ (V x) v -> In _ v x
}.

Class Interior {X: Type} (I: ^X -> ^X) := {
  interior_total_space : Same_set _ (Full_set X) (I (Full_set X));
  interior_intensive : forall (A: ^X), Included _ (I A) A;
  interior_intersection : forall A B: ^X, Same_set _ (I (Intersection _ A B)) (Intersection _ (I A) (I B));
}.

Definition neighborhood_interior {X: Type} (V: X -> ^^X) (S: ^X) (x: X) := In _ (V x) S.
Definition interior_neighborhood {X: Type} (I: ^X -> ^X) (x: X) (S: ^X) :=  In _ (I S) x.
Definition interior_exterior {X: Type} (I: ^X -> ^X) (S: ^X) := I (Complement _ S).
Definition exterior_interiot {X: Type} (E: ^X -> ^X) (S: ^X) := E (Complement _ S).
Definition exterior_closure {X: Type} (E: ^X -> ^X) (S: ^X) := Complement _ (E S).
Definition closuer_exterior {X: Type} (C: ^X -> ^X) (S: ^X) := Complement _ (C S).

Theorem neighborhood_derives_interior {X: Type} (V: X -> ^^X) : Neighborhood V -> Interior (neighborhood_interior V).
move => neighborhood_v.
case: neighborhood_v => filters elem.
apply: Build_Interior.
- apply: conj.
  + move => x x_in_full. (* total_space *)
    by apply: (fullset_in_filter (filters x)).
  + move=> x x_in_interior.
    by apply: Full_intro.
- move => A x x_in_interior. (* intensive *)
  case: (filters x) => nonempty superset intersection.
  apply: elem.
  by apply: x_in_interior.
- move => A B. (* intersection *)
  constructor.
  move => x x_in_ab.
  constructor.
  + case: (filters x) => nonempty superset intersection.
    apply: (superset (Intersection _ A B) A x_in_ab).
    by apply: intersection_included_l.
  + case: (filters x) => nonempty superset intersection.
    apply: (superset (Intersection _ A B) B x_in_ab).
    by apply: intersection_included_r.
- move => x x_in_ia_ib.
  case: (filters x) => nonempty superset intersection.
  apply: intersection.
  + by case: x_in_ia_ib => y a b.
  + by case: x_in_ia_ib => y a b.
Qed.

Theorem interior_derives_neighborhood {X: Type} (I: ^X -> ^X) : Interior I -> Neighborhood (interior_neighborhood I).
move => interior_i.
case: interior_i => total intensive intersection.
move: (Build_Neighborhood (X:=X) (V:=interior_neighborhood I)) => p.
apply: p.


Class Preexterior {X: Type} (ext: ^X -> ^X) := {
}.
Class Preclosure {X: Type} (C: ^X -> ^X) := {
  zero: Included X (C (Empty_set _)) (Empty_set _);
  incl: forall A: ^X, Included _ A (C A);
  union: forall A B: ^X, Included _ (C (Union _ A B)) (Union _ (C A) (C B));
}.

