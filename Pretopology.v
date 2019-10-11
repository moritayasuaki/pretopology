From mathcomp Require Import all_ssreflect.
Require Export Ensembles.
Require Export Constructive_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Notation "^ X" := (Ensemble X) (at level 0). 

Definition upper_close {X: Type} (F: ^^X) := forall v w: ^X, In _ F v -> Included _ v w -> In _ F w.
Definition intersection_close {X: Type} (F: ^^X) := forall v w: ^X, In _ F v -> In _ F w -> In _ F (Intersection _ v w).

Class Filter {X: Type} (F: ^^X) := {
  filter_nonempty: exists x, In _ F x;
  filter_upper: upper_close F;
  f_intersection_close: intersection_close F;
}.

Theorem fullset_in_filter {X: Type} (F: ^^X) : Filter F -> In _ F (Full_set _).
Proof.
move=> F_is_filter.
case F_is_filter.
move=> nonempty upper intersection.
case nonempty.
move=> v.
assert (Included _ v (Full_set _)).
-rewrite /Included.
 rewrite /In.
 by constructor.
move=> v_in_F.
rewrite /upper_close in upper.
apply (upper v (Full_set _)).
by [].
by [].
Qed.

Theorem comp {X: Type} : forall v: ^X, Included X v (Complement _ (Empty_set _)) .
rewrite /Included.
move=> v x i.
rewrite /In.
rewrite /Complement.
rewrite /not.
move=> H.
contradiction H.
Qed.

Theorem compEmpty {X: Type} (F: ^^X) : Filter F -> In _ F (Complement _ (Empty_set _)).
Proof.
move=> F_is_filter.
case F_is_filter.
move=> e u i.
case e.
move=> b c.
rewrite /upper_close in u.
apply (u b (Complement _ (Empty_set _))).
by [].
apply (comp).
Qed.


Class Preneighborhood {X: Type} (V: X -> ^^X) := {
  neighborhood :> forall x: X, Filter (V x);
  inclusion : forall x: X, forall v: ^X, In _ (V x) v -> In _ v x
}.




Class Preclosure {X: Type} (C: ^X -> ^X) := {
  zero: Included X (C (Empty_set _)) (Empty_set _);
  incl: forall A: ^X, Included _ A (C A);
  union: forall A B: ^X, C(Union _ A B) = Union _ (C A) (C B);
}.

Definition PreneighborhoodToPreclosure {X: Type} (V: X -> ^^X) :=
  fun A: ^X => Complement _ (fun x: X => In _ (V x) (Complement X A)).

Theorem t: forall X (V: X-> ^^X), Preneighborhood V -> Preclosure (PreneighborhoodToPreclosure V).
Proof.
move=> X V p.
case p.
move=> n0 i0.
move: n0.
rewrite /PreneighborhoodToPreclosure.
split.
-rewrite /Included.
 intros.
 contradiction H.
 apply compEmpty.
 apply n0.
-rewrite /Included.
 intros.
specialize (i0 x).
specialize (n0 x).
case n0.
intro.
intro.
intro.
rewrite /In.
contradiction H.
destruct filter_nonempty0.
rewrite /not.
