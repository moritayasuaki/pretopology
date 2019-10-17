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
Definition pow:= Ensemble.



Class Upward {T} (o: relation T) (u: pow T) := {
  upward (s t: T) : o s t -> u s -> u t;
}.

Class Nonempty {T} (u: pow T) := {
  nonempty: exists s, u s;
}.

Class Proper {T} (p: pow (pow T)) := {
  proper: ~ p Empty_set 
}.

Class Directed {T} (o: relation T) (d: pow T) := {
  directed (s t: T) : d s -> d t -> exists u, (d u /\ o u s /\ o u t);
}.

Class Filter {T} (f: pow (pow T)) := {
  filter_nonempty :> Nonempty f; (* => implies having total set with upward property *)
  filter_upward :> Upward Included f;
  filter_directed :> Directed Included f;
  filter_preserve_intersection (s t: pow T) : f s -> f t -> f (s && t);
}.

Class Neighborhood {T} (n: T -> pow (pow T)) := {
  neighborhood_filters (x:T) : Filter (n x);
  neighborhood_point (x:T) (s: pow T) : n x s -> s x;
}.

Class Interior {T} (i: pow T -> pow T) := {
  interior_preserve_total : Full_set == i Full_set;
  interior_intensivity (s: pow T) : i s <= s;
  interior_isotonic (s t: pow T) : s <= t -> i s <= i t;
  interior_preserve_intersection (s t: pow T) : i (s && t) == (i s) && (i t);
}.

Lemma isotonic_implies_intersection T (i: pow T -> pow T): (forall s t: pow T, s <= t -> i s <= i t) -> (forall s t, i (s && t) <= (i s) && (i t)).
move => isotonic.
have: forall s t: pow T, s && t <= s.
- move => s t x stx.
  by case: stx.
move => incr.
have: forall s t: pow T, s && t <= t.
- move => s t x stx.
  by case: stx.
move => incl.
move => s t x istx.
split.
- by apply: (isotonic (s && t) s (incr s t)).
- by apply: (isotonic (s && t) t (incl s t)).
Qed.


Lemma and_in T (s t: pow T): forall x: T, s x -> t x -> (s && t) x.
move => x sx tx.
by constructor.
Qed.

Lemma iso2 (p : Prop -> Prop): (forall a b: Prop, (a -> b) -> p a -> p b) -> (forall a:Prop, p a -> a) -> (forall a b: Prop, (p a) /\ (p b) -> p (a /\ b)).
move => iso inc a b pab.
case: pab => pa pb.
move: (inc a pa) => ta.
move: (inc b pb) => tb.
apply: (iso (a) (a /\ b)).
move => ta2.
constructor.
by exact.
by exact.
by exact.
Qed.

Lemma iso3 (p : Prop -> Prop): (forall a b: Prop, (a -> b) -> p a -> p b) -> (forall a:Prop, p a -> a) -> (forall a b: Prop, p (a /\ b) -> (p a) /\ (p b)).
move => iso inc a b pab.
constructor.
apply: (iso (a /\ b) a).
move=> ab.
by case ab.
exact pab.
apply: (iso (a /\ b) b).
move=> ab.
by case ab.
exact pab.
Qed.

Class Closure {T} (c: pow T -> pow T) := {
  closure_preserve_empty : Empty_set == c Empty_set;
  closure_extensivity (s: pow T) : s <= c s;
  closure_isotonic (s t: pow T) : s <= t -> c s <= c t;
  closure_preserve_union (s t: pow T) : c (s || t) == (c s) || (c t);
}.


Lemma intersection_with_complement_of_itself_is_empty {T} (c: pow T -> pow T) : forall s: pow T, (s && ~~s) <= Empty_set.
move => s x sinsx.
case: sinsx => p sx nsx.
exfalso.
by apply nsx.
Qed.

Lemma union_complement_total_classic {T}: (forall s: pow T, Full_set <= (s || ~~s)) -> (forall s: pow T, (~~~~s) <= s).
have: (forall (v: pow T), (Full_set <= v) -> forall x: T, In v x).
- move => s p x.
  by apply p.
move => i u s x.
move: (i (s || ~~s) (u s) x) => sucsx.
by case: x / sucsx => x sx ccsx.
Qed.

Definition n2i {T} (v: T -> pow (pow T)) (s: pow T) (x:T) := v x s.
Definition i2n {T} (i: pow T -> pow T) (x:T) (s: pow T) := i s x.
Definition i2c {T} (i: pow T -> pow T) (s: pow T) := ~~ (i (~~ s)).
Definition c2i {T} (c: pow T -> pow T) (s: pow T) := ~~ (c (~~ s)).

Lemma projl {T} : forall s t : pow T, s && t <= s.
Proof.
move => s t x stx.
by case: stx => y sx tx.
Qed.

Lemma projr {T} : forall s t : pow T, s && t <= t.
Proof.
move => s t x stx.
by case: stx => y sx tx.
Qed.

Theorem neighborhood_derives_interior {T} (n: T->pow (pow T)): Neighborhood n -> Interior (n2i n).
Proof.
  move => neighborhood.
  case: neighborhood => filters base.
  constructor.
  - constructor.
    + move => x fx.
      move: (filters x) => filter.
      case: filter => nonempty upward directed intersection; case: upward => upward; case: nonempty => nonempty; case: directed => directed.
      case: nonempty => s nxs.
      apply: (fun g => (upward s Full_set) g nxs).
      by constructor.
    + move => x n2in.
      by constructor.
  - move => s x nxs.
    case: (filters x)=> nonempty upward directed interseciton.
    case: upward => upward.
    by apply: (base x s).
  - move => s t s_included_t x nxs.
    case: (filters x) => nonemtpy upward directed intersection.
    case: upward => upward.
    by apply: (upward s t s_included_t).
  - move => s t.
    constructor.
    + move => x nxst.
      move: (filters x) => filter.
      case: filter => nonempty upward directed intersection; case: upward => upward; case: nonempty => nonempty; case: directed => directed.
      constructor.
      * move: (projl (T:=T) (s:=s) (t:=t)) => projl.
        apply: (upward (s && t) s projl).
        by apply: nxst.
      * move: (projr(T:=T) (s:=s) (t:=t)) => projr.
        apply: (upward (s && t) t projr).
        by apply: nxst.
    + move => x nsntx.
      case: x /nsntx => x l r.
      move: (filters x) => filter.
      case: filter => nonempty upward directed intersection; case: upward => upward; case: nonempty => nonempty; case: directed => directed.
      by apply: (intersection s t l r).
Qed. 

Theorem interior_derives_neighborhood {T} (i: pow T -> pow T): Interior i -> Neighborhood (i2n i).
Proof.
  move => interior.
  case: interior => preserve_total intensive isotonic intersection.
  constructor.
  - move => x.
    constructor.
    + constructor.
      exists Full_set.
      apply: (proj1 preserve_total).
      by constructor.
    + constructor.
      move => s t s_included_t isx.
      apply: (isotonic s t s_included_t).
      by apply: isx.
    + constructor.
      move => s t isx itx.
      exists (s && t).
      - constructor.
        compute.
        apply: (proj2 (intersection s t)).
        by constructor.
      - constructor.
        + by apply: projl.
        + by apply: projr.
    + move => s t isx itx.
      apply: (proj2 (intersection s t)).
      by constructor.
  - move => x s isx.
    by apply: intensive.
Qed.

Theorem contra {T} (s t: pow T) : s <= t -> ~~t <= ~~s.
Proof.
  move => s_implies_t x ctx sx.
  apply: ctx.
  by apply: s_implies_t.
Qed.

Theorem contra2 {T} (s t: pow T) : s <= ~~t -> t <= ~~s.
Proof.
  move => s_implies_ct x tx sx.
  by apply: (s_implies_ct x sx).
Qed.

Lemma injl {T} : forall s t : pow T, s <= s || t.
Proof.
move => s t x stx.
by constructor 1.
Qed.

Lemma injr {T} : forall s t : pow T, t <= s || t.
Proof.
move => s t x stx.
by constructor 2.
Qed.

Lemma b {T} : forall s: pow T, s <= ~~~~s.
move => a x ax cax.
by contradiction cax.
Qed.

Theorem demorgan1 {T} (s t : pow T) : (~~(s || t)) <= (~~s) && (~~t).
Proof.
  move => x nstx.
  constructor.
  - move => sx.
    apply: nstx.
    by constructor 1.
  - move => tx.
    apply: nstx.
    by constructor 2.
Qed.


Axiom cc: forall (T:Type) (s: pow T), ~~~~s <= s.
Theorem pem {T} (s : pow T) : (~~s) && s <= Empty_set.
move => x nss.
case nss => y nsy sy.
by contradiction nsy.
Qed.
Theorem dual {T} (s t : pow T) : ~~s <= ~~t -> t <= s. (* classic *)
Proof.
move => l x g.
apply: (cc (s:=s)).
move => a.
by apply: (l x a g).
Qed.
Theorem em {T}: (~~Full_set (U:=T) ) <= Empty_set.
move => x nfx.
contradiction nfx.
constructor.
Qed.

Theorem dual2 {T} (s t : pow T) : ~~ (s && t) <= (~~s) || (~~t).  (* classic *)
Proof.
  move=> x nstx.
  apply: cc.
  move=> nnsntx.
  apply: nstx.
  constructor.
  - apply: cc.
    move=> nsx.
    apply: nnsntx.
    by constructor 1.
  - apply: cc.
    move=> nsx.
    apply: nnsntx.
    by constructor 2.
Qed.
Theorem dual3 {T} (s t : pow T) : ~~ (s || t) <= (~~ s) && (~~t).
Proof.
  move => x nstx.
  constructor.
  - move => sx.
    apply: nstx.
    by apply: injl sx.
  - move => tx.
    apply: nstx.
    by apply: injr tx.
Qed.

Theorem dual4 {T} (s t : pow T) : ((~~ s) && (~~t)) <= ~~ (s || t).
Proof.
  move => x nsntx.
  destruct nsntx as [x L R].
  move => nstx.
  destruct nstx as [x LL |x RR].
  by apply: L.
  by apply: R.
Qed.
Theorem iso {T} (i: pow T -> pow T): Interior i -> forall s: pow T, i s <= c2i (i2c i) s.
Proof.
  move => interior s.
  rewrite /i2c /c2i.
  move => x isx ninnsx.
  apply: ninnsx.
  destruct interior.
  move: (interior_isotonic0 s (~~~~s)) => d.
  assert (s <= (~~~~s)).
  - move => v sv nsv.
    by apply: nsv.
  by apply: (d H).
Qed.


Theorem interior_derives_closure {T} (i: pow T -> pow T): Interior i -> Closure (i2c i).
Proof.
  move => interior.
  case: interior => preserve_total intensive isotonic intersection.
  assert (extensivity: forall u: pow T, u <= i2c i u).
  + move => u x ux icux.
    by apply: (intensive (~~u) x icux).
  assert (isotonic_c: forall s t : pow T, s <= t -> i2c i s <= i2c i t).
  + move => s t s_implies_t.
    apply: contra.
    apply: (isotonic (~~t) (~~s)).
    by apply: contra. 
  constructor.
  - constructor.
    + move => x empx.
      by contradiction empx.
    + move => x iempx.
      contradiction iempx.
      rewrite /In.
      assert (empfull: i Full_set <= i (~~Empty_set)).
      * apply: isotonic.
        move => y fully empy.
        by contradiction empy.
      apply: empfull.
      apply: (proj1 preserve_total).
      assert (sf: Singleton x <= Full_set).
      * move => y singy.
       by constructor.
      apply: sf.
      by constructor.
  - by apply: extensivity.
  - by apply: isotonic_c.
  - move => s t.
    constructor.
    + move => x nst.
      apply: dual2. 
      move => nnsnst.
      apply: nst.
      apply: (isotonic ((~~ s) && (~~t)) (~~(s||t))).
      by apply: dual4.
      by apply: (proj2 (intersection (~~s) (~~t))).
    + rewrite /i2c.
      move => x nst instx.
      destruct nst as [x p| x p].
      - apply: p.
        apply: (isotonic (~~( s || t)) (~~s)).
        apply: dual.
        move => p mm mmm.
        apply mm.
        move => mmmm.
        apply: mmm.
        by constructor 1.
        by [].
      - apply: p.
        apply: (isotonic (~~ (s || t)) (~~t)).
        apply: dual.
        move => p mm mmm.
        apply mm.
        move => mmmm.
        apply: mmm.
        by constructor 2.
        by [].
Qed.

Definition image {X Y} (f: X -> Y) (preimage : pow X) := fun y: Y => exists x:X, preimage x /\ (f x = y).
Definition preimage {X Y} (f: X -> Y) (image : pow Y) := fun x: X => exists y:Y, image y /\ (f x = y).
Definition filter_image {X Y} (f: X -> Y) (F : pow (pow X)) := fun fA: pow Y => exists A: pow X, F A /\ image f A <= fA.

Definition converge {T} (f: pow (pow T)) (n: T -> pow (pow T)) (x: T) := n x <= f.
Definition continuous {X Y} (nx: X -> pow (pow X)) (ny: Y -> pow (pow Y)) (f: X -> Y) (x: X):= 
  forall fx : pow (pow X), converge fx nx x -> converge (filter_image f (fx)) ny (f x).

Definition ultrafilter {T} (f: pow (pow T)):= forall g: pow (pow T), f <= g -> f == g.
Definition compact {T} (n: T -> pow (pow T)) := forall g: pow (pow T), ultrafilter g -> exists x:T, converge g n x.
Definition weakest_topology {X Y} (f: X -> Y) (ny: Y -> pow (pow Y)) := fun x: X => fun sx:pow X => ny (f x) (image f sx).
Definition strongest_topology {X Y} (f: X -> Y) (nx: X -> pow (pow X)) := fun y: Y => fun sy:pow Y => sy y /\ exists x:X, nx x (preimage f sy).

Definition multspace {I} {X: I -> Type} (nxi: forall i:I, X i -> pow (pow (X i))) (i: I) := weakest_topology (fun x: X i => x) (nxi i).
End Pretopology.