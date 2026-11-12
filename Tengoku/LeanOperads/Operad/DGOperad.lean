/-
# Graded and dg operads, and the homology operad

A **graded operad** (`GrOperad`) is an operad in super modules: every space of operations carries
a parity decomposition (the projections `par false` and `par true`), relabellings and
compositions respect parities, and parallel associativity holds up to the Koszul sign
`σ(|y| |z|)` of `Operad.GerBV`. A **dg operad** (`DGOperad`) has moreover an odd differential
commuting with relabellings, vanishing on the unit, which is a derivation of the compositions:
`d (x ∘ᵢ y) = d x ∘ᵢ y + ε x ∘ᵢ d y`, `ε = par false - par true` being the parity involution.

**The homology of a dg operad is a graded operad** (`DGOperad.instGrOperadHomology`): a composite
of cycles is a cycle, and a composite with a boundary is a boundary, so the relabellings, the
unit, the compositions and the parity decomposition descend to homology
(`DGOperad.hcomp_cls`), and the axioms hold on representatives — homogeneous ones for parallel
associativity, which exist because the parity projections act on homology.
-/
import Tengoku.LeanOperads.Operad.Perturbation
import Tengoku.LeanOperads.Operad.GerBV
import Tengoku.LeanOperads.Operad.Sym

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v

namespace Operad

open Sym GerBV

/-! ## Graded operads -/

/-- **A graded operad in super modules**: operations with a parity decomposition, relabellings and
compositions preserving parities, and parallel associativity up to the Koszul sign.-/
class GrOperad (R : Type u) [CommRing R]
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] where
  /-- The parity projections.-/
  par {A : Type} [Fintype A] [DecidableEq A] : Bool → P A →ₗ[R] P A
  /-- Every operation is the sum of its even and odd parts.-/
  par_add {A : Type} [Fintype A] [DecidableEq A] (x : P A) : par false x + par true x = x
  /-- The parity projections are complementary idempotents.-/
  par_par {A : Type} [Fintype A] [DecidableEq A] (b b' : Bool) (x : P A) :
    par b (par b' x) = if b = b' then par b' x else 0
  /-- Relabelling the inputs along a bijection.-/
  map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    (A ≃ B) → P A →ₗ[R] P B
  map_refl {A : Type} [Fintype A] [DecidableEq A] (x : P A) : map (Equiv.refl A) x = x
  map_trans {A B C : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (e : A ≃ B) (f : B ≃ C) (x : P A) :
    map (e.trans f) x = map f (map e x)
  /-- Relabelling preserves parities.-/
  map_par {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (b : Bool) (x : P A) : map e (par b x) = par b (map e x)
  /-- The identity operation, even.-/
  one : P Unit
  par_one : par false one = one
  /-- Insert an operation at the input `i`.-/
  comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A) :
    P A →ₗ[R] P B →ₗ[R] P (Without A i ⊕ B)
  /-- Composition adds parities.-/
  comp_par {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (p q : Bool) (x : P A) (y : P B) :
    par (xor p q) (comp i (par p x) (par q y)) = comp i (par p x) (par q y)
  map_comp {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] (σ : A ≃ A') (τ : B ≃ B') (i : A)
    (x : P A) (y : P B) :
    map (compEquiv σ τ i) (comp i x y) = comp (σ i) (map σ x) (map τ y)
  comp_one {A : Type} [Fintype A] [DecidableEq A] (i : A) (x : P A) :
    map (rightUnitEquiv i) (comp i x one) = x
  one_comp {B : Type} [Fintype B] [DecidableEq B] (y : P B) :
    map (leftUnitEquiv B) (comp () one y) = y
  comp_assoc_seq {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] (i : A) (j : B) (x : P A) (y : P B) (z : P D) :
    map (seqEquiv i j D) (comp (Sum.inr j) (comp i x y) z) = comp i x (comp j y z)
  /-- **Parallel associativity, up to the Koszul sign** of exchanging `y` and `z`.-/
  comp_assoc_par {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {i k : A} (hik : i ≠ k) (x : P A) {q r : Bool} {y : P B}
    {z : P D} (hy : par q y = y) (hz : par r z = z) :
    map (parEquiv hik B D) (comp (Sum.inl ⟨k, Ne.symm hik⟩) (comp i x y) z)
      = σ R (q && r) • comp (Sum.inl ⟨i, hik⟩) (comp k x z) y

/-! ## dg operads -/

/-- **A dg operad**: a graded operad with an odd differential commuting with relabellings,
vanishing on the unit, which is a derivation of the compositions.-/
class DGOperad (R : Type u) [CommRing R]
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
    [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] extends GrOperad R P where
  /-- The differential.-/
  d {A : Type} [Fintype A] [DecidableEq A] : P A →ₗ[R] P A
  d_d {A : Type} [Fintype A] [DecidableEq A] (x : P A) : d (d x) = 0
  /-- The differential is odd.-/
  d_par {A : Type} [Fintype A] [DecidableEq A] (b : Bool) (x : P A) :
    d (par b x) = par (!b) (d x)
  map_d {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : A ≃ B)
    (x : P A) : map e (d x) = d (map e x)
  d_one : d one = 0
  /-- **The Leibniz rule**, the sign carried by the parity involution.-/
  d_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (i : A)
    (x : P A) (y : P B) :
    d (comp i x y) = comp i (d x) y + comp i (par false x - par true x) (d y)

namespace DGOperad

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [DGOperad R P]

open GrOperad

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The differential, with the ring made explicit.-/
local notation "𝐝" => DGOperad.d (R := R) (P := P)

/-- The parity projections, with the ring made explicit.-/
local notation "𝐩" => GrOperad.par (R := R) (P := P)

/-- The compositions, with the ring made explicit.-/
local notation "𝐜" => GrOperad.comp (R := R) (P := P)

omit [Fintype B] [DecidableEq B] in
/-- The parity involution anticommutes with the differential.-/
lemma d_eps (x : P A) : 𝐝 (𝐩 false x - 𝐩 true x) = -(𝐩 false (𝐝 x) - 𝐩 true (𝐝 x)) := by
  rw [map_sub, d_par, d_par]
  simp only [Bool.not_false, Bool.not_true]
  abel

omit [Fintype B] [DecidableEq B] in
lemma eps_eps (x : P A) :
    𝐩 false (𝐩 false x - 𝐩 true x) - 𝐩 true (𝐩 false x - 𝐩 true x) = x := by
  simp only [map_sub, par_par, ite_true, Bool.false_eq_true, ite_false, Bool.true_eq_false,
    sub_zero, zero_sub, sub_neg_eq_add]
  exact par_add x

/-- **A composite of cycles is a cycle.**-/
lemma comp_cycle (i : A) {x : P A} {y : P B} (hx : 𝐝 x = 0) (hy : 𝐝 y = 0) :
    𝐝 (𝐜 i x y) = 0 := by
  rw [d_comp, hx, hy, map_zero, LinearMap.zero_apply, map_zero, add_zero]

/-- **A boundary composed with a cycle is a boundary.**-/
lemma comp_boundary_left (i : A) (w : P A) {y : P B} (hy : 𝐝 y = 0) :
    𝐜 i (𝐝 w) y = 𝐝 (𝐜 i w y) := by
  rw [d_comp, hy, map_zero, add_zero]

/-- **A cycle composed with a boundary is a boundary.**-/
lemma comp_boundary_right (i : A) {x : P A} (hx : 𝐝 x = 0) (w : P B) :
    𝐜 i x (𝐝 w) = 𝐝 (𝐜 i (𝐩 false x - 𝐩 true x) w) := by
  rw [d_comp, d_eps, hx]
  simp only [map_zero, sub_zero, neg_zero, LinearMap.zero_apply, zero_add]
  rw [eps_eps]

/-! ## The homology operad -/

variable (R P) in
/-- **The homology of a dg operad**, arity by arity.-/
@[nolint unusedArguments]
def HomologyOp (A : Type) [Fintype A] [DecidableEq A] : Type v :=
  Homology R (DGOperad.d (R := R) (P := P) (A := A))

instance (A : Type) [Fintype A] [DecidableEq A] : AddCommGroup (HomologyOp R P A) :=
  inferInstanceAs (AddCommGroup (Homology R _))

instance (A : Type) [Fintype A] [DecidableEq A] : Module R (HomologyOp R P A) :=
  inferInstanceAs (Module R (Homology R _))

/-- The class of a cycle.-/
def cls (x : P A) (hx : 𝐝 x = 0) : HomologyOp R P A := Homology.mk 𝐝 ⟨x, hx⟩

omit [Fintype B] [DecidableEq B] in
lemma cls_congr {x x' : P A} (h : x = x') (hx : 𝐝 x = 0) (hx' : 𝐝 x' = 0) :
    cls x hx = cls x' hx' := by
  subst h
  rfl

omit [Fintype B] [DecidableEq B] in
lemma exists_cls (X : HomologyOp R P A) : ∃ (x : P A) (hx : 𝐝 x = 0), cls x hx = X := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := Homology.mk_surjective _ X
  exact ⟨x, hx, rfl⟩

/-- **A linear map sending cycles to cycles and boundaries to boundaries acts on homology.**-/
def homMap (f : P A →ₗ[R] P B) (hc : ∀ x, 𝐝 x = 0 → 𝐝 (f x) = 0)
    (hb : ∀ w, ∃ w', f (𝐝 w) = 𝐝 w') : HomologyOp R P A →ₗ[R] HomologyOp R P B :=
  Submodule.mapQ _ _ (f.restrict fun x hx => hc x hx) fun z hz => by
    obtain ⟨w, hw⟩ := hz
    obtain ⟨w', hw'⟩ := hb w
    exact ⟨w', by rw [← hw', hw]; rfl⟩

/-- The composite with a cycle, on cycles.-/
def compCyc (i : A) (x : LinearMap.ker (𝐝 : P A →ₗ[R] P A)) :
    LinearMap.ker (𝐝 : P B →ₗ[R] P B) →ₗ[R] LinearMap.ker (𝐝 : P (Without A i ⊕ B) →ₗ[R] _) :=
  (𝐜 i x.1).restrict fun _ hy => comp_cycle i x.2 hy

end DGOperad

end Operad
