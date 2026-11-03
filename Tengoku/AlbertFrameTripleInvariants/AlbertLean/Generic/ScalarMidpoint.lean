import Tengoku.Seed.LinearAlgebra.BilinearMap
import Tengoku.Seed.Tactic.Module
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms midpoint_products` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms midpoint_square` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms midpoint_reflection_apply` (it only prints; the queue checks the axioms of every declaration). -/

/-! Source-only scalar midpoint implication. The entire pair multiplication
 table is a hypothesis. No Albert algebra, primitive predicate, unit, Jordan
 identity, or Peirce automorphism theorem is defined or assumed implicitly. -/

noncomputable section
namespace AlbertLean.Generic.ScalarMidpoint

universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The six entries of the symmetric pair table; this is explicit input data.-/
structure PairTable (μ : V →ₗ[K] V →ₗ[K] V) (e f c : V) (t : K) : Prop where
  ee : μ e e = e
  ff : μ f f = f
  ef : μ e f = c
  ec : μ e c = (1 / 2 : K) • (c + t • e)
  fc : μ f c = (1 / 2 : K) • (c + t • f)
  cc : μ c c = (t / 4) • (e + f + (2 : K) • c)

/-- Literal division of a module vector is multiplication by the scalar inverse.-/
def midpoint (e f c : V) (s : K) : V :=
  (2 * (1 + s))⁻¹ • (e + f + (2 / s) • c)

private theorem one_add_ne_zero {s : K} (hs : s ≠ -1) : 1 + s ≠ 0 := by
  intro h
  apply hs
  calc
    s = (1 + s) - 1 := by ring
    _ = -1 := by rw [h]; simp

/-- The three scalar-normalized products that make the midpoint useful.
Symmetry is used only for the reverse entries of the explicit pair table.
@isnad1 id=and.5h8v.s11.c8485172e45d from=translated src=- shape=25135b60 vocab=d7f228de
-/
theorem midpoint_products
    (μ : V →ₗ[K] V →ₗ[K] V) (hsym : ∀ x y, μ x y = μ y x)
    (e f c : V) (t s : K) (h : PairTable μ e f c t)
    (hsquare : s ^ 2 = t) (hs0 : s ≠ 0) (hsneg : s ≠ -1) :
    μ (midpoint e f c s) e = (1 / 2 : K) • e + (1 / (2 * s)) • c ∧
    μ (midpoint e f c s) f = (1 / 2 : K) • f + (1 / (2 * s)) • c ∧
    μ (midpoint e f c s) c = (s / 4) • (e + f) + (1 / 2 : K) • c := by
  subst t
  have hs1 := one_add_ne_zero hsneg
  have hfe : μ f e = c := (hsym f e).trans h.ef
  have hce : μ c e = (1 / 2 : K) • (c + s ^ 2 • e) :=
    (hsym c e).trans h.ec
  have hcf : μ c f = (1 / 2 : K) • (c + s ^ 2 • f) :=
    (hsym c f).trans h.fc
  refine ⟨?_, ?_, ?_⟩
  all_goals
    dsimp only [midpoint]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      h.ee, h.ff, h.ef, hfe, h.ec, hce, h.fc, hcf, h.cc]
    match_scalars <;> field_simp [hs0, hs1] <;> ring

/-- Idempotence of the literal midpoint, conditional on the six pair entries.
@isnad1 id=eq.5h8v.s10.13ab8203a022 from=translated src=- shape=0349caea vocab=1a138ec2
-/
theorem midpoint_square
    (μ : V →ₗ[K] V →ₗ[K] V) (hsym : ∀ x y, μ x y = μ y x)
    (e f c : V) (t s : K) (h : PairTable μ e f c t)
    (hsquare : s ^ 2 = t) (hs0 : s ≠ 0) (hsneg : s ≠ -1) :
    μ (midpoint e f c s) (midpoint e f c s) = midpoint e f c s := by
  obtain ⟨he, hf, hc⟩ := midpoint_products μ hsym e f c t s h hsquare hs0 hsneg
  have hs1 := one_add_ne_zero hsneg
  change μ (midpoint e f c s)
      ((2 * (1 + s))⁻¹ • (e + f + (2 / s) • c)) =
    (2 * (1 + s))⁻¹ • (e + f + (2 / s) • c)
  simp only [map_add, map_smul, he, hf, hc]
  match_scalars <;> field_simp [hs0, hs1] <;> ring

/-- The prescribed quadratic expression sends e to f. This theorem does not
assert that this expression is an automorphism on the surrounding module.
@isnad1 id=eq.5h8v.s11.8a4d6d7e0fdb from=translated src=- shape=4b09ef5e vocab=a2cea538
-/
theorem midpoint_reflection_apply
    (μ : V →ₗ[K] V →ₗ[K] V) (hsym : ∀ x y, μ x y = μ y x)
    (e f c : V) (t s : K) (h : PairTable μ e f c t)
    (hsquare : s ^ 2 = t) (hs0 : s ≠ 0) (hsneg : s ≠ -1) :
    e - (8 : K) • μ (midpoint e f c s) e +
      (8 : K) • μ (midpoint e f c s) (μ (midpoint e f c s) e) = f := by
  obtain ⟨he, _, hc⟩ := midpoint_products μ hsym e f c t s h hsquare hs0 hsneg
  simp only [he, map_add, map_smul, hc]
  match_scalars <;> field_simp [hs0] <;> ring

end AlbertLean.Generic.ScalarMidpoint
