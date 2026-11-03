import Tengoku.AlbertFrameTripleInvariants.AlbertLean.CubicNorm.ProductRecovery
import Tengoku.Seed.Algebra.Field.Rat
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Automorphisms recovered from a cubic norm and its unit

This file isolates the standard compression argument for a cubic-norm
algebra.  An ambient `Data` record says that its trace pairing and adjoint
have the expected cubic-polarization characterizations.  For that fixed
ambient algebra, a linear bijection preserving only the literal cubic and
the unit automatically preserves the trace, pairing, adjoint, cross product,
and Springer product.

The product-preservation conclusion is therefore derived; it is not a field
of the input preserving map.
-/

noncomputable section

namespace AlbertLean.Generic.CubicAutomorphism

variable {K V : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V]

/-- Full finite-difference polarization, with no factorial normalization.-/
def polar (N : V → K) (x y z : V) : K :=
  N (x + y + z) - N (x + y) - N (x + z) - N (y + z) +
    N x + N y + N z - N 0

/-- A linear equivalence preserving a literal cubic preserves its full
finite-difference polarization.
@isnad1 id=eq.1h7v.s9.3f5f75553157 from=translated src=- shape=283fa356 vocab=72364d30
-/
theorem polar_map (N : V → K) (g : V ≃ₗ[K] V)
    (hCubic : ∀ x, N (g x) = N x) (x y z : V) :
    polar N (g x) (g y) (g z) = polar N x y z := by
  have hxyz : N (g x + g y + g z) = N (x + y + z) := by
    rw [← g.map_add x y, ← g.map_add (x + y) z, hCubic]
  have hxy : N (g x + g y) = N (x + y) := by
    rw [← g.map_add x y, hCubic]
  have hxz : N (g x + g z) = N (x + z) := by
    rw [← g.map_add x z, hCubic]
  have hyz : N (g y + g z) = N (y + z) := by
    rw [← g.map_add y z, hCubic]
  simp only [polar, hxyz, hxy, hxz, hyz, hCubic]

/-- Ambient cubic-norm data needed by the recovery argument.  The trace and
Springer product themselves are defined below from `cubic`, `one`, and
`adjoint`; only the representation properties of the trace form and adjoint
are recorded as laws.-/
structure Data (K V : Type*) [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] where
  cubic : V → K
  one : V
  traceForm : V →ₗ[K] V →ₗ[K] K
  adjoint : V → V
  traceForm_nondegenerate :
    ∀ x : V, (∀ y : V, traceForm x y = 0) → x = 0
  traceForm_formula : ∀ x y : V,
    traceForm x y =
      (polar cubic one one x / 2) * (polar cubic one one y / 2) -
        polar cubic one x y
  adjoint_characterization : ∀ x y : V,
    traceForm (adjoint x) y = polar cubic x x y / 2

namespace Data

variable (D : Data K V)

/-- The linear trace selected by the cubic and unit.-/
def trace (x : V) : K := polar D.cubic D.one D.one x / 2

/-- The bilinear spur selected by the cubic and unit.-/
def spurBilinear (x y : V) : K := polar D.cubic D.one x y

/-- Polarization of the trace-dual cubic adjoint.-/
def cross (x y : V) : V := D.adjoint (x + y) - D.adjoint x - D.adjoint y

/-- The canonical Springer product recovered from the cubic norm and unit.-/
def product (x y : V) : V :=
  (2 : K)⁻¹ •
    (D.cross x y + D.trace x • y + D.trace y • x -
      D.spurBilinear x y • D.one)

/-- A linear equivalence preserving a literal cubic preserves its full
finite-difference polarization.
@isnad1 id=eq.1h7v.s9.8d784ab4c785 from=translated src=- shape=18e85a32 vocab=ea0982e5
-/
theorem map_polar (g : V ≃ₗ[K] V)
    (hCubic : ∀ x, D.cubic (g x) = D.cubic x) (x y z : V) :
    polar D.cubic (g x) (g y) (g z) = polar D.cubic x y z := by
  exact polar_map D.cubic g hCubic x y z

/-- Cubic and unit preservation imply trace preservation.
@isnad1 id=eq.2h5v.s9.b1e2bb6b61bc from=translated src=- shape=e603e460 vocab=ab5ce910
-/
theorem map_trace (g : V ≃ₗ[K] V) (hOne : g D.one = D.one)
    (hCubic : ∀ x, D.cubic (g x) = D.cubic x) (x : V) :
    D.trace (g x) = D.trace x := by
  have hp := D.map_polar g hCubic D.one D.one x
  rw [hOne] at hp
  exact congrArg (fun a => a / 2) hp

/-- Cubic and unit preservation imply preservation of the spur
polarization.
@isnad1 id=eq.2h6v.s9.48df75c58b0b from=translated src=- shape=cbf05286 vocab=15b7c44c
-/
theorem map_spurBilinear (g : V ≃ₗ[K] V) (hOne : g D.one = D.one)
    (hCubic : ∀ x, D.cubic (g x) = D.cubic x) (x y : V) :
    D.spurBilinear (g x) (g y) = D.spurBilinear x y := by
  have hp := D.map_polar g hCubic D.one x y
  rw [hOne] at hp
  exact hp

/-- Cubic and unit preservation imply trace-pairing preservation.
@isnad1 id=eq.2h6v.s10.1f007f0d6e62 from=translated src=- shape=20d1539b vocab=f846be0f
-/
theorem map_traceForm (g : V ≃ₗ[K] V) (hOne : g D.one = D.one)
    (hCubic : ∀ x, D.cubic (g x) = D.cubic x) (x y : V) :
    D.traceForm (g x) (g y) = D.traceForm x y := by
  rw [D.traceForm_formula, D.traceForm_formula]
  change D.trace (g x) * D.trace (g y) - D.spurBilinear (g x) (g y) =
    D.trace x * D.trace y - D.spurBilinear x y
  rw [D.map_trace g hOne hCubic, D.map_trace g hOne hCubic,
    D.map_spurBilinear g hOne hCubic]

/-- Adjoint recovery commutes with a cubic-and-unit preserving linear
equivalence.  Nondegeneracy is used here, rather than product preservation.
@isnad1 id=eq.2h5v.s9.c4c884cbc066 from=translated src=- shape=792269ca vocab=6766cfc2
-/
theorem map_adjoint (g : V ≃ₗ[K] V) (hOne : g D.one = D.one)
    (hCubic : ∀ x, D.cubic (g x) = D.cubic x) (x : V) :
    g (D.adjoint x) = D.adjoint (g x) := by
  apply sub_eq_zero.mp
  apply D.traceForm_nondegenerate
  intro w
  obtain ⟨y, rfl⟩ := g.surjective w
  simp only [map_sub, LinearMap.sub_apply]
  rw [D.map_traceForm g hOne hCubic, D.adjoint_characterization,
    D.adjoint_characterization, D.map_polar g hCubic]
  ring

/-- Cross-product preservation derived from adjoint recovery.
@isnad1 id=eq.2h6v.s9.d2a757adc901 from=translated src=- shape=94495b1f vocab=8f10e2c1
-/
theorem map_cross (g : V ≃ₗ[K] V) (hOne : g D.one = D.one)
    (hCubic : ∀ x, D.cubic (g x) = D.cubic x) (x y : V) :
    g (D.cross x y) = D.cross (g x) (g y) := by
  simp [cross, D.map_adjoint g hOne hCubic]

/-- The compression theorem: cubic and unit preservation force preservation
of the Springer product.
@isnad1 id=eq.2h6v.s9.0eb155dbbd07 from=translated src=- shape=94495b1f vocab=53e28f69
-/
theorem map_product (g : V ≃ₗ[K] V) (hOne : g D.one = D.one)
    (hCubic : ∀ x, D.cubic (g x) = D.cubic x) (x y : V) :
    g (D.product x y) = D.product (g x) (g y) := by
  simp only [product, map_smul, map_add, map_sub,
    D.map_cross g hOne hCubic, D.map_trace g hOne hCubic,
    D.map_spurBilinear g hOne hCubic, hOne]

/-- Unital product automorphisms of the recovered Springer algebra.-/
structure Aut where
  linear : V ≃ₗ[K] V
  map_one : linear D.one = D.one
  map_product : ∀ x y, linear (D.product x y) =
    D.product (linear x) (linear y)

/-- Package a cubic-and-unit preserving linear equivalence as an actual
unital product automorphism.-/
def automorphismOfCubicUnit (g : V ≃ₗ[K] V)
    (hOne : g D.one = D.one)
    (hCubic : ∀ x, D.cubic (g x) = D.cubic x) : D.Aut where
  linear := g
  map_one := hOne
  map_product := D.map_product g hOne hCubic

end Data

/-! ## Compatibility with the established trace-dual recovery API -/

open AlbertLean.CubicNorm

/-- A literal cubic presentation of existing `RecoveryData`.  These laws say
that its polarization, trace, and trace form are the ones obtained from the
displayed cubic and the recovery-data unit.-/
structure RecoveryPresentation (D : RecoveryData K V) where
  cubic : V → K
  polar_formula : ∀ x y z,
    D.polar x y z = polar cubic x y z
  trace_formula : ∀ x,
    D.trace x = D.polar D.one D.one x / 2
  traceForm_formula : ∀ x y,
    D.traceForm x y = D.trace x * D.trace y - D.polar D.one x y

namespace RecoveryPresentation

variable {D : RecoveryData K V} (P : RecoveryPresentation D)

/-- Cubic preservation alone gives preservation of the recovery
polarization.
@isnad1 id=eq.1h8v.s12.9671c0795973 from=translated src=- shape=7ea01828 vocab=e28f6387
-/
theorem map_polar (g : V ≃ₗ[K] V)
    (hCubic : ∀ x, P.cubic (g x) = P.cubic x) (x y z : V) :
    D.polar (g x) (g y) (g z) = D.polar x y z := by
  rw [P.polar_formula, P.polar_formula]
  exact polar_map P.cubic g hCubic x y z

/-- Cubic and unit preservation give preservation of the recovery trace.
@isnad1 id=eq.2h6v.s9.0bfaba23e793 from=translated src=- shape=8b73834c vocab=d82ee0f0
-/
theorem map_trace (g : V ≃ₗ[K] V) (hOne : g D.one = D.one)
    (hCubic : ∀ x, P.cubic (g x) = P.cubic x) (x : V) :
    D.trace (g x) = D.trace x := by
  rw [P.trace_formula, P.trace_formula]
  have hp := P.map_polar g hCubic D.one D.one x
  rw [hOne] at hp
  exact congrArg (fun a => a / 2) hp

/-- Cubic and unit preservation give preservation of the recovery trace
pairing.
@isnad1 id=eq.2h7v.s10.b9f52545a89b from=translated src=- shape=e44fdd82 vocab=aba4dfcd
-/
theorem map_traceForm (g : V ≃ₗ[K] V) (hOne : g D.one = D.one)
    (hCubic : ∀ x, P.cubic (g x) = P.cubic x) (x y : V) :
    D.traceForm (g x) (g y) = D.traceForm x y := by
  rw [P.traceForm_formula, P.traceForm_formula,
    P.map_trace g hOne hCubic, P.map_trace g hOne hCubic]
  have hp := P.map_polar g hCubic D.one x y
  rw [hOne] at hp
  rw [hp]

/-- Adjoint preservation derived through the established nondegenerate
trace-dual recovery theorem.
@isnad1 id=eq.2h6v.s9.00dbb0f3185d from=translated src=- shape=73fcbf68 vocab=7ac16f6c
-/
theorem map_adjoint [FiniteDimensional K V]
    (g : V ≃ₗ[K] V) (hOne : g D.one = D.one)
    (hCubic : ∀ x, P.cubic (g x) = P.cubic x) (x : V) :
    g (D.adjoint x) = D.adjoint (g x) := by
  apply D.map_adjoint D g
  · exact P.map_traceForm g hOne hCubic
  · exact P.map_polar g hCubic

/-- Cross preservation derived from recovered-adjoint preservation.
@isnad1 id=eq.2h7v.s9.348c55214ad5 from=translated src=- shape=3ec6bad7 vocab=1fbd568f
-/
theorem map_cross [FiniteDimensional K V]
    (g : V ≃ₗ[K] V) (hOne : g D.one = D.one)
    (hCubic : ∀ x, P.cubic (g x) = P.cubic x) (x y : V) :
    g (D.cross x y) = D.cross (g x) (g y) := by
  apply D.map_cross D g
  · exact P.map_traceForm g hOne hCubic
  · exact P.map_polar g hCubic

/-- Compression over `RecoveryData`: preserving only the displayed cubic and
unit forces preservation of its canonical Springer product.
@isnad1 id=eq.2h7v.s9.d62d22331f05 from=translated src=- shape=3ec6bad7 vocab=98f0380a
-/
theorem map_product [FiniteDimensional K V]
    (g : V ≃ₗ[K] V) (hOne : g D.one = D.one)
    (hCubic : ∀ x, P.cubic (g x) = P.cubic x) (x y : V) :
    g (D.product x y) = D.product (g x) (g y) := by
  apply D.map_product D g hOne
  · exact P.map_trace g hOne hCubic
  · exact P.map_traceForm g hOne hCubic
  · exact P.map_polar g hCubic

/-- Unital automorphisms of the product canonically recovered by `D`.-/
structure Aut (D : RecoveryData K V) [FiniteDimensional K V] where
  linear : V ≃ₗ[K] V
  map_one : linear D.one = D.one
  map_product : ∀ x y, linear (D.product x y) =
    D.product (linear x) (linear y)

/-- Package cubic-and-unit preservation as an actual automorphism of the
recovered product.-/
def automorphismOfCubicUnit [FiniteDimensional K V]
    (g : V ≃ₗ[K] V) (hOne : g D.one = D.one)
    (hCubic : ∀ x, P.cubic (g x) = P.cubic x) : Aut D where
  linear := g
  map_one := hOne
  map_product := P.map_product g hOne hCubic

end RecoveryPresentation
end AlbertLean.Generic.CubicAutomorphism
