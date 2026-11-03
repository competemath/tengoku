/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Data.Complex.Basic
import Tengoku.Seed.LinearAlgebra.BilinearForm.Orthogonal
import Tengoku.Seed.LinearAlgebra.QuadraticForm.Real
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The complex functional of a pair in a quadratic space

An ordered pair `(x, y)` — later read as the real and imaginary parts of `Ω` — determines

```
Z (v) = ⟪x, v⟫ + i ⟪y, v⟫
```

This is `⟪Ω, -⟫` written without complexifying the space, since `⟪·,·⟫` is
the polar form.  The API below is ordinary linear algebra: it packages no
heart, semistable locus, support predicate, or wall arrangement.

The span, orthogonal complement, and exact kernel description are generic
quadratic algebra. Signature and positive-plane consequences live in
`ComplexPairingSignature.lean`; stability and wall interpretations live in
`StabilityCondition/CentralCharge/Quadratic.lean`.

## Main results

* `centralCharge_eq_zero_iff` — **the kernel of `Z` is the orthogonal complement
  of the plane.**
-/

open QuadraticMap Complex

namespace PeriodDomain

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}

section Pair

variable (Q)

/-- The subspace spanned by an ordered pair.-/
def pairSpan (x y : M) : Submodule ℝ M := Submodule.span ℝ ({x, y} : Set M)

/-- The orthogonal complement with respect to the polar pairing.-/
abbrev orthogonal (W : Submodule ℝ M) : Submodule ℝ M :=
  LinearMap.BilinForm.orthogonal Q.polarBilin W

end Pair

/-- Membership in the orthogonal complement, written using the polar form.
@isnad1 id=iff.0h4v.s7.e694af019e06 from=translated src=- shape=e6948226 vocab=ed4d674f
-/
theorem mem_orthogonal_iff {W : Submodule ℝ M} {u : M} :
    u ∈ orthogonal Q W ↔ ∀ w ∈ W, polar (⇑Q) w u = 0 := by
  simp [orthogonal, LinearMap.BilinForm.mem_orthogonal_iff]

/-- Orthogonality to a span of two vectors is orthogonality to both.
@isnad1 id=iff.0h5v.s7.647cac31cf19 from=translated src=- shape=bb81de64 vocab=93506ddd
-/
theorem mem_orthogonal_span_pair_iff {x y u : M} :
    u ∈ orthogonal Q (Submodule.span ℝ ({x, y} : Set M)) ↔
      polar (⇑Q) x u = 0 ∧ polar (⇑Q) y u = 0 := by
  rw [mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨h x (Submodule.subset_span (by simp)), h y (Submodule.subset_span (by simp))⟩
  · rintro ⟨hx, hy⟩ w hw
    have hle : Submodule.span ℝ ({x, y} : Set M) ≤ LinearMap.ker (Q.polarBilin.flip u) := by
      rw [Submodule.span_le]
      rintro z (rfl | rfl) <;> simp [LinearMap.mem_ker, hx, hy]
    simpa [LinearMap.mem_ker] using hle hw

section Defs

variable (Q)

/-- The **central charge** of an ordered pair: the pairing against `x` and `y`
read as the real and imaginary parts of a complex number.-/
def centralCharge (x y v : M) : ℂ :=
  Complex.ofReal (polar (⇑Q) x v) + Complex.ofReal (polar (⇑Q) y v) * Complex.I

end Defs

/--
@isnad1 id=eq.0h5v.s6.92abd6b77446 from=translated src=- shape=f888fecc vocab=e9b8547b
-/
@[simp]
theorem centralCharge_re (x y v : M) : (centralCharge Q x y v).re = polar (⇑Q) x v := by
  simp [centralCharge]

/--
@isnad1 id=eq.0h5v.s6.c27e9ed74637 from=translated src=- shape=fc80ea68 vocab=b79bfdad
-/
@[simp]
theorem centralCharge_im (x y v : M) : (centralCharge Q x y v).im = polar (⇑Q) y v := by
  simp [centralCharge]

/--
@isnad1 id=eq.0h6v.s6.518a516a7e7c from=translated src=- shape=7333d309 vocab=95c7f5c1
-/
theorem centralCharge_add (x y v w : M) :
    centralCharge Q x y (v + w) = centralCharge Q x y v + centralCharge Q x y w := by
  apply Complex.ext <;> simp [polar_add_right]

/--
@isnad1 id=eq.0h6v.s6.f43a89022d36 from=translated src=- shape=89be5a30 vocab=60245a42
-/
theorem centralCharge_smul (x y v : M) (a : ℝ) :
    centralCharge Q x y (a • v) = (a : ℂ) * centralCharge Q x y v := by
  apply Complex.ext <;> simp [polar_smul_right]

/--
@isnad1 id=eq.0h4v.s5.516cd3007800 from=translated src=- shape=2ff9ddc7 vocab=45cef302
-/
@[simp]
theorem centralCharge_zero (x y : M) : centralCharge Q x y 0 = 0 := by
  apply Complex.ext <;> simp

/-- **The kernel of the charge is the orthogonal complement of the plane.**
@isnad1 id=iff.0h5v.s6.67dd2fad7476 from=translated src=- shape=1ca689af vocab=0392bdae
-/
theorem centralCharge_eq_zero_iff {x y v : M} :
    centralCharge Q x y v = 0 ↔ v ∈ orthogonal Q (pairSpan x y) := by
  rw [pairSpan, mem_orthogonal_span_pair_iff, Complex.ext_iff]
  simp

/-- The charge kernel as a submodule: the orthogonal complement, named for what
it is in stability language.
@isnad1 id=eq.0h4v.s6.4da22592dd35 from=translated src=- shape=b98574b9 vocab=e8da669e
-/
theorem ker_centralCharge_eq (x y : M) :
    {v : M | centralCharge Q x y v = 0} = (orthogonal Q (pairSpan x y) : Set M) := by
  ext v
  exact centralCharge_eq_zero_iff

end PeriodDomain
