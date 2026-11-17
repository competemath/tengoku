/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.GroupTheory.Coxeter.GeometricRepresentation
import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The geometric construction with explicit admissible root choices

## Main definitions / results
`RootChoice` exposes exactly the choices hidden in `CoxeterMatrix.geomRoot`.
`reflection` and `representation` use the existing form/reflection/lift formulas.
`opaque_reflection` identifies the old construction as a specialization.

## References
Reconstructed by parameterizing the existing GeometricRepresentation.lean proofs.
No faithfulness assertion is made for the opaque specialization.
-/

namespace GeometricParametric

/-- A root of order `2m` for every positive `m`, and the conventional value at zero.-/
structure RootChoice (K : Type*) [Field K] where
  root : ℕ → K
  root_zero : root 0 = 1
  order_root : ∀ {m : ℕ}, 0 < m → orderOf (root m) = 2 * m

variable {K : Type*} [Field K] (r : RootChoice K)

/-- Admissibility is exactly primitivity of the chosen roots, for every positive exponent.
@isnad1 id=isprimit.1h3v.s5.13cfd1d157d1 from=translated src=- shape=3247ca89 vocab=892709e6
-/
theorem root_primitive {m : ℕ} (hm : 0 < m) :
    IsPrimitiveRoot (r.root m) (2 * m) :=
  IsPrimitiveRoot.iff_orderOf.mpr (r.order_root hm)

/-- Every chosen root satisfies its defining power relation.
@isnad1 id=eq.0h3v.s6.3d406a52d9da from=translated src=- shape=0bc6d95a vocab=e4643981
-/
theorem root_pow (m : ℕ) : r.root m ^ (2 * m) = 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [← r.order_root hm]
    exact pow_orderOf_eq_one _

/-- Admissible roots are nonzero.
@isnad1 id=ne.0h3v.s5.7df4c1ddceec from=translated src=- shape=ba76d645 vocab=bc5eb07e
-/
theorem root_ne_zero (m : ℕ) : r.root m ≠ 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [r.root_zero]; exact one_ne_zero
  · intro h
    have hp := root_pow r m
    rw [h, zero_pow (by omega)] at hp
    exact zero_ne_one hp

/-- Roots for off-diagonal finite exponents do not square to one.
@isnad1 id=ne.1h3v.s6.37565e67606e from=translated src=- shape=1b6992b8 vocab=2844af6b
-/
theorem root_sq_ne_one {m : ℕ} (hm : 1 < m) : r.root m ^ 2 ≠ 1 := by
  intro h
  have hd := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one h)
  rw [r.order_root (by omega)] at hd
  omega

/-- The existing half-sum convention, now with an explicit root parameter.-/
noncomputable def coeff (m : ℕ) : K :=
  if m = 0 then 1 else (r.root m + (r.root m)⁻¹) / 2

variable [CharZero K]

/-- Reflection coefficients are inverse sums, not half-sums.
@isnad1 id=eq.1h3v.s6.7e731b2ba886 from=translated src=- shape=01d435eb vocab=dcaf2b93
-/
theorem two_mul_coeff {m : ℕ} (hm : m ≠ 0) :
    2 * coeff r m = r.root m + (r.root m)⁻¹ := by
  simp only [coeff, hm, ↓reduceIte]
  ring

/-- The diagonal coefficient follows from exact order two.
@isnad1 id=eq.0h2v.s6.2b641019fe53 from=translated src=- shape=651cdaca vocab=9980563a
-/
theorem coeff_one : coeff r 1 = -1 := by
  have h1 : r.root 1 ^ 2 = 1 := by simpa using root_pow r 1
  have h2 : r.root 1 ≠ 1 := by
    intro h
    have ho := r.order_root one_pos
    rw [h, orderOf_one] at ho
    omega
  have h3 : r.root 1 = -1 := by
    have he : (r.root 1 - 1) * (r.root 1 + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp he with h | h
    · exact absurd (sub_eq_zero.mp h) h2
    · exact eq_neg_of_add_eq_zero_left h
  simp only [coeff, one_ne_zero, ↓reduceIte, h3]
  norm_num

variable {B : Type*} (M : CoxeterMatrix B)

/-- The original geometric form with a parameterized coefficient.-/
noncomputable def form (i : B) : (B →₀ K) →ₗ[K] K :=
  Finsupp.linearCombination K fun j ↦ -coeff r (M i j)

/-- The actual original reflection formula, not a matrix-defined surrogate.-/
noncomputable def reflection (i : B) : Module.End K (B →₀ K) :=
  LinearMap.id - (form r M i).smulRight (Finsupp.single i 2)

omit [CharZero K] in
/-- Evaluation of the parameterized form on a basis vector.
@isnad1 id=eq.0h7v.s8.8cf8ec449a37 from=translated src=- shape=05ff0847 vocab=a85e8e6c
-/
theorem form_single (i j : B) (a : K) :
    form r M i (Finsupp.single j a) = a * -coeff r (M i j) := by
  simp [form, Finsupp.linearCombination_single]

/-- The form has diagonal value one.
@isnad1 id=eq.0h6v.s8.d27cb9d25899 from=translated src=- shape=51a4d2cb vocab=bb0578a4
-/
theorem form_single_self (i : B) (a : K) :
    form r M i (Finsupp.single i a) = a := by
  rw [form_single, M.diagonal, coeff_one r]
  ring

omit [CharZero K] in
/-- The defining reflection formula.
@isnad1 id=eq.0h6v.s9.6d0432f7b862 from=translated src=- shape=c84ffa91 vocab=527dd585
-/
theorem reflection_apply (i : B) (v : B →₀ K) :
    reflection r M i v = v - form r M i v • Finsupp.single i 2 := rfl

omit [CharZero K] in
/-- Basis action, with the original factor of two.
@isnad1 id=eq.0h6v.s9.543639798eb9 from=translated src=- shape=c2710a80 vocab=27193bcf
-/
theorem reflection_single (i j : B) :
    reflection r M i (Finsupp.single j 1) =
      Finsupp.single j 1 + (2 * coeff r (M i j)) • Finsupp.single i 1 := by
  rw [reflection_apply, form_single, ← Finsupp.smul_single_one i (2 : K)]
  module

/-- Each parameterized reflection is an involution.
@isnad1 id=eq.0h5v.s9.a2b70725c7d5 from=translated src=- shape=69c3d1fb vocab=1b140f04
-/
theorem reflection_mul_self (i : B) : reflection r M i * reflection r M i = 1 := by
  refine LinearMap.ext fun v ↦ ?_
  have h : form r M i (reflection r M i v) = -form r M i v := by
    rw [reflection_apply, map_sub, map_smul, form_single_self, smul_eq_mul]
    ring
  rw [Module.End.mul_apply, Module.End.one_apply,
    reflection_apply r M i (reflection r M i v), h, reflection_apply]
  module

omit [CharZero K] in
/-- The formula in the exact shape required by the existing dihedral theorem.
@isnad1 id=eq.0h6v.s9.984300f73267 from=translated src=- shape=e70b5035 vocab=1d69f593
-/
theorem reflection_apply' (i : B) (v : B →₀ K) :
    reflection r M i v = v - (2 * form r M i v) • Finsupp.single i 1 := by
  rw [reflection_apply, ← Finsupp.smul_single_one i (2 : K), smul_smul, mul_comm]

/-- All admissible choices satisfy all the Coxeter relations.
@isnad1 id=isliftab.0h4v.s7.14789908c799 from=translated src=- shape=32ee02b6 vocab=251d985d
-/
theorem reflection_liftable : M.IsLiftable (reflection r M) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [M.diagonal, pow_one, reflection_mul_self]
  by_cases hm0 : M i j = 0
  · rw [hm0, pow_zero]
  have hm : 1 < M i j := by have := M.off_diagonal i j hij; omega
  exact Module.End.mul_pow_eq_one_of_reflections (reflection_apply' r M i)
    (reflection_apply' r M j) (form_single_self r M i 1)
    (by rw [form_single, one_mul])
    (by rw [form_single, one_mul, M.symmetric j i])
    (form_single_self r M j 1) (root_ne_zero r _) (two_mul_coeff r hm0)
    (root_sq_ne_one r hm) (root_pow r _)

/-- The geometric representation for an arbitrary admissible choice, via the same lift.-/
noncomputable def representation {W : Type*} [Group W] (cs : CoxeterSystem M W) :
    W →* Module.End K (B →₀ K) :=
  cs.lift ⟨reflection r M, reflection_liftable r M⟩

/-- The representation really maps the simple generators to the chosen-root reflections.
@isnad1 id=eq.0h7v.s9.1534eb69d464 from=translated src=- shape=eb86ff5c vocab=422f7487
-/
theorem representation_simple {W : Type*} [Group W] (cs : CoxeterSystem M W) (i : B) :
    representation r M cs (cs.simple i) = reflection r M i :=
  cs.lift_apply_simple _ i

/-- The existing opaque root choice is admissible.-/
noncomputable def opaqueChoice (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    RootChoice K where
  root := CoxeterMatrix.geomRoot K
  root_zero := by simp [CoxeterMatrix.geomRoot]
  order_root := CoxeterMatrix.orderOf_geomRoot K

/-- Specializing recovers exactly the existing reflection formula.
@isnad1 id=eq.0h4v.s6.8e3d383decde from=translated src=- shape=a80b7ce7 vocab=6b012463
-/
theorem opaque_reflection [IsAlgClosed K] (i : B) :
    reflection (opaqueChoice K) M i = M.geomReflection K i := rfl

/-- Specializing recovers the existing representation, not just its coefficients.
@isnad1 id=eq.0h5v.s8.62a16a75cf41 from=translated src=- shape=dcb2f93f vocab=9c268f68
-/
theorem opaque_representation [IsAlgClosed K] {W : Type*} [Group W]
    (cs : CoxeterSystem M W) :
    representation (opaqueChoice K) M cs = cs.geometricRepresentation K := rfl

end GeometricParametric
