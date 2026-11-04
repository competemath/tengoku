import Tengoku.Seed.Algebra.MonoidAlgebra.Support
import Tengoku.Seed.Algebra.MonoidAlgebra.Basic
import Tengoku.Seed.Analysis.Convex.Hull
import Tengoku.Seed.Analysis.LocallyConvex.Separation
import Tengoku
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Adapted from the neighboring MathieuProperty/LaurentSupport.lean,
with namespace and imports adjusted; no dependency on that project.

The separating-functional part of the torus argument.
This proves the elementary implication after strict separation. It does not
assume or assert the missing Duistermaat--van der Kallen theorem.
-/

open scoped Pointwise

namespace DuistermaatVanDerKallen

abbrev MultiLaurent (d : ℕ) := AddMonoidAlgebra ℂ (Fin d → ℤ)

def constantTerm {d : ℕ} (f : MultiLaurent d) : ℂ := f.coeff 0

def exponentVector {d : ℕ} (a : Fin d → ℤ) : Fin d → ℝ := fun i => (a i : ℝ)

/-- The exact Newton convex hull, retaining complex coefficient cancellation.-/
def newtonPolytope {d : ℕ} (f : MultiLaurent d) : Set (Fin d → ℝ) :=
  convexHull ℝ (exponentVector '' (f.coeff.support : Set (Fin d → ℤ)))

section Support
variable {M : Type*} [AddCommMonoid M] (w : M →+ ℝ)

/--
@isnad1 id=le.3h7v.s8.2826aad29c35 from=translated src=- shape=f5840273 vocab=870fca19
-/
theorem support_mul_lower_bound (f g : AddMonoidAlgebra ℂ M) (a b : ℝ)
    (hf : ∀ x ∈ f.coeff.support, a ≤ w x)
    (hg : ∀ x ∈ g.coeff.support, b ≤ w x) :
    ∀ x ∈ (f * g).coeff.support, a + b ≤ w x := by
  classical
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_coeff_mul_subset f g hx)
  rw [map_add]
  exact add_le_add (hf y hy) (hg z hz)

/--
@isnad1 id=le.2h6v.s7.d9088b8a37f7 from=translated src=- shape=b3f713ee vocab=0e3b8b47
-/
theorem support_pow_lower_bound (f : AddMonoidAlgebra ℂ M) (δ : ℝ)
    (hf : ∀ x ∈ f.coeff.support, δ ≤ w x) (m : ℕ) :
    ∀ x ∈ (f ^ m).coeff.support, m * δ ≤ w x := by
  classical
  induction m with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by simpa using hx
    simp [hx0]
  | succ m ih =>
    simpa [pow_succ, Nat.cast_add, Nat.cast_one, add_mul] using
      support_mul_lower_bound w (f ^ m) f (m * δ) δ ih hf

/-- An explicit support lower bound is enough to force eventual constant-term
vanishing, including zero polynomials and arbitrary fixed multipliers.
@isnad1 id=ex.2h5v.s7.772f81cfabae from=translated src=- shape=ade8d816 vocab=e4d70373
-/
theorem eventual_constantTerm_zero_of_lower_bound (f h : AddMonoidAlgebra ℂ M)
    (δ : ℝ) (hδ : 0 < δ) (hf : ∀ x ∈ f.coeff.support, δ ≤ w x) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → (h * f ^ m).coeff 0 = 0 := by
  classical
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ h.coeff.support.image w, C ≤ x :=
    (h.coeff.support.image w).exists_le (α := ℝᵒᵈ)
  obtain ⟨N, hN⟩ := exists_nat_gt (-C / δ)
  refine ⟨N, fun m hm => ?_⟩
  by_contra hne
  have hbound := support_mul_lower_bound w h (f ^ m) C (m * δ)
    (fun x hx => hC _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    (support_pow_lower_bound w f δ hf m) 0 (Finsupp.mem_support_iff.mpr hne)
  have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
  have hN' : -C < N * δ := (div_lt_iff₀ hδ).mp hN
  simp only [map_zero] at hbound
  nlinarith

end Support

/-- Hahn--Banach supplies the support bound whenever the Newton hull avoids zero.
@isnad1 id=ex.1h2v.s7.0fc4bec039a7 from=translated src=- shape=c89bdfb1 vocab=6fb1ee0f
-/
theorem support_strict_separation {d : ℕ} (f : MultiLaurent d)
    (hf : (0 : Fin d → ℝ) ∉ newtonPolytope f) :
    ∃ w : (Fin d → ℤ) →+ ℝ, ∃ δ : ℝ, 0 < δ ∧
      ∀ a ∈ f.coeff.support, δ ≤ w a := by
  classical
  have hc : IsCompact (newtonPolytope f) :=
    (f.coeff.support.finite_toSet.image exponentVector).isCompact_convexHull ℝ
  obtain ⟨L, c, h0, hL⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ _) hc.isClosed hf
  let w : (Fin d → ℤ) →+ ℝ :=
    { toFun := fun a => L (exponentVector a)
      map_zero' := by
        change L (exponentVector (0 : Fin d → ℤ)) = 0
        have he : exponentVector (0 : Fin d → ℤ) = 0 := by
          ext i
          simp [exponentVector]
        rw [he, map_zero]
      map_add' := by
        intro a b
        have he : exponentVector (a + b) = exponentVector a + exponentVector b := by
          ext i
          simp [exponentVector]
        simp [he] }
  refine ⟨w, c, by simpa using h0, ?_⟩
  intro a ha
  exact (hL _ (subset_convexHull ℝ _ ⟨a, ha, rfl⟩)).le

/-- The full elementary conclusion in the torus proof, with precisely its
geometric premise. Obtaining this premise from zero moments remains unproved.
@isnad1 id=ex.1h3v.s7.da54a7ec1b96 from=translated src=- shape=a9450f3a vocab=8c141562
-/
theorem eventual_constantTerm_zero_of_newton {d : ℕ} (f h : MultiLaurent d)
    (hf : (0 : Fin d → ℝ) ∉ newtonPolytope f) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → constantTerm (h * f ^ m) = 0 := by
  obtain ⟨w, δ, hδ, hw⟩ := support_strict_separation f hf
  exact eventual_constantTerm_zero_of_lower_bound w f h δ hδ hw

end DuistermaatVanDerKallen
