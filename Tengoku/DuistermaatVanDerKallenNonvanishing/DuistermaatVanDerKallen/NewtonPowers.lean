import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.Targets
import Tengoku.Seed.Analysis.Convex.KreinMilman

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Newton-polytope homogeneity by exposed vertices and coefficient survival.
The finite hull is recovered from its extreme points using mathlib's
Krein–Milman theorem and compactness of the finite vertex hull. -/

open Set
open scoped Pointwise
namespace DuistermaatVanDerKallen

/-- A uniquely minimizing support exponent survives in every power.-/
theorem coeff_pow_unique_min {M : Type*} [AddCommGroup M]
    (w : M →+ ℝ) (f : AddMonoidAlgebra ℂ M) (v : M)
    (hv : v ∈ f.coeff.support)
    (hw : ∀ a ∈ f.coeff.support, w v ≤ w a)
    (hu : ∀ a ∈ f.coeff.support, w a = w v → a = v) (n : ℕ) :
    (f ^ n).coeff (n • v) = f.coeff v ^ n := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, AddMonoidAlgebra.coeff_mul_apply_right, Finsupp.sum]
    rw [Finset.sum_eq_single v]
    · rw [succ_nsmul, add_neg_cancel_right, ih, pow_succ]
    · intro a ha hav
      have hlt : w v < w a := lt_of_le_of_ne (hw a ha) (fun he => hav (hu a ha he.symm))
      have hz : (f ^ n).coeff ((n + 1) • v + -a) = 0 := by
        by_contra hne
        have hb := support_pow_lower_bound w f (w v) hw n _ (Finsupp.mem_support_iff.mpr hne)
        simp only [map_add, map_nsmul, map_neg, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hb
        nlinarith
      rw [hz, zero_mul]
    · exact fun hnot => (hnot hv).elim

theorem exponentVector_add {d : ℕ} (a b : Fin d → ℤ) :
    exponentVector (a + b) = exponentVector a + exponentVector b := by
  ext i
  simp [exponentVector]

theorem exponentVector_nsmul {d : ℕ} (n : ℕ) (a : Fin d → ℤ) :
    exponentVector (n • a) = (n : ℝ) • exponentVector a := by
  ext i
  simp [exponentVector]

theorem newtonPolytope_mul_subset {d : ℕ} (f g : MultiLaurent d) :
    newtonPolytope (f * g) ⊆ newtonPolytope f + newtonPolytope g := by
  apply convexHull_min _ ((convex_convexHull ℝ _).add (convex_convexHull ℝ _))
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_coeff_mul_subset f g ha)
  exact ⟨exponentVector b, subset_convexHull ℝ _ ⟨b, hb, rfl⟩,
    exponentVector c, subset_convexHull ℝ _ ⟨c, hc, rfl⟩, (exponentVector_add b c).symm⟩

theorem newtonPolytope_pow_subset {d : ℕ} (f : MultiLaurent d) {n : ℕ} (hn : 1 ≤ n) :
    newtonPolytope (f ^ n) ⊆ (n : ℝ) • newtonPolytope f := by
  have hconv : Convex ℝ (newtonPolytope f) := convex_convexHull ℝ _
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one,
      hconv.add_smul (Nat.cast_nonneg n) zero_le_one, one_smul]
    exact (newtonPolytope_mul_subset (f ^ n) f).trans (add_subset_add ih Subset.rfl)

/-- Every vertex of a finite convex hull is exposed by a strict minimum.-/
theorem finite_extremePoint_exposed {d : ℕ} {S : Set (Fin d → ℝ)} (hS : S.Finite)
    {x : Fin d → ℝ} (hx : x ∈ (convexHull ℝ S).extremePoints ℝ) :
    ∃ L : (Fin d → ℝ) →L[ℝ] ℝ, ∀ y ∈ S, L x ≤ L y ∧ (L y = L x → y = x) := by
  have hc := ((convex_convexHull ℝ S).mem_extremePoints_iff_convex_sdiff.mp hx).2
  have hsub : convexHull ℝ (S \ {x}) ⊆ convexHull ℝ S \ {x} :=
    convexHull_min (fun y hy => ⟨subset_convexHull ℝ S hy.1, hy.2⟩) hc
  have hnot : x ∉ convexHull ℝ (S \ {x}) := fun h => (hsub h).2 rfl
  obtain ⟨L, r, hxr, hr⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
    ((hS.sdiff (t := {x})).isCompact_convexHull ℝ).isClosed hnot
  refine ⟨L, ?_⟩
  intro y hy
  by_cases he : y = x
  · exact ⟨he ▸ le_rfl, fun _ => he⟩
  have hlt := hxr.trans (hr y (subset_convexHull ℝ _ ⟨hy, he⟩))
  exact ⟨hlt.le, fun h => (hlt.ne h.symm).elim⟩

/-- An extreme point of the Laurent Newton polytope survives under scaling.-/
theorem extremePoint_pow_mem {d : ℕ} (f : MultiLaurent d) (n : ℕ)
    {x : Fin d → ℝ} (hx : x ∈ (newtonPolytope f).extremePoints ℝ) :
    (n : ℝ) • x ∈ newtonPolytope (f ^ n) := by
  classical
  let S : Set (Fin d → ℝ) := exponentVector '' (f.coeff.support : Set (Fin d → ℤ))
  have hS : S.Finite := f.coeff.support.finite_toSet.image exponentVector
  obtain ⟨L, hL⟩ := finite_extremePoint_exposed hS hx
  obtain ⟨v, hv, rfl⟩ := extremePoints_convexHull_subset hx
  let w : (Fin d → ℤ) →+ ℝ :=
    { toFun a := L (exponentVector a)
      map_zero' := by
        have hz : exponentVector (0 : Fin d → ℤ) = 0 := by ext i; simp [exponentVector]
        rw [hz, map_zero]
      map_add' a b := by rw [exponentVector_add, map_add] }
  have hw : ∀ a ∈ f.coeff.support, w v ≤ w a := fun a ha => (hL _ ⟨a, ha, rfl⟩).1
  have hu : ∀ a ∈ f.coeff.support, w a = w v → a = v := by
    intro a ha he
    have he' := (hL _ ⟨a, ha, rfl⟩).2 he
    funext i
    have hi : (a i : ℝ) = (v i : ℝ) := congr_fun he' i
    exact_mod_cast hi
  have hcoeff := coeff_pow_unique_min w f v hv hw hu n
  rw [← exponentVector_nsmul]
  exact subset_convexHull ℝ _ ⟨n • v, Finsupp.mem_support_iff.mpr
    (hcoeff ▸ pow_ne_zero n (Finsupp.mem_support_iff.mp hv)), rfl⟩

/-- Newton polytopes of positive powers are exactly homothetic copies.-/
theorem newtonPolytope_pow {d : ℕ} (f : MultiLaurent d) {n : ℕ} (hn : 1 ≤ n) :
    newtonPolytope (f ^ n) = (n : ℝ) • newtonPolytope f := by
  apply Subset.antisymm (newtonPolytope_pow_subset f hn)
  have hS : (exponentVector '' (f.coeff.support : Set (Fin d → ℤ))).Finite :=
    f.coeff.support.finite_toSet.image exponentVector
  have hV : ((newtonPolytope f).extremePoints ℝ).Finite :=
    hS.subset extremePoints_convexHull_subset
  have hconv : Convex ℝ (newtonPolytope f) := convex_convexHull ℝ _
  have hHull : convexHull ℝ ((newtonPolytope f).extremePoints ℝ) = newtonPolytope f := by
    have he := closure_convexHull_extremePoints (hS.isCompact_convexHull ℝ) hconv
    exact (hV.isCompact_convexHull ℝ).isClosed.closure_eq.symm.trans he
  calc
    (n : ℝ) • newtonPolytope f = (n : ℝ) • convexHull ℝ ((newtonPolytope f).extremePoints ℝ) :=
      congrArg ((n : ℝ) • ·) hHull.symm
    _ = convexHull ℝ ((n : ℝ) • (newtonPolytope f).extremePoints ℝ) := (convexHull_smul _ _).symm
    _ ⊆ newtonPolytope (f ^ n) := by
      apply convexHull_min _ (convex_convexHull ℝ _)
      rintro _ ⟨x, hx, rfl⟩
      exact extremePoint_pow_mem f n hx

/-- The previously isolated Newton-power origin-preservation obligation.-/
theorem origin_in_newton_powers : OriginInNewtonPowers := by
  intro d f _ hf n hn
  rw [newtonPolytope_pow f hn]
  exact ⟨0, hf, smul_zero _⟩

/-- Infinite nonvanishing now requires only the still-open minimal theorem.-/
theorem infinite_of_minimal (hminimal : MinimalNonvanishing) : InfiniteNonvanishing :=
  infinite_of_minimal_and_newton_powers hminimal origin_in_newton_powers

end DuistermaatVanDerKallen
