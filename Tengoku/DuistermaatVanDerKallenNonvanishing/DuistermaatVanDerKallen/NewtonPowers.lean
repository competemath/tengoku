import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.Targets
import Tengoku.Seed.Analysis.Convex.KreinMilman

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Newton-polytope homogeneity by exposed vertices and coefficient survival.
The finite hull is recovered from its extreme points using mathlib's
Krein–Milman theorem and compactness of the finite vertex hull. -/

open Set
open scoped Pointwise
namespace DuistermaatVanDerKallen

/-- A uniquely minimizing support exponent survives in every power.
@isnad1 id=eq.3h5v.s8.46155a828e74 from=translated src=- shape=0d86e933 vocab=78716d10
-/
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

/--
@isnad1 id=eq.0h3v.s6.3bd5c78ab8ff from=translated src=- shape=6c7d02ab vocab=8b0160ef
-/
theorem exponentVector_add {d : ℕ} (a b : Fin d → ℤ) :
    exponentVector (a + b) = exponentVector a + exponentVector b := by
  ext i
  simp [exponentVector]

/--
@isnad1 id=eq.0h3v.s6.684fac42c786 from=translated src=- shape=a41961a6 vocab=3a67514c
-/
theorem exponentVector_nsmul {d : ℕ} (n : ℕ) (a : Fin d → ℤ) :
    exponentVector (n • a) = (n : ℝ) • exponentVector a := by
  ext i
  simp [exponentVector]

/--
@isnad1 id=le.0h3v.s6.d90feed84228 from=translated src=- shape=949fc64b vocab=ea971f38
-/
theorem newtonPolytope_mul_subset {d : ℕ} (f g : MultiLaurent d) :
    newtonPolytope (f * g) ⊆ newtonPolytope f + newtonPolytope g := by
  apply convexHull_min _ ((convex_convexHull ℝ _).add (convex_convexHull ℝ _))
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_coeff_mul_subset f g ha)
  exact ⟨exponentVector b, subset_convexHull ℝ _ ⟨b, hb, rfl⟩,
    exponentVector c, subset_convexHull ℝ _ ⟨c, hc, rfl⟩, (exponentVector_add b c).symm⟩

/--
@isnad1 id=le.1h3v.s6.2f69939a5ae6 from=translated src=- shape=5b049cee vocab=f3819191
-/
theorem newtonPolytope_pow_subset {d : ℕ} (f : MultiLaurent d) {n : ℕ} (hn : 1 ≤ n) :
    newtonPolytope (f ^ n) ⊆ (n : ℝ) • newtonPolytope f := by
  have hconv : Convex ℝ (newtonPolytope f) := convex_convexHull ℝ _
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one,
      hconv.add_smul (Nat.cast_nonneg n) zero_le_one, one_smul]
    exact (newtonPolytope_mul_subset (f ^ n) f).trans (add_subset_add ih Subset.rfl)

/-- Every vertex of a finite convex hull is exposed by a strict minimum.
@isnad1 id=ex.2h3v.s9.e06a00f0dcaa from=translated src=- shape=afbe2aff vocab=ecb538e8
-/
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

/-- An extreme point of the Laurent Newton polytope survives under scaling.
@isnad1 id=mem.1h4v.s7.6023de6dae57 from=translated src=- shape=de797902 vocab=99ce6f1a
-/
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

/-- Newton polytopes of positive powers are exactly homothetic copies.
@isnad1 id=eq.1h3v.s6.8cd1dda240b7 from=translated src=- shape=cbca7770 vocab=f3819191
-/
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

/-- The previously isolated Newton-power origin-preservation obligation.
@isnad1 id=originin.0h0v.s0.a2f0dc63e3f1 from=translated src=- shape=45709ebd vocab=a2f0dc63
-/
theorem origin_in_newton_powers : OriginInNewtonPowers := by
  intro d f _ hf n hn
  rw [newtonPolytope_pow f hn]
  exact ⟨0, hf, smul_zero _⟩

/-- Infinite nonvanishing now requires only the still-open minimal theorem.
@isnad1 id=infinite.1h0v.s1.f264a2921953 from=translated src=- shape=1d48f1ac vocab=b1307d40
-/
theorem infinite_of_minimal (hminimal : MinimalNonvanishing) : InfiniteNonvanishing :=
  infinite_of_minimal_and_newton_powers hminimal origin_in_newton_powers

end DuistermaatVanDerKallen
