import Tengoku.Seed.Analysis.InnerProductSpace.LinearMap
import Tengoku.Seed.Analysis.Convex.Topology
import Tengoku.Seed.Topology.Order.Compact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real support functions of compact sets

Attainment, norm bounds, Lipschitz continuity and invariance under convexification
for the ordinary support function, with no absolute value inside its supremum.
These deterministic facts underlie Gaussian width.
-/

noncomputable section
open Set
namespace NLAlib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real-valued support function of a set. It is the maximum of the linear
functional on a nonempty compact set. Empty or unbounded image sets have the
usual total real-supremum junk value.-/
def realSupportFunction (T : Set E) (z : E) : ℝ :=
  sSup ((fun x => inner ℝ z x) '' T)

/-- A compact nonempty set attains its support function at a deterministic point.
@isnad1 id=ex.2h3v.s6.57843fe96c34 from=translated src=- shape=8ded739d vocab=0cc25e15
-/
theorem exists_inner_eq_realSupportFunction {T : Set E} (hT : IsCompact T)
    (hne : T.Nonempty) (z : E) :
    ∃ x ∈ T, inner ℝ z x = realSupportFunction T z := by
  have hc : Continuous (fun x : E => inner ℝ z x) := by fun_prop
  obtain ⟨x, hx, hmax⟩ := hT.exists_isMaxOn hne hc.continuousOn
  refine ⟨x, hx, ?_⟩
  symm
  exact (show IsGreatest ((fun x => inner ℝ z x) '' T) (inner ℝ z x) from
    ⟨⟨x, hx, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hmax hy⟩).csSup_eq

/-- Every point of a compact set gives a lower bound for its support function.
@isnad1 id=le.2h4v.s6.a73b11ac9150 from=translated src=- shape=68944d8b vocab=0fde8a0d
-/
theorem inner_le_realSupportFunction {T : Set E} (hT : IsCompact T)
    {x : E} (hx : x ∈ T) (z : E) : inner ℝ z x ≤ realSupportFunction T z := by
  exact le_csSup ((hT.image (continuous_const.inner continuous_id)).bddAbove)
    ⟨x, hx, rfl⟩

/-- The support function is bounded by the Euclidean radius times the norm.
@isnad1 id=le.3h4v.s6.b836bbaca440 from=translated src=- shape=2729ea28 vocab=a72da021
-/
theorem abs_realSupportFunction_le {T : Set E} (hT : IsCompact T) (hne : T.Nonempty)
    {R : ℝ} (hR : ∀ x ∈ T, ‖x‖ ≤ R) (z : E) :
    |realSupportFunction T z| ≤ R * ‖z‖ := by
  obtain ⟨x, hx, he⟩ := exists_inner_eq_realSupportFunction hT hne z
  rw [← he]
  exact (abs_real_inner_le_norm z x).trans (by nlinarith [norm_nonneg z, hR x hx])

/-- A radius bound makes the support function Lipschitz, without selecting a
measurable maximizing point.
@isnad1 id=le.3h5v.s6.db06db0d0c9b from=translated src=- shape=056b02bd vocab=9390e80e
-/
theorem abs_realSupportFunction_sub_le {T : Set E} (hT : IsCompact T) (hne : T.Nonempty)
    {R : ℝ} (hR : ∀ x ∈ T, ‖x‖ ≤ R) (z w : E) :
    |realSupportFunction T z - realSupportFunction T w| ≤ R * ‖z - w‖ := by
  have hstep : ∀ z w : E, realSupportFunction T z - realSupportFunction T w ≤ R * ‖z-w‖ := by
    intro z w
    obtain ⟨x, hx, he⟩ := exists_inner_eq_realSupportFunction hT hne z
    have hl := inner_le_realSupportFunction hT hx w
    have hi := abs_real_inner_le_norm (z-w) x
    have hinner : inner ℝ (z-w) x = inner ℝ z x - inner ℝ w x := inner_sub_left _ _ _
    rw [he] at hinner
    have hb : ‖z-w‖ * ‖x‖ ≤ R * ‖z-w‖ := by nlinarith [norm_nonneg (z-w), hR x hx]
    linarith [le_abs_self (inner ℝ (z-w) x)]
  exact abs_sub_le_iff.mpr ⟨hstep z w, by simpa [norm_sub_rev] using hstep w z⟩

/-- The ordinary support function of a nonempty compact set is continuous.
@isnad1 id=continuo.2h2v.s5.f076ebadec22 from=translated src=- shape=7f3bcfce vocab=97148eb2
-/
theorem continuous_realSupportFunction {T : Set E} (hT : IsCompact T) (hne : T.Nonempty) :
    Continuous (realSupportFunction T) := by
  obtain ⟨R, hR, hbound⟩ := hT.isBounded.exists_pos_norm_le
  exact (LipschitzWith.of_dist_le_mul (K := ⟨R, hR.le⟩) (fun z w => by
    rw [Real.dist_eq, dist_eq_norm]
    change |realSupportFunction T z - realSupportFunction T w| ≤ R * ‖z-w‖
    exact abs_realSupportFunction_sub_le hT hne hbound z w)).continuous

/-- Translation adds exactly the corresponding linear functional to a support
function.
@isnad1 id=eq.2h4v.s6.4cf8367bd915 from=translated src=- shape=0bf384f7 vocab=55cf5129
-/
theorem realSupportFunction_image_add {T : Set E} (hT : IsCompact T) (hne : T.Nonempty)
    (a z : E) :
    realSupportFunction ((fun x => x + a) '' T) z = realSupportFunction T z + inner ℝ z a := by
  obtain ⟨x, hx, he⟩ := exists_inner_eq_realSupportFunction hT hne z
  have himg : IsCompact ((fun x : E => x + a) '' T) := hT.image (by fun_prop)
  obtain ⟨_, ⟨y, hy, rfl⟩, hf⟩ := exists_inner_eq_realSupportFunction himg (hne.image _) z
  have hxy := inner_le_realSupportFunction hT hy z
  have hyx := inner_le_realSupportFunction himg
    (mem_image_of_mem (fun x => x + a) hx) z
  rw [inner_add_right] at hf hyx
  linarith

/-- Taking the convex hull does not change a compact set's support function.
@isnad1 id=eq.2h3v.s6.980a5c4fed75 from=translated src=- shape=f442dddb vocab=6f17f694
-/
theorem realSupportFunction_convexHull {T : Set E} (hT : IsCompact T) (hne : T.Nonempty)
    (z : E) : realSupportFunction (convexHull ℝ T) z = realSupportFunction T z := by
  have hb : ∀ x ∈ convexHull ℝ T, inner ℝ z x ≤ realSupportFunction T z := by
    have hc : Convex ℝ {x : E | inner ℝ z x ≤ realSupportFunction T z} := by
      intro x hx y hy a b ha hb hab
      change inner ℝ z (a • x + b • y) ≤ realSupportFunction T z
      rw [inner_add_right, inner_smul_right, inner_smul_right]
      calc
        _ ≤ a * realSupportFunction T z + b * realSupportFunction T z :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
        _ = _ := by rw [← add_mul, hab, one_mul]
    exact convexHull_min (fun x hx => inner_le_realSupportFunction hT hx z) hc
  have hbound : BddAbove ((fun x => inner ℝ z x) '' convexHull ℝ T) :=
    ⟨realSupportFunction T z, by rintro _ ⟨x,hx,rfl⟩; exact hb x hx⟩
  obtain ⟨x,hx,he⟩ := exists_inner_eq_realSupportFunction hT hne z
  apply le_antisymm
  · exact csSup_le ((hne.mono (subset_convexHull ℝ T)).image _)
      (by rintro _ ⟨y,hy,rfl⟩; exact hb y hy)
  · rw [← he]
    exact le_csSup hbound ⟨x, subset_convexHull ℝ T hx, rfl⟩

/-- A singleton support function is its single linear functional.
@isnad1 id=eq.0h3v.s5.aa71b0d1d17d from=translated src=- shape=b0db6e3f vocab=db8ecef1
-/
@[simp] theorem realSupportFunction_singleton (x z : E) :
    realSupportFunction ({x} : Set E) z = inner ℝ z x := by
  simp [realSupportFunction]

/-- Support functions are monotone under inclusion of compact nonempty sets.
@isnad1 id=le.4h4v.s6.682bff88d4e4 from=translated src=- shape=27d0e9c8 vocab=b2aa4c0a
-/
theorem realSupportFunction_mono {S T : Set E} (hS : IsCompact S) (hne : S.Nonempty)
    (hT : IsCompact T) (hst : S ⊆ T) (z : E) :
    realSupportFunction S z ≤ realSupportFunction T z := by
  obtain ⟨x, hx, he⟩ := exists_inner_eq_realSupportFunction hS hne z
  rw [← he]
  exact inner_le_realSupportFunction hT (hst hx) z

/-- Isometric changes of coordinates move a support function by the inverse
isometry on its argument.
@isnad1 id=eq.0h4v.s8.c6f99394b6e2 from=translated src=- shape=a4171c00 vocab=8d1ff863
-/
theorem realSupportFunction_image_linearIsometryEquiv (T : Set E)
    (U : E ≃ₗᵢ[ℝ] E) (z : E) :
    realSupportFunction (U '' T) z = realSupportFunction T (U.symm z) := by
  unfold realSupportFunction
  congr 1
  have hi (x : E) : inner ℝ (U.symm z) x = inner ℝ z (U x) := by
    simpa only [U.apply_symm_apply] using (U.inner_map_map (U.symm z) x).symm
  ext r
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hr⟩
    refine ⟨x,hx,?_⟩
    exact (hi x).trans hr
  · rintro ⟨x,hx,hr⟩
    refine ⟨U x, ⟨x,hx,rfl⟩, ?_⟩
    exact (hi x).symm.trans hr

/-- Nonnegative scaling commutes with compact support functions, including the
zero scalar.
@isnad1 id=eq.3h4v.s7.7b039e14191d from=translated src=- shape=30cdf776 vocab=62b93aa8
-/
theorem realSupportFunction_image_smul {T : Set E} (hT : IsCompact T) (hne : T.Nonempty)
    {c : ℝ} (hc : 0 ≤ c) (z : E) :
    realSupportFunction ((fun x => c • x) '' T) z = c * realSupportFunction T z := by
  have himg : IsCompact ((fun x : E => c • x) '' T) := hT.image (by fun_prop)
  obtain ⟨x,hx,he⟩ := exists_inner_eq_realSupportFunction hT hne z
  obtain ⟨_,⟨y,hy,rfl⟩,hf⟩ := exists_inner_eq_realSupportFunction himg (hne.image _) z
  have hxy := mul_le_mul_of_nonneg_left (inner_le_realSupportFunction hT hy z) hc
  have hyx := inner_le_realSupportFunction himg (mem_image_of_mem (fun x => c • x) hx) z
  rw [inner_smul_right] at hf hyx
  rw [he] at hyx
  exact le_antisymm (by linarith) hyx

/-- Closing the convex hull does not change a compact set's finite support
function. This uses a closed half-space, not a measurable optimizer.
@isnad1 id=eq.2h3v.s7.6bcd32d20cf7 from=translated src=- shape=02fc52ab vocab=a68f8c9f
-/
theorem realSupportFunction_closure_convexHull {T : Set E} (hT : IsCompact T)
    (hne : T.Nonempty) (z : E) :
    realSupportFunction (closure (convexHull ℝ T)) z = realSupportFunction T z := by
  have hbase : ∀ x ∈ convexHull ℝ T, inner ℝ z x ≤ realSupportFunction T z := by
    have hc : Convex ℝ {x : E | inner ℝ z x ≤ realSupportFunction T z} := by
      intro x hx y hy a b ha hb hab
      change inner ℝ z (a • x + b • y) ≤ realSupportFunction T z
      rw [inner_add_right, inner_smul_right, inner_smul_right]
      calc
        _ ≤ a * realSupportFunction T z + b * realSupportFunction T z :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
        _ = _ := by rw [← add_mul, hab, one_mul]
    exact convexHull_min (fun x hx => inner_le_realSupportFunction hT hx z) hc
  have hclosed : IsClosed {x : E | inner ℝ z x ≤ realSupportFunction T z} :=
    isClosed_le (by fun_prop) continuous_const
  have hb : ∀ x ∈ closure (convexHull ℝ T), inner ℝ z x ≤ realSupportFunction T z :=
    closure_minimal hbase hclosed
  have hbound : BddAbove ((fun x => inner ℝ z x) '' closure (convexHull ℝ T)) :=
    ⟨realSupportFunction T z, by rintro _ ⟨x,hx,rfl⟩; exact hb x hx⟩
  obtain ⟨x,hx,he⟩ := exists_inner_eq_realSupportFunction hT hne z
  have hsubset : T ⊆ closure (convexHull ℝ T) := (subset_convexHull ℝ T).trans subset_closure
  apply le_antisymm
  · exact csSup_le ((hne.mono hsubset).image _)
      (by rintro _ ⟨y,hy,rfl⟩; exact hb y hy)
  · rw [← he]
    exact le_csSup hbound ⟨x,hsubset hx,rfl⟩

end NLAlib
