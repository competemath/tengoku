import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyQuadraticDirectScaleEnergy
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyQuadraticResidueArithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite scale and residue tails for the direct quadratic action

This is the finite bookkeeping layer between the genuine direct action and
the seven separated annular tail families.  The ambient family `S` remains
fixed in every definition; only `A` is filtered as an output family.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectScaleTails

open KrauseLaceyQuadraticDirectPartition
open KrauseLaceyQuadraticDirectAction
open KrauseLaceyQuadraticDirectScaleEnergy
open KrauseLaceyQuadraticResidueArithmetic
open KrauseLaceyQuadraticAnnularTail
open KrauseLaceyQuadraticSmoothProjection

set_option autoImplicit false

noncomputable section

local instance : DecidableEq RealInterval := Classical.decEq _

/-- The literal output of one fixed integer scale.  Its smallest-region
input is still formed from `S`, not from the output subcollection.-/
def directScaleOutput
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (k s : ℤ) (x : ℝ) : ℂ :=
  ∑ I ∈ A.filter (fun I ↦ scale I = k),
    krauseLaceyLocalizedPiece 1 (scale I) I
      (offsetGroupedInput S scale f I s) x

/-- The fixed-scale output after imposing a length threshold.-/
def directScaleOutputAtThreshold
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell k s : ℤ) (x : ℝ) : ℂ :=
  ∑ I ∈ (A.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length)).filter
      (fun I ↦ scale I = k),
    krauseLaceyLocalizedPiece 1 (scale I) I
      (offsetGroupedInput S scale f I s) x

/-- The sequence in a single residue class to which the finite annular-tail
maximal theorem applies.-/
def directResidueOutput
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (r : Fin 7) (s : ℤ) : ℕ → ℝ → ℂ :=
  fun n ↦ directScaleOutput S A scale f (residueScale r n) s

/-- A scale absent from the retained output family has identically zero
fixed-scale output.
@isnad1 id=eq.1h6v.s6.23ac98e12dd2 from=translated src=- shape=664d7275 vocab=f2cb0ca4
-/
theorem directScaleOutput_eq_zero_of_not_mem_image
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (k s : ℤ) (hk : k ∉ A.image scale) :
    directScaleOutput S A scale f k s = 0 := by
  funext x
  unfold directScaleOutput
  apply Finset.sum_eq_zero
  intro I hI
  exact (hk (Finset.mem_image.mpr ⟨I, (Finset.mem_filter.mp hI).1,
    (Finset.mem_filter.mp hI).2⟩)).elim

/-- Under the finite nonnegative scale range hypothesis, the fixed-scale
outputs are supported on the literal range `0, ..., N - 1`.
@isnad1 id=eq.3h7v.s6.93c33ba57311 from=translated src=- shape=909d9c58 vocab=de372f2b
-/
theorem directScaleOutput_eq_zero_of_outside_range
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (N : ℕ) (s k : ℤ)
    (hnonneg : ∀ I ∈ A, 0 ≤ scale I)
    (hbound : ∀ I ∈ A, scale I < N) (hk : k < 0 ∨ N ≤ k) :
    directScaleOutput S A scale f k s = 0 := by
  apply directScaleOutput_eq_zero_of_not_mem_image
  intro hkimage
  obtain ⟨I, hI, hIk⟩ := Finset.mem_image.mp hkimage
  rcases hk with hk | hk
  · have hI0 := hnonneg I hI
    omega
  · have hIN := hbound I hI
    omega

/-- The concrete scale output is the a.e. representative of the genuine
`L²` fixed-scale sum from the direct energy module.
@isnad1 id=eventual.0h6v.s8.71382549941f from=translated src=- shape=468f7a67 vocab=0ad628d5
-/
theorem offsetOutputScaleLp_ae_eq_directScaleOutput
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : L0Infinity)
    (k s : ℤ) :
    offsetOutputScaleLp S A scale f k s =ᵐ[volume]
      directScaleOutput S A scale f k s := by
  exact offsetOutputScaleLp_ae_eq S A scale f k s

/-- Exact finite recombination of a thresholded direct action by its actual
output scales.  This needs no scale geometry: it is a finite fiberwise sum.
@isnad1 id=eq.0h7v.s6.7fc3f951ceb9 from=translated src=- shape=3b0eb356 vocab=589c889d
-/
theorem offsetLocalizedActionOn_eq_sum_scaleOutputs
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell s : ℤ) (x : ℝ) :
    offsetLocalizedActionOn S A scale f ell s x =
      ∑ k ∈ (A.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length)).image scale,
        directScaleOutputAtThreshold S A scale f ell k s x := by
  classical
  let T := A.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length)
  let g : RealInterval → ℂ := fun I ↦
    krauseLaceyLocalizedPiece 1 (scale I) I
      (offsetGroupedInput S scale f I s) x
  have hmaps : (↑T : Set RealInterval).MapsTo scale (↑(T.image scale) : Set ℤ) := by
    intro I hI
    exact Finset.mem_image.mpr ⟨I, hI, rfl⟩
  change (∑ I ∈ T, g I) = ∑ k ∈ T.image scale,
    ∑ I ∈ T.filter (fun I ↦ scale I = k), g I
  symm
  exact Finset.sum_fiberwise_of_maps_to hmaps _

/-- The seven residue-class pieces are exactly the concrete fixed-scale
outputs, evaluated along `r + 7n`.
@isnad1 id=eq.0h7v.s5.5458da154720 from=translated src=- shape=51a2d66c vocab=8216da24
-/
theorem directResidueOutput_apply
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (r : Fin 7) (s : ℤ) (n : ℕ) :
    directResidueOutput S A scale f r s n =
      directScaleOutput S A scale f (residueScale r n) s := rfl

/-- Every lower-scale cutoff inside one residue class is bounded by its
finite annular tail maximum.
@isnad1 id=le.0h9v.s6.7dd3b7c37730 from=translated src=- shape=9b823fa2 vocab=b1a4e117
-/
theorem enorm_directResidue_cutoff_le_tailMax
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (r : Fin 7) (q N : ℕ) (s : ℤ) (x : ℝ) :
    ‖∑ n ∈ (Finset.range N).filter
        (fun n ↦ (q : ℤ) ≤ residueScale r n),
        directResidueOutput S A scale f r s n x‖ₑ ≤
      finitePieceTailMax N (directResidueOutput S A scale f r s) x := by
  exact enorm_sum_filter_residueScale_ge_le_tailMax
    (directResidueOutput S A scale f r s) r q N x

/-- Quotient and remainder by seven give the exact finite bijection between
nonnegative scales below `N` and the valid residue-scale pairs.
@isnad1 id=eq.0h4v.s8.05f08ef75cc5 from=translated src=- shape=0fdfd759 vocab=0d0d4526
-/
theorem sum_range_filter_eq_sum_residuePairs
    {E : Type*} [AddCommMonoid E] (u : ℤ → E) (N q : ℕ) :
    (∑ k ∈ (Finset.range N).filter (fun k ↦ q ≤ k), u (k : ℤ)) =
      ∑ p ∈ (Finset.univ.product (Finset.range N)).filter (fun p ↦
        (q : ℤ) ≤ residueScale p.1 p.2 ∧
          residueScale p.1 p.2 < (N : ℤ)),
        u (residueScale p.1 p.2) := by
  apply Finset.sum_bij (fun k _ ↦
    (⟨k % 7, Nat.mod_lt _ (by omega)⟩, k / 7))
  · intro k hk
    have hk' := Finset.mem_filter.mp hk
    have hkN : k < N := Finset.mem_range.mp hk'.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · exact Finset.mem_range.mpr ((Nat.div_le_self k 7).trans_lt hkN)
    · have heq : residueScale
          (⟨k % 7, Nat.mod_lt _ (by omega)⟩ : Fin 7) (k / 7) = (k : ℤ) := by
        unfold residueScale
        exact_mod_cast Nat.mod_add_div k 7
      rw [heq]
      exact ⟨by exact_mod_cast hk'.2, by exact_mod_cast hkN⟩
  · intro k₁ hk₁ k₂ hk₂ heq
    have hs := congrArg (fun p : Fin 7 × ℕ ↦ residueScale p.1 p.2) heq
    have h₁ : residueScale
        (⟨k₁ % 7, Nat.mod_lt _ (by omega)⟩ : Fin 7) (k₁ / 7) = (k₁ : ℤ) := by
      unfold residueScale
      exact_mod_cast Nat.mod_add_div k₁ 7
    have h₂ : residueScale
        (⟨k₂ % 7, Nat.mod_lt _ (by omega)⟩ : Fin 7) (k₂ / 7) = (k₂ : ℤ) := by
      unfold residueScale
      exact_mod_cast Nat.mod_add_div k₂ 7
    rw [h₁, h₂] at hs
    exact_mod_cast hs
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    let k : ℕ := (p.1 : ℕ) + 7 * p.2
    have hscale : residueScale p.1 p.2 = (k : ℤ) := by
      simp only [residueScale, k]
      norm_cast
    have hqk : (q : ℤ) ≤ (k : ℤ) := by
      simpa only [hscale] using hp'.2.1
    have hkN : (k : ℤ) < (N : ℤ) := by
      simpa only [hscale] using hp'.2.2
    refine ⟨k, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ?_⟩
      · exact_mod_cast hkN
      · exact_mod_cast hqk
    · apply Prod.ext
      · apply Fin.ext
        dsimp [k]
        omega
      · dsimp [k]
        omega
  · intro k hk
    have heq : residueScale
        (⟨k % 7, Nat.mod_lt _ (by omega)⟩ : Fin 7) (k / 7) = (k : ℤ) := by
      unfold residueScale
      exact_mod_cast Nat.mod_add_div k 7
    rw [heq]

/-- If the summand vanishes at scales at least `N`, the harmless overrun
terms in the seven rectangular residue ranges may be inserted.
@isnad1 id=eq.1h4v.s7.6a60baec97c0 from=translated src=- shape=809b2c4a vocab=9ec0e46e
-/
theorem sum_range_filter_eq_sum_sevenResidues_of_zero_outside
    {E : Type*} [AddCommMonoid E] (u : ℤ → E) (N q : ℕ)
    (hzero : ∀ k : ℤ, 0 ≤ k → (N : ℤ) ≤ k → u k = 0) :
    (∑ k ∈ (Finset.range N).filter (fun k ↦ q ≤ k), u (k : ℤ)) =
      ∑ r : Fin 7, ∑ n ∈ (Finset.range N).filter
        (fun n ↦ (q : ℤ) ≤ residueScale r n), u (residueScale r n) := by
  calc
    (∑ k ∈ (Finset.range N).filter (fun k ↦ q ≤ k), u (k : ℤ)) =
        ∑ p ∈ (Finset.univ.product (Finset.range N)).filter (fun p ↦
          (q : ℤ) ≤ residueScale p.1 p.2 ∧
            residueScale p.1 p.2 < (N : ℤ)),
          u (residueScale p.1 p.2) := sum_range_filter_eq_sum_residuePairs u N q
    _ = ∑ r : Fin 7, ∑ n ∈ (Finset.range N).filter (fun n ↦
          (q : ℤ) ≤ residueScale r n ∧ residueScale r n < (N : ℤ)),
          u (residueScale r n) := by
      rw [Finset.sum_filter]
      calc
        (∑ p ∈ Finset.univ.product (Finset.range N),
            if (q : ℤ) ≤ residueScale p.1 p.2 ∧
                residueScale p.1 p.2 < (N : ℤ) then
              u (residueScale p.1 p.2) else 0) =
            ∑ r ∈ Finset.univ, ∑ n ∈ Finset.range N,
              if (q : ℤ) ≤ residueScale r n ∧
                  residueScale r n < (N : ℤ) then
                u (residueScale r n) else 0 :=
          Finset.sum_product Finset.univ (Finset.range N) _
        _ = _ := by simp_rw [← Finset.sum_filter]
    _ = ∑ r : Fin 7, ∑ n ∈ (Finset.range N).filter
        (fun n ↦ (q : ℤ) ≤ residueScale r n), u (residueScale r n) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_subset
      · intro n hn
        have hn' := Finset.mem_filter.mp hn
        exact Finset.mem_filter.mpr ⟨hn'.1, hn'.2.1⟩
      · intro n hnq hnnot
        have hnq' := Finset.mem_filter.mp hnq
        have hnN : (N : ℤ) ≤ residueScale r n := by
          by_contra hlt
          apply hnnot
          exact Finset.mem_filter.mpr ⟨hnq'.1, hnq'.2, lt_of_not_ge hlt⟩
        exact hzero (residueScale r n) (by unfold residueScale; omega) hnN

/-- On nonnegative scales, the literal length threshold is the cutoff at
`max 0 (ell - 2)`.  This is the point where the physical-scale convention
`length = 2^(scale + 2)` enters the residue bookkeeping.
@isnad1 id=iff.5h6v.s7.4ffb3c2fe311 from=translated src=- shape=70c348e2 vocab=26a4531a
-/
theorem length_threshold_iff_scale_cutoff_of_geometry
    (S A : Finset RealInterval) (scale : RealInterval → ℤ)
    (ell : ℤ) (q : ℕ) {I : RealInterval}
    (hA : A ⊆ S)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hnonneg : ∀ I ∈ A, 0 ≤ scale I)
    (hq : (q : ℤ) = max 0 (ell - 2)) (hI : I ∈ A) :
    (2 : ℝ) ^ ell ≤ I.length ↔ (q : ℤ) ≤ scale I := by
  rw [hscale I (hA hI)]
  rw [zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
  rw [hq]
  have hI0 := hnonneg I hI
  omega

/-- A thresholded fixed-scale output agrees with the unthresholded one once
the scale is above the physical threshold.
@isnad1 id=eq.5h8v.s7.c99c1b69476c from=translated src=- shape=d5ccb02c vocab=4c09dff4
-/
theorem directScaleOutputAtThreshold_eq_directScaleOutput_of_geometry
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell k s : ℤ) (q : ℕ)
    (hA : A ⊆ S)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hnonneg : ∀ I ∈ A, 0 ≤ scale I)
    (hq : (q : ℤ) = max 0 (ell - 2)) (hk : (q : ℤ) ≤ k) :
    directScaleOutputAtThreshold S A scale f ell k s =
      directScaleOutput S A scale f k s := by
  funext x
  have hfilter :
      (A.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length)).filter
          (fun I ↦ scale I = k) =
        A.filter (fun I ↦ scale I = k) := by
    ext I
    simp only [Finset.mem_filter]
    constructor
    · intro hI
      exact ⟨hI.1.1, hI.2⟩
    · intro hI
      refine ⟨⟨hI.1, ?_⟩, hI.2⟩
      have hcut := (length_threshold_iff_scale_cutoff_of_geometry
        S A scale ell q hA hscale hnonneg hq hI.1).mpr
        (by simpa [hI.2] using hk)
      exact hcut
  simp only [directScaleOutputAtThreshold, directScaleOutput, hfilter]

/-- A thresholded scale absent from the image of the retained threshold
family contributes zero.
@isnad1 id=eq.1h7v.s6.82be840b1b82 from=translated src=- shape=a326a949 vocab=b4e66d76
-/
theorem directScaleOutputAtThreshold_eq_zero_of_not_mem_image
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell k s : ℤ)
    (hk : k ∉ (A.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length)).image scale) :
    directScaleOutputAtThreshold S A scale f ell k s = 0 := by
  funext x
  unfold directScaleOutputAtThreshold
  apply Finset.sum_eq_zero
  intro I hI
  exact (hk (Finset.mem_image.mpr ⟨I, (Finset.mem_filter.mp hI).1,
    (Finset.mem_filter.mp hI).2⟩)).elim

/-- Exact recombination of a physical threshold into the finite interval of
actual nonnegative scales.
@isnad1 id=eq.5h9v.s7.9f89fbf8e9c6 from=translated src=- shape=bbb41974 vocab=8f858bd5
-/
theorem offsetLocalizedActionOn_eq_sum_range_scaleOutputs_of_geometry
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell s : ℤ) (q N : ℕ) (x : ℝ)
    (hA : A ⊆ S)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hnonneg : ∀ I ∈ A, 0 ≤ scale I)
    (hbound : ∀ I ∈ A, scale I < N)
    (hq : (q : ℤ) = max 0 (ell - 2)) :
    offsetLocalizedActionOn S A scale f ell s x =
      ∑ k ∈ (Finset.range N).filter (fun k ↦ q ≤ k),
        directScaleOutput S A scale f (k : ℤ) s x := by
  classical
  let T := A.filter (fun I ↦ (2 : ℝ) ^ ell ≤ I.length)
  let U : Finset ℤ := ((Finset.range N).filter (fun k ↦ q ≤ k)).map
    ⟨fun k : ℕ ↦ (k : ℤ), by intro a b h; exact Int.ofNat_inj.mp h⟩
  have himage : T.image scale ⊆ U := by
    intro k hk
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hk
    have hIA : I ∈ A := (Finset.mem_filter.mp hI).1
    have hcut : (q : ℤ) ≤ scale I :=
      (length_threshold_iff_scale_cutoff_of_geometry
        S A scale ell q hA hscale hnonneg hq hIA).mp
        (Finset.mem_filter.mp hI).2
    apply Finset.mem_map.mpr
    refine ⟨(scale I).toNat, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩, ?_⟩
    · exact (Int.toNat_lt (hnonneg I hIA)).mpr (hbound I hIA)
    · rw [← Int.toNat_of_nonneg (hnonneg I hIA)] at hcut
      exact_mod_cast hcut
    · exact Int.toNat_of_nonneg (hnonneg I hIA)
  calc
    offsetLocalizedActionOn S A scale f ell s x =
        ∑ k ∈ T.image scale,
          directScaleOutputAtThreshold S A scale f ell k s x := by
      simpa only [T] using
        (offsetLocalizedActionOn_eq_sum_scaleOutputs S A scale f ell s x)
    _ = ∑ k ∈ U, directScaleOutputAtThreshold S A scale f ell k s x := by
      apply Finset.sum_subset himage
      intro k hkU hkimage
      exact congrFun
        (directScaleOutputAtThreshold_eq_zero_of_not_mem_image S A scale f ell k s hkimage) x
    _ = ∑ k ∈ U, directScaleOutput S A scale f k s x := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkq : (q : ℤ) ≤ k := by
        obtain ⟨m, hm, hmk⟩ := Finset.mem_map.mp hk
        have hmq : q ≤ m := (Finset.mem_filter.mp hm).2
        rw [← hmk]
        change (q : ℤ) ≤ (m : ℤ)
        exact_mod_cast hmq
      exact congrFun
        (directScaleOutputAtThreshold_eq_directScaleOutput_of_geometry
          S A scale f ell k s q hA hscale hnonneg hq hkq) x
    _ = ∑ k ∈ (Finset.range N).filter (fun k ↦ q ≤ k),
        directScaleOutput S A scale f (k : ℤ) s x := by
      dsimp [U]
      rw [Finset.sum_map]
      rfl

/-- The physical threshold action is exactly the sum of its seven residue
cutoffs.  No decomposition hypothesis is left for the caller.
@isnad1 id=eq.4h8v.s8.3ffdbf5f07c5 from=translated src=- shape=c691862c vocab=d34d381c
-/
theorem offsetLocalizedActionOn_eq_sum_seven_residueCutoffs_of_geometry
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell s : ℤ) (N : ℕ) (x : ℝ)
    (hA : A ⊆ S)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hnonneg : ∀ I ∈ A, 0 ≤ scale I)
    (hbound : ∀ I ∈ A, scale I < N) :
    offsetLocalizedActionOn S A scale f ell s x =
      ∑ r : Fin 7, ∑ n ∈ (Finset.range N).filter
        (fun n ↦ ((max 0 (ell - 2)).toNat : ℤ) ≤ residueScale r n),
        directResidueOutput S A scale f r s n x := by
  let q : ℕ := (max 0 (ell - 2)).toNat
  have hq : (q : ℤ) = max 0 (ell - 2) := by
    dsimp [q]
    rw [Int.toNat_of_nonneg]
    exact le_max_left _ _
  calc
    offsetLocalizedActionOn S A scale f ell s x =
        ∑ k ∈ (Finset.range N).filter (fun k ↦ q ≤ k),
          directScaleOutput S A scale f (k : ℤ) s x :=
      offsetLocalizedActionOn_eq_sum_range_scaleOutputs_of_geometry
        S A scale f ell s q N x hA hscale hnonneg hbound hq
    _ = ∑ r : Fin 7, ∑ n ∈ (Finset.range N).filter
        (fun n ↦ (q : ℤ) ≤ residueScale r n),
        directScaleOutput S A scale f (residueScale r n) s x := by
      exact sum_range_filter_eq_sum_sevenResidues_of_zero_outside
        (fun k ↦ directScaleOutput S A scale f k s x) N q (by
      intro k hk0 hkN
      exact congrFun (directScaleOutput_eq_zero_of_outside_range S A scale f N s k
        hnonneg hbound (Or.inr hkN)) x)
    _ = ∑ r : Fin 7, ∑ n ∈ (Finset.range N).filter
        (fun n ↦ (q : ℤ) ≤ residueScale r n),
        directResidueOutput S A scale f r s n x := by rfl
    _ = ∑ r : Fin 7, ∑ n ∈ (Finset.range N).filter
        (fun n ↦ ((max 0 (ell - 2)).toNat : ℤ) ≤ residueScale r n),
        directResidueOutput S A scale f r s n x := by rfl

/-- Once a thresholded direct action has been written as the finite sum of
its seven residue cutoffs, the triangle inequality and the residue arithmetic
give the desired seven-tail majorization.  The equality premise is deliberately
separate: it is the remaining finite `Nat` division/modulo reindexing bridge.
@isnad1 id=le.1h9v.s7.9477fc39fd69 from=translated src=- shape=fa525917 vocab=010ae73e
-/
theorem enorm_offsetLocalizedActionOn_le_sum_seven_tailMax_of_residue_decomposition
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell s : ℤ) (q N : ℕ) (x : ℝ)
    (hdecomp : offsetLocalizedActionOn S A scale f ell s x =
      ∑ r : Fin 7, ∑ n ∈ (Finset.range N).filter
        (fun n ↦ (q : ℤ) ≤ residueScale r n),
        directResidueOutput S A scale f r s n x) :
    ‖offsetLocalizedActionOn S A scale f ell s x‖ₑ ≤
      ∑ r : Fin 7, finitePieceTailMax N (directResidueOutput S A scale f r s) x := by
  rw [hdecomp]
  calc
    ‖∑ r : Fin 7, ∑ n ∈ (Finset.range N).filter
        (fun n ↦ (q : ℤ) ≤ residueScale r n),
        directResidueOutput S A scale f r s n x‖ₑ ≤
      ∑ r : Fin 7, ‖∑ n ∈ (Finset.range N).filter
        (fun n ↦ (q : ℤ) ≤ residueScale r n),
        directResidueOutput S A scale f r s n x‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ r : Fin 7, finitePieceTailMax N
        (directResidueOutput S A scale f r s) x := by
          apply Finset.sum_le_sum
          intro r hr
          exact enorm_directResidue_cutoff_le_tailMax S A scale f r q N s x

/-- The seven-tail estimate with the residue decomposition supplied by the
physical scale geometry, rather than by a separate premise.
@isnad1 id=le.4h8v.s7.b852bc0282b2 from=translated src=- shape=1c63c784 vocab=e71bb4f8
-/
theorem enorm_offsetLocalizedActionOn_le_sum_seven_tailMax_of_geometry
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell s : ℤ) (N : ℕ) (x : ℝ)
    (hA : A ⊆ S)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hnonneg : ∀ I ∈ A, 0 ≤ scale I)
    (hbound : ∀ I ∈ A, scale I < N) :
    ‖offsetLocalizedActionOn S A scale f ell s x‖ₑ ≤
      ∑ r : Fin 7, finitePieceTailMax N (directResidueOutput S A scale f r s) x := by
  exact enorm_offsetLocalizedActionOn_le_sum_seven_tailMax_of_residue_decomposition
    S A scale f ell s (max 0 (ell - 2)).toNat N x
    (offsetLocalizedActionOn_eq_sum_seven_residueCutoffs_of_geometry
      S A scale f ell s N x hA hscale hnonneg hbound)

/-- The genuine threshold maximal action is pointwise controlled by the same
seven finite residue-tail maxima.  The fixed-threshold geometric bound is
uniform in the index of the supremum.
@isnad1 id=le.4h8v.s7.1ac947866b3e from=translated src=- shape=7633fcdf vocab=7d9db5ed
-/
theorem offsetTailMaximalOn_le_sum_seven_tailMax_of_geometry
    (S A : Finset RealInterval) (scale : RealInterval → ℤ) (f : ℝ → ℂ)
    (ell₀ s : ℤ) (N : ℕ) (x : ℝ)
    (hA : A ⊆ S)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hnonneg : ∀ I ∈ A, 0 ≤ scale I)
    (hbound : ∀ I ∈ A, scale I < N) :
    offsetTailMaximalOn S A scale f ell₀ s x ≤
      ∑ r : Fin 7, finitePieceTailMax N (directResidueOutput S A scale f r s) x := by
  unfold offsetTailMaximalOn
  apply iSup_le
  rintro ⟨ell, hell⟩
  exact enorm_offsetLocalizedActionOn_le_sum_seven_tailMax_of_geometry
    S A scale f ell s N x hA hscale hnonneg hbound

end
end KrauseLaceyQuadraticDirectScaleTails
end QuadraticCarleson
