/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.RepresentationTheory.Crystal.Subcrystal
import Tengoku.Seed.Topology.Algebra.Order.Field
import Tengoku.Seed.Topology.Order.Compact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Littelmann paths

Littelmann's path model ([Lit95] §1, [Lit94]) realizes the crystals of integrable
highest-weight modules by paths `π : [0,1] → X_ℝ` in the real span of the weight lattice, with
`π(0) = 0` and `π(1) ∈ X`. The root operators (defined in
`LieLean.RepresentationTheory.Crystal.Path.RootOperators`) only use, for each simple coroot
`αᵢ^∨`, the function `hᵢ(t) = ⟨π(t), αᵢ^∨⟩` and its running minima. This file sets up the paths and
these functions.

## Conventions

Littelmann considers piecewise linear paths `[0,1] ∩ ℚ → ℚ ⊗ X` ([Lit95] §1) modulo
reparametrization. We work instead with *parametrized* paths `π : 𝕜 → V` (constant outside `[0,1]`)
and only require continuity of the functions `hᵢ`; no quotient is needed, because the root operators
are defined pointwise in the time parameter (`π ↦ π - c(t) αᵢ` for an explicit continuous function
`c`) and are exactly inverse to each other on parametrized paths. Piecewise linear paths form a
subclass stable under the root operators; we do not need this.

The real span of the weight lattice is an auxiliary vector space `V` containing `X`, on which the
coroots extend to linear forms (`CartanDatum.PathSpace`). Instead of `ℝ` we allow any
conditionally complete linearly ordered field `𝕜` with its order topology (such a field is
isomorphic to `ℝ`); only the existence of minima of continuous functions on compact intervals and
the intermediate value theorem are used.

## Main definitions

* `CartanDatum.PathSpace D 𝕜 V`: an embedding of the weight lattice `X` of a Cartan datum into a
  `𝕜`-vector space `V`, with `𝕜`-linear extensions of the coroots.
* `LittelmannPath S`: paths `π : 𝕜 → V`, constant outside `[0,1]`, with `π(0) = 0`,
  `π(1) = wt π ∈ X`, and continuous `hᵢ = ⟨π(·), αᵢ^∨⟩` for every `i`.
* `LittelmannPath.pairing π i t = ⟨π(t), αᵢ^∨⟩`, its running minimum
  `LittelmannPath.runningMin π i t = min_{s ∈ [0,t]} hᵢ(s)`, the minimum from the right
  `LittelmannPath.rightMin π i t = min_{s ∈ [t,1]} hᵢ(s)`, and the minimum
  `LittelmannPath.minPairing π i = min_{[0,1]} hᵢ` (Littelmann's `m_α`).
* `LittelmannPath.rev`: the reversed path `π^∨(t) = π(1 - t) - π(1)` ([Lit95] §2).

## Main results

* `LittelmannPath.continuous_runningMin`: the running minimum is continuous.
* `LittelmannPath.runningMin_rev`: the running minimum of `π^∨` is the minimum from the right of
  `π`.

## References

* [Lit94] P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*,
  Invent. Math. **116** (1994), 329–346.
* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math.
  **142** (1995), 499–525.
-/
namespace Tengoku.LieLean end Tengoku.LieLean open Tengoku.LieLean
open Set

/-! ### Minima of continuous functions on compact intervals -/

namespace Tengoku.LieLean.LittelmannPath

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {g : 𝕜 → 𝕜} {a b c : 𝕜}

/--
@isnad1 id=le.2h5v.s6.9e253e1c99d2 from=translated src=- shape=775a9eea vocab=f6dc84ed
-/
lemma sInf_image_Icc_le (hg : Continuous g) {s : 𝕜} (hs : s ∈ Icc a b) :
    sInf (g '' Icc a b) ≤ g s :=
  csInf_le (isCompact_Icc.image hg).bddBelow (mem_image_of_mem g hs)

/--
@isnad1 id=ex.2h4v.s6.76f85c06128c from=translated src=- shape=eb99f368 vocab=f6dc84ed
-/
lemma exists_eq_sInf_image_Icc (hg : Continuous g) (hab : a ≤ b) :
    ∃ s ∈ Icc a b, g s = sInf (g '' Icc a b) :=
  (isCompact_Icc.image hg).sInf_mem ((nonempty_Icc.mpr hab).image g)

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] in
/--
@isnad1 id=le.2h5v.s6.b0e6bbc1fadf from=translated src=- shape=be0d7895 vocab=206b4b4f
-/
lemma le_sInf_image_Icc (hab : a ≤ b) (h : ∀ s ∈ Icc a b, c ≤ g s) :
    c ≤ sInf (g '' Icc a b) :=
  le_csInf ((nonempty_Icc.mpr hab).image g) (forall_mem_image.mpr h)

/--
@isnad1 id=eq.4h5v.s7.6b1167879a5e from=translated src=- shape=9c0f41fe vocab=f6dc84ed
-/
lemma sInf_image_Icc_eq (hg : Continuous g) (hab : a ≤ b) {s : 𝕜} (hs : s ∈ Icc a b)
    (h : ∀ t ∈ Icc a b, g s ≤ g t) : sInf (g '' Icc a b) = g s :=
  le_antisymm (sInf_image_Icc_le hg hs) (le_sInf_image_Icc hab h)

/--
@isnad1 id=le.4h6v.s7.6e56e692240b from=translated src=- shape=55420e05 vocab=66be6ade
-/
lemma sInf_image_Icc_anti (hg : Continuous g) {a' b' : 𝕜} (hab : a ≤ b) (ha : a' ≤ a)
    (hb : b ≤ b') : sInf (g '' Icc a' b') ≤ sInf (g '' Icc a b) :=
  csInf_le_csInf (isCompact_Icc.image hg).bddBelow ((nonempty_Icc.mpr hab).image g)
    (image_mono (Icc_subset_Icc ha hb))

variable [DenselyOrdered 𝕜]

/-- The first time in `[a, b]` at which a continuous function with `c ≤ g a` and `g b ≤ c`
reaches the level `c`.
@isnad1 id=ex.4h5v.s7.1a0e253c7557 from=translated src=- shape=d6dab761 vocab=3c71b1f5
-/
lemma exists_first_eq (hg : Continuous g) (hab : a ≤ b) (ha : c ≤ g a) (hb : g b ≤ c) :
    ∃ u ∈ Icc a b, g u = c ∧ ∀ v ∈ Ico a u, c < g v := by
  set K := Icc a b ∩ g ⁻¹' Iic c
  have hK : IsClosed K := isClosed_Icc.inter (isClosed_Iic.preimage hg)
  have hne : K.Nonempty := ⟨b, right_mem_Icc.mpr hab, hb⟩
  have hbdd : BddBelow K := ⟨a, fun x hx ↦ hx.1.1⟩
  have hu := hK.csInf_mem hne hbdd
  refine ⟨sInf K, hu.1, ?_, fun v hv ↦ ?_⟩
  · obtain ⟨w, hw, hwc⟩ := intermediate_value_Icc' hu.1.1 hg.continuousOn ⟨hu.2, ha⟩
    have : sInf K ≤ w := csInf_le hbdd ⟨⟨hw.1, hw.2.trans hu.1.2⟩, hwc.le⟩
    rw [← le_antisymm hw.2 this]
    exact hwc
  · by_contra hcv
    have := csInf_le hbdd ⟨⟨hv.1, hv.2.le.trans hu.1.2⟩, not_lt.mp hcv⟩
    exact absurd hv.2 (not_lt.mpr this)

omit [DenselyOrdered 𝕜] in
/-- The running minimum `t ↦ min_{[0, max 0 t]} g` of a continuous function vanishing on
`(-∞, 0]` is continuous.
@isnad1 id=continuo.2h2v.s7.179c0251b77c from=translated src=- shape=e04c66ac vocab=cce267d3
-/
lemma continuous_sInf_image_Icc_zero [Field 𝕜] [IsStrictOrderedRing 𝕜] (hg : Continuous g)
    (h0 : ∀ t ≤ 0, g t = 0) :
    Continuous fun t ↦ sInf (g '' Icc 0 (max 0 t)) := by
  have : (fun t ↦ sInf (g '' Icc 0 (max 0 t))) =
      fun t ↦ sInf ((fun t u ↦ g (u * t)) t '' Icc 0 1) := by
    funext t
    change sInf (g '' Icc 0 (max 0 t)) = sInf ((fun u ↦ g (u * t)) '' Icc 0 1)
    rcases le_or_gt 0 t with ht | ht
    · rw [max_eq_right ht, show (fun u ↦ g (u * t)) = g ∘ (fun u ↦ u * t) from rfl, image_comp,
        image_mul_right_Icc zero_le_one ht, zero_mul, one_mul]
    · rw [max_eq_left ht.le, Icc_self, image_singleton, h0 0 le_rfl, csInf_singleton]
      have : (fun u ↦ g (u * t)) '' Icc 0 1 = (fun _ : 𝕜 ↦ (0 : 𝕜)) '' Icc (0 : 𝕜) 1 :=
        image_congr fun (u : 𝕜) (hu : u ∈ Icc (0 : 𝕜) 1) ↦
          h0 _ (mul_nonpos_of_nonneg_of_nonpos hu.1 ht.le)
      rw [this, (nonempty_Icc.mpr zero_le_one).image_const, csInf_singleton]
  rw [this]
  exact isCompact_Icc.continuous_sInf (hg.comp (continuous_snd.mul continuous_fst))

end Tengoku.LieLean.LittelmannPath

/-! ### Paths -/

variable {ι X : Type*} [AddCommGroup X]

/-- An embedding of the weight lattice `X` of a Cartan datum into a vector space `V` over a field
`𝕜` (in practice `𝕜 = ℝ`), together with linear extensions `V → 𝕜` of the coroots `⟨·, αᵢ^∨⟩`.
Littelmann's paths ([Lit95] §1) take values in `V` (for instance `V = ℝ ⊗ X`, or
`V = 𝔥*` for a realization over `ℝ`).-/
structure Tengoku.LieLean.CartanDatum.PathSpace (D : CartanDatum ι X) (𝕜 V : Type*) [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] where
  /-- The embedding `X → V`.-/
  embed : X →+ V
  embed_injective : Function.Injective embed
  /-- The linear extensions of the coroots.-/
  coroot : ι → Module.Dual 𝕜 V
  coroot_embed : ∀ i x, coroot i (embed x) = D.coroot i x

namespace Tengoku.LieLean.CartanDatum.PathSpace

variable {𝕜 : Type*} [Field 𝕜] {D : CartanDatum ι X} {V : Type*} [AddCommGroup V] [Module 𝕜 V]
  (S : D.PathSpace 𝕜 V)

/-- The simple root `αᵢ`, as an element of `V`.-/
def root (i : ι) : V := S.embed (D.root i)

/--
@isnad1 id=eq.0h8v.s7.f589c8e97787 from=translated src=- shape=53688867 vocab=3a2b320d
-/
lemma coroot_root (i j : ι) : S.coroot i (S.root j) = D.cartanMatrix i j := by
  simp [root, coroot_embed]

/--
@isnad1 id=eq.0h7v.s7.6382c6c40a13 from=translated src=- shape=e08e5122 vocab=71b1dae4
-/
@[simp] lemma coroot_root_self (i : ι) : S.coroot i (S.root i) = 2 := by
  rw [coroot_root, D.cartanMatrix_self]
  norm_num

end Tengoku.LieLean.CartanDatum.PathSpace

/-- A (parametrized) Littelmann path ([Lit95] §1) in the span `V` of the weight
lattice: a map `π : 𝕜 → V`, constant outside `[0,1]`, with `π(0) = 0` and endpoint
`π(1) = wt π ∈ X`, such that `t ↦ ⟨π(t), αᵢ^∨⟩` is continuous for every `i`.-/
structure _root_.Tengoku.LieLean.LittelmannPath {𝕜 : Type*} [Field 𝕜] [LE 𝕜] [TopologicalSpace 𝕜] {D : CartanDatum ι X}
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] (S : D.PathSpace 𝕜 V) where
  /-- The underlying map.-/
  toFun : 𝕜 → V
  /-- The endpoint `π(1)`, as an element of the weight lattice.-/
  wt : X
  toFun_of_nonpos' : ∀ t ≤ 0, toFun t = 0
  toFun_of_one_le' : ∀ t, 1 ≤ t → toFun t = S.embed wt
  continuous_coroot' : ∀ i, Continuous fun t ↦ S.coroot i (toFun t)

namespace Tengoku.LieLean.LittelmannPath

section Basic

variable {𝕜 : Type*} [Field 𝕜] [Preorder 𝕜] [TopologicalSpace 𝕜] {D : CartanDatum ι X}
  {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}

instance : FunLike (LittelmannPath S) 𝕜 V where
  coe := toFun
  coe_injective π π' h := by
    have hw : π.wt = π'.wt := S.embed_injective <| by
      rw [← π.toFun_of_one_le' 1 le_rfl, ← π'.toFun_of_one_le' 1 le_rfl, h]
    cases π
    cases π'
    congr

variable (π π' : LittelmannPath S) {i : ι} {s t : 𝕜}

/--
@isnad1 id=eq.0h7v.s6.94011e6f2808 from=translated src=- shape=e9eac4fc vocab=f4694cac
-/
@[simp] lemma toFun_eq_coe : π.toFun = π := rfl

/--
@isnad1 id=eq.1h8v.s7.2681af0a3e92 from=translated src=- shape=37d0e41c vocab=14581e72
-/
@[ext] lemma ext {π π' : LittelmannPath S} (h : ∀ t, π t = π' t) : π = π' :=
  DFunLike.ext _ _ h

/--
@isnad1 id=eq.1h8v.s7.3d30ce071b26 from=translated src=- shape=639bdc0f vocab=ea25e82e
-/
lemma apply_of_nonpos (ht : t ≤ 0) : π t = 0 := π.toFun_of_nonpos' t ht

/--
@isnad1 id=eq.1h8v.s7.f89099d5c004 from=translated src=- shape=0967dbda vocab=3cfcd7f7
-/
lemma apply_of_one_le (ht : 1 ≤ t) : π t = S.embed π.wt := π.toFun_of_one_le' t ht

/--
@isnad1 id=eq.0h7v.s7.0f635cf25384 from=translated src=- shape=08a730dd vocab=14581e72
-/
@[simp] lemma apply_zero : π 0 = 0 := π.apply_of_nonpos le_rfl

/--
@isnad1 id=eq.0h7v.s7.78b20defba68 from=translated src=- shape=92b42dde vocab=ce233788
-/
lemma apply_one : π 1 = S.embed π.wt := π.apply_of_one_le le_rfl

/-- Littelmann's function `hᵢ(t) = ⟨π(t), αᵢ^∨⟩`.-/
def pairing (i : ι) (t : 𝕜) : 𝕜 := S.coroot i (π t)

/--
@isnad1 id=continuo.0h8v.s6.511bd0bdac51 from=translated src=- shape=c79f6564 vocab=c3897d3d
-/
lemma continuous_pairing (i : ι) : Continuous (π.pairing i) := π.continuous_coroot' i

/--
@isnad1 id=eq.1h9v.s7.67bb3e71e2ea from=translated src=- shape=649461b4 vocab=c6426616
-/
lemma pairing_of_nonpos (ht : t ≤ 0) : π.pairing i t = 0 := by
  simp [pairing, π.apply_of_nonpos ht]

/--
@isnad1 id=eq.0h8v.s6.7451911d979a from=translated src=- shape=374e4079 vocab=de740792
-/
@[simp] lemma pairing_zero : π.pairing i 0 = 0 := π.pairing_of_nonpos le_rfl

/--
@isnad1 id=eq.0h8v.s7.6de3bee7681a from=translated src=- shape=d20f4af7 vocab=96422908
-/
lemma pairing_one (i : ι) : π.pairing i 1 = D.coroot i π.wt := by
  rw [pairing, apply_one, S.coroot_embed]

/--
@isnad1 id=eq.1h9v.s7.d74446bce2c3 from=translated src=- shape=ebb998b9 vocab=c6426616
-/
lemma pairing_of_one_le (ht : 1 ≤ t) : π.pairing i t = π.pairing i 1 := by
  rw [pairing, pairing, π.apply_of_one_le ht, apply_one]

end Basic

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] {D : CartanDatum ι X} {V : Type*} [AddCommGroup V]
  [Module 𝕜 V] {S : D.PathSpace 𝕜 V} (π : LittelmannPath S) {i : ι} {s t : 𝕜}

omit [OrderTopology 𝕜] in
/-- Two paths agreeing on `[0,1]` are equal.
@isnad1 id=eq.1h8v.s8.86a7cf260384 from=translated src=- shape=3d64b4aa vocab=5271ccc3
-/
lemma ext_of_eqOn {π π' : LittelmannPath S} (h : ∀ t ∈ Icc (0 : 𝕜) 1, π t = π' t) : π = π' := by
  ext t
  rcases le_or_gt t 0 with ht | ht
  · rw [π.apply_of_nonpos ht, π'.apply_of_nonpos ht]
  rcases le_or_gt 1 t with ht' | ht'
  · rw [π.apply_of_one_le ht', π'.apply_of_one_le ht', ← π.apply_one, ← π'.apply_one,
      h 1 ⟨zero_le_one, le_rfl⟩]
  · exact h t ⟨ht.le, ht'.le⟩

/-- The running minimum `min_{s ∈ [0,t]} hᵢ(s)` (for `t < 0` it is `hᵢ(0) = 0`).-/
noncomputable def runningMin (i : ι) (t : 𝕜) : 𝕜 := sInf (π.pairing i '' Icc 0 (max 0 t))

/-- The minimum `min_{s ∈ [t,1]} hᵢ(s)`, for `t ∈ [0,1]`.-/
noncomputable def rightMin (i : ι) (t : 𝕜) : 𝕜 := sInf (π.pairing i '' Icc t 1)

/-- The minimum `mᵢ = min_{t ∈ [0,1]} hᵢ(t)` of Littelmann's function `hᵢ`.-/
noncomputable def minPairing (i : ι) : 𝕜 := π.runningMin i 1

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] in
/--
@isnad1 id=eq.1h9v.s7.3da6725a2ac4 from=translated src=- shape=c400fda1 vocab=ef1a2ec0
-/
lemma runningMin_eq (ht : 0 ≤ t) : π.runningMin i t = sInf (π.pairing i '' Icc 0 t) := by
  rw [runningMin, max_eq_right ht]

omit [OrderTopology 𝕜] in
/--
@isnad1 id=eq.0h8v.s7.00d3e6c9e645 from=translated src=- shape=371e56ca vocab=f51e3419
-/
lemma rightMin_zero (i : ι) : π.rightMin i 0 = π.minPairing i := by
  rw [minPairing, runningMin_eq _ zero_le_one, rightMin]

omit [IsStrictOrderedRing 𝕜] in
/--
@isnad1 id=le.1h10v.s7.ddd7109e8756 from=translated src=- shape=3779936c vocab=8334be4d
-/
lemma runningMin_le (hs : s ∈ Icc 0 t) : π.runningMin i t ≤ π.pairing i s :=
  (π.runningMin_eq (hs.1.trans hs.2)).trans_le (sInf_image_Icc_le (π.continuous_pairing i) hs)

omit [IsStrictOrderedRing 𝕜] in
/--
@isnad1 id=ex.1h9v.s7.ee5cf61453d7 from=translated src=- shape=83d1a139 vocab=8334be4d
-/
lemma exists_runningMin (i : ι) (ht : 0 ≤ t) :
    ∃ s ∈ Icc 0 t, π.pairing i s = π.runningMin i t := by
  rw [π.runningMin_eq ht]
  exact exists_eq_sInf_image_Icc (π.continuous_pairing i) ht

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] in
/--
@isnad1 id=le.2h10v.s7.a361c5360a33 from=translated src=- shape=7a60fb63 vocab=d85b273c
-/
lemma le_runningMin {c : 𝕜} (ht : 0 ≤ t) (h : ∀ s ∈ Icc 0 t, c ≤ π.pairing i s) :
    c ≤ π.runningMin i t :=
  (le_sInf_image_Icc ht h).trans_eq (π.runningMin_eq ht).symm

omit [IsStrictOrderedRing 𝕜] in
/--
@isnad1 id=le.2h10v.s7.61c84281cb13 from=translated src=- shape=31b153e7 vocab=c26700c0
-/
lemma runningMin_anti (hs : 0 ≤ s) (hst : s ≤ t) : π.runningMin i t ≤ π.runningMin i s := by
  rw [π.runningMin_eq hs, π.runningMin_eq (hs.trans hst)]
  exact sInf_image_Icc_anti (π.continuous_pairing i) hs le_rfl hst

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] in
/--
@isnad1 id=eq.1h9v.s7.9b2cff326785 from=translated src=- shape=649461b4 vocab=cee97f94
-/
lemma runningMin_of_nonpos (ht : t ≤ 0) : π.runningMin i t = 0 := by
  rw [runningMin, max_eq_left ht, Icc_self, image_singleton, csInf_singleton, pairing_zero]

omit [IsStrictOrderedRing 𝕜] in
/--
@isnad1 id=le.1h9v.s7.08d6c6bb54e4 from=translated src=- shape=943628b4 vocab=c26700c0
-/
lemma runningMin_le_zero (ht : 0 ≤ t) : π.runningMin i t ≤ 0 :=
  (π.runningMin_le ⟨le_rfl, ht⟩).trans_eq π.pairing_zero

/--
@isnad1 id=continuo.0h8v.s7.5f8037b89483 from=translated src=- shape=c826f0fe vocab=649525af
-/
lemma continuous_runningMin (i : ι) : Continuous (π.runningMin i) :=
  continuous_sInf_image_Icc_zero (π.continuous_pairing i) fun _ ht ↦ π.pairing_of_nonpos ht

omit [IsStrictOrderedRing 𝕜] in
/--
@isnad1 id=le.1h9v.s7.9d0a81caf659 from=translated src=- shape=7d550820 vocab=8c68357a
-/
lemma minPairing_le (hs : s ∈ Icc (0 : 𝕜) 1) : π.minPairing i ≤ π.pairing i s :=
  π.runningMin_le hs

/--
@isnad1 id=ex.0h8v.s7.30deeb721ffd from=translated src=- shape=2e1d0e66 vocab=37b76ad2
-/
lemma exists_minPairing (i : ι) : ∃ s ∈ Icc (0 : 𝕜) 1, π.pairing i s = π.minPairing i :=
  π.exists_runningMin i zero_le_one

/--
@isnad1 id=le.0h8v.s7.1813d66e3f17 from=translated src=- shape=c5561621 vocab=beeee3e5
-/
lemma minPairing_nonpos (i : ι) : π.minPairing i ≤ 0 := π.runningMin_le_zero zero_le_one

/--
@isnad1 id=le.0h8v.s7.65bf1e50b709 from=translated src=- shape=94f55fcb vocab=bf73a8a7
-/
lemma minPairing_le_pairing_one (i : ι) : π.minPairing i ≤ π.pairing i 1 :=
  π.minPairing_le ⟨zero_le_one, le_rfl⟩

/--
@isnad1 id=eq.1h9v.s7.500d6514de92 from=translated src=- shape=ca211a44 vocab=0790b4a0
-/
lemma runningMin_of_one_le (ht : 1 ≤ t) : π.runningMin i t = π.minPairing i := by
  obtain ⟨s, hs, hs'⟩ := π.exists_minPairing i
  rw [π.runningMin_eq (zero_le_one.trans ht), ← hs']
  refine sInf_image_Icc_eq (π.continuous_pairing i) (zero_le_one.trans ht)
    ⟨hs.1, hs.2.trans ht⟩ fun u hu ↦ ?_
  rw [hs']
  rcases le_total u 1 with hu1 | hu1
  · exact π.minPairing_le ⟨hu.1, hu1⟩
  · rw [π.pairing_of_one_le hu1]
    exact π.minPairing_le_pairing_one i

/--
@isnad1 id=le.1h9v.s7.846c8d232165 from=translated src=- shape=0b926483 vocab=0790b4a0
-/
lemma minPairing_le_runningMin (ht : 0 ≤ t) : π.minPairing i ≤ π.runningMin i t := by
  rcases le_total t 1 with ht1 | ht1
  · exact π.runningMin_anti ht ht1
  · exact (π.runningMin_of_one_le ht1).ge

omit [IsStrictOrderedRing 𝕜] in
/--
@isnad1 id=le.1h10v.s7.e9936d979426 from=translated src=- shape=39211814 vocab=832ca064
-/
lemma rightMin_le (hs : s ∈ Icc t 1) : π.rightMin i t ≤ π.pairing i s :=
  sInf_image_Icc_le (π.continuous_pairing i) hs

omit [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] in
/--
@isnad1 id=le.2h10v.s7.61e64f27e5eb from=translated src=- shape=d5b30d31 vocab=57876b53
-/
lemma le_rightMin {c : 𝕜} (ht : t ≤ 1) (h : ∀ s ∈ Icc t 1, c ≤ π.pairing i s) :
    c ≤ π.rightMin i t :=
  le_sInf_image_Icc ht h

omit [IsStrictOrderedRing 𝕜] in
/--
@isnad1 id=ex.1h9v.s7.6f354c5ae70b from=translated src=- shape=87ddf965 vocab=832ca064
-/
lemma exists_rightMin (i : ι) (ht : t ≤ 1) : ∃ s ∈ Icc t 1, π.pairing i s = π.rightMin i t :=
  exists_eq_sInf_image_Icc (π.continuous_pairing i) ht

/-! ### Reversed paths -/

/-- The reversed path `π^∨(t) = π(1 - t) - π(1)` ([Lit95] §2): it runs through `π`
backwards, translated so as to start at `0`; its endpoint is `-π(1)`.-/
def rev : LittelmannPath S where
  toFun t := π (1 - t) - π 1
  wt := -π.wt
  toFun_of_nonpos' t ht := by rw [π.apply_of_one_le (by linarith), apply_one, sub_self]
  toFun_of_one_le' t ht := by
    rw [π.apply_of_nonpos (by linarith), apply_one, zero_sub, map_neg]
  continuous_coroot' i := by
    simp only [map_sub]
    exact ((π.continuous_pairing i).comp (continuous_const.sub continuous_id)).sub
      continuous_const

/--
@isnad1 id=eq.0h8v.s8.70607da2706c from=translated src=- shape=09591907 vocab=a69dd496
-/
lemma rev_apply (t : 𝕜) : π.rev t = π (1 - t) - π 1 := rfl

/--
@isnad1 id=eq.0h7v.s7.856b0bc79cc0 from=translated src=- shape=4aaaff84 vocab=44c18e3a
-/
@[simp] lemma wt_rev : π.rev.wt = -π.wt := rfl

/--
@isnad1 id=eq.0h7v.s7.dec089300000 from=translated src=- shape=98c0750f vocab=64848ac4
-/
@[simp] lemma rev_rev : π.rev.rev = π := by
  ext t
  simp [rev_apply]

/--
@isnad1 id=eq.0h9v.s8.035fb11e9022 from=translated src=- shape=6d35e6b9 vocab=a9e526c2
-/
lemma pairing_rev (i : ι) (t : 𝕜) : π.rev.pairing i t = π.pairing i (1 - t) - π.pairing i 1 := by
  simp [pairing, rev_apply]

/-- The running minimum of the reversed path is the minimum from the right of the path:
`min_{[0,t]} h^∨ = min_{[1-t,1]} h - h(1)`.
@isnad1 id=eq.1h9v.s8.27249fe1a62f from=translated src=- shape=74d1e2e7 vocab=60707c78
-/
lemma runningMin_rev (ht : t ∈ Icc (0 : 𝕜) 1) :
    π.rev.runningMin i t = π.rightMin i (1 - t) - π.pairing i 1 := by
  obtain ⟨s, hs, hs'⟩ := π.exists_rightMin i (t := 1 - t) (by linarith [ht.1])
  rw [π.rev.runningMin_eq ht.1, ← hs', ← sub_sub_cancel 1 s, ← pairing_rev]
  refine sInf_image_Icc_eq (π.rev.continuous_pairing i) ht.1
    ⟨by linarith [hs.2], by linarith [hs.1]⟩ fun u hu ↦ ?_
  rw [pairing_rev, pairing_rev, sub_sub_cancel, hs']
  gcongr
  exact π.rightMin_le ⟨by linarith [hu.2], by linarith [hu.1]⟩

/--
@isnad1 id=eq.0h8v.s7.5a5ce2533c2a from=translated src=- shape=af97a34f vocab=9100291c
-/
lemma minPairing_rev (i : ι) : π.rev.minPairing i = π.minPairing i - π.pairing i 1 := by
  rw [minPairing, runningMin_rev _ ⟨zero_le_one, le_rfl⟩, sub_self, rightMin_zero]

end Tengoku.LieLean.LittelmannPath
-- Tengoku: root names of this library moved to Tengoku.LieLean so they do not collide with other libraries (generated)
