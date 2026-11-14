/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.RingOfIntegers.HalfInt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Ring `ℤ[(1 + √(1 + 4k)) / 2]`

This file defines and studies the ring `ZOnePlusSqrtdOverTwo k`, which is the
candidate ring of integers for quadratic fields with `d ≡ 1 (mod 4)`.
When `d = 1 + 4k`, we have `𝓞(Q(√d)) ≅ ℤ[(1+√d)/2]`.

## Main Definitions

* `ZOnePlusSqrtdOverTwo k`: The ring `ℤ[(1 + √(1+4k))/2]` modeled as
  `QuadraticAlgebra ℤ k 1` (satisfying `ω² = ω + k`).
* `Qsqrtd.omega k`: The generator `ω = (1 + √(1+4k))/2` in `Q(√(1+4k))`.
* `Qsqrtd.Zomega k`: The subalgebra `ℤ[ω]` as a `Subalgebra`.
* `ZOnePlusSqrtdOverTwo.toQsqrtdHom`: Ring hom embedding into `Q(√(1+4k))`.
* `ZOnePlusSqrtdOverTwo.carrierSet`: The image as a set.

## Main Theorems

* `ZOnePlusSqrtdOverTwo.toQsqrtdHom_injective`: The embedding is injective.
* `ZOnePlusSqrtdOverTwo.halfInt_mem_carrierSet_iff_same_parity`:
  A half-integer is in the carrier iff its coordinates have the same parity.
-/
namespace Tengoku.QuadraticNumberFields end Tengoku.QuadraticNumberFields open Tengoku.QuadraticNumberFields
local notation "ℚ√" d => Qsqrtd d

namespace Tengoku.QuadraticNumberFields.Qsqrtd

/-- The discriminant-like parameter `1 + 4k` viewed in `ℚ`.-/
@[nolint defsWithUnderscore]
abbrev d_of_k (k : ℤ) : ℚ := ((1 + 4 * k : ℤ) : ℚ)

/-- `ω_k = (1 + √(1 + 4k)) / 2` in `Q(√(1 + 4k))`.-/
def omega (k : ℤ) : Qsqrtd (d_of_k k) := ⟨(1 / 2 : ℚ), (1 / 2 : ℚ)⟩

/-- The order candidate `ℤ[ω_k]` with `ω_k = (1 + √(1 + 4k)) / 2`.-/
abbrev Zomega (k : ℤ) : Subalgebra ℤ (Qsqrtd (d_of_k k)) :=
  Algebra.adjoin ℤ ({omega k} : Set (Qsqrtd (d_of_k k)))

/--
@isnad1 id=mem.0h1v.s6.b92775850e7f from=translated src=- shape=cf01479f vocab=a48b13b4
-/
lemma omega_mem_Zomega (k : ℤ) : omega k ∈ Zomega k :=
  Algebra.subset_adjoin (by simp)

end Tengoku.QuadraticNumberFields.Qsqrtd

open QuadraticNumberFields

/-- Algebraic model of `ℤ[(1 + √(1 + 4d))/2]` via `ω^2 = ω + d`.
In `QuadraticAlgebra R a b`, one has `ω^2 = a + b * ω`, so this is
`QuadraticAlgebra ℤ d 1` (not `QuadraticAlgebra ℤ 1 d`).-/
abbrev _root_.Tengoku.QuadraticNumberFields.ZOnePlusSqrtdOverTwo (d : ℤ) : Type := QuadraticAlgebra ℤ d 1

namespace Tengoku.QuadraticNumberFields.ZOnePlusSqrtdOverTwo

/-- Ambient parameter in `ℚ`: `1 + 4d`.-/
abbrev qParam (d : ℤ) : ℚ := Qsqrtd.d_of_k d

/-- The norm on `ℤ[(1 + √(1 + 4d))/2]` as a `MonoidHom` to `ℤ`.-/
abbrev normHom (d : ℤ) : ZOnePlusSqrtdOverTwo d →* ℤ :=
  QuadraticAlgebra.norm

/--
@isnad1 id=eq.0h2v.s7.4c1906ad0a65 from=translated src=- shape=73b9d87c vocab=5b08e28a
-/
theorem normHom_apply (d : ℤ) (z : ZOnePlusSqrtdOverTwo d) :
    normHom d z = QuadraticAlgebra.norm z :=
  rfl

/-- The norm on the unit group of `ℤ[(1 + √(1 + 4d))/2]`, as a `MonoidHom` to `ℤˣ`.-/
abbrev normUnitsHom (d : ℤ) : (ZOnePlusSqrtdOverTwo d)ˣ →* ℤˣ :=
  Units.map (normHom d)

/--
@isnad1 id=eq.0h2v.s8.d6f711db7cef from=translated src=- shape=481a9fc8 vocab=0bc6275e
-/
theorem normUnitsHom_coe (d : ℤ) (u : (ZOnePlusSqrtdOverTwo d)ˣ) :
    ((normUnitsHom d u : ℤˣ) : ℤ) = QuadraticAlgebra.norm (u : ZOnePlusSqrtdOverTwo d) := by
  simp [normUnitsHom, normHom]

/-- The norm of `x + y·ω` in coordinates: `‖x + y·ω‖ = x² + x·y - d·y²`.
@isnad1 id=eq.0h3v.s7.2b5fa2c3e297 from=translated src=- shape=b3c01702 vocab=c4d9618e
-/
@[simp]
theorem norm_mk (d x y : ℤ) :
    QuadraticAlgebra.norm (⟨x, y⟩ : ZOnePlusSqrtdOverTwo d) = x ^ 2 + x * y - d * y ^ 2 := by
  have h : QuadraticAlgebra.norm (⟨x, y⟩ : ZOnePlusSqrtdOverTwo d) =
      x * x + 1 * x * y - d * y * y := QuadraticAlgebra.norm_def _
  rw [h]; ring

/-- `x + y·ω` is a unit of `ℤ[(1 + √(1 + 4d))/2]` iff `x² + x·y - d·y² = ±1`.
@isnad1 id=iff.0h3v.s7.1fe4596fb2a2 from=translated src=- shape=d2c5be26 vocab=ee6cd537
-/
theorem isUnit_mk_iff {d x y : ℤ} :
    IsUnit (⟨x, y⟩ : ZOnePlusSqrtdOverTwo d) ↔
      x ^ 2 + x * y - d * y ^ 2 = 1 ∨ x ^ 2 + x * y - d * y ^ 2 = -1 := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, Int.isUnit_iff, norm_mk]

/-- Coordinate-level embedding candidate into `Q(√(1 + 4d))`.-/
def toQsqrtdFun (d : ℤ) : ZOnePlusSqrtdOverTwo d → Qsqrtd (qParam d) :=
  -- Send `r + sω` to `r + s * (1 + √(1 + 4d)) / 2`,
  -- so the real coordinate is `r + s/2` and the `√d`-coordinate is `s/2`.
  fun x => ⟨(x.re : ℚ) + (x.im : ℚ) / 2, (x.im : ℚ) / 2⟩

/-- Coordinate-level embedding as a ring hom into `Q(√(1 + 4d))`.-/
def toQsqrtdHom (d : ℤ) : ZOnePlusSqrtdOverTwo d →+* Qsqrtd (qParam d) where
  toFun := toQsqrtdFun d
  map_one' := by
    ext <;> simp [toQsqrtdFun, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' := by
    -- The multiplication formulas agree because `ω² = ω + d`,
    -- which is exactly the relation defining `QuadraticAlgebra ℤ d 1`.
    intro x y
    ext <;>
      simp [toQsqrtdFun, qParam, Qsqrtd.d_of_k,
        QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;>
      ring
  map_zero' := by
    ext <;> simp [toQsqrtdFun, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero]
  map_add' := by
    intro x y
    ext <;> simp [toQsqrtdFun, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add] <;> ring

/--
@isnad1 id=eq.0h2v.s6.9110c0d7b1b6 from=translated src=- shape=1ee31dcf vocab=2a742cd5
-/
@[simp] theorem toQsqrtdHom_apply (d : ℤ) (z : ZOnePlusSqrtdOverTwo d) :
    toQsqrtdHom d z = toQsqrtdFun d z := rfl

/--
@isnad1 id=eq.0h2v.s5.601ba5d83274 from=translated src=- shape=641a30f2 vocab=182ee5aa
-/
@[simp]
theorem toQsqrtdFun_re (d : ℤ) (z : ZOnePlusSqrtdOverTwo d) :
    (toQsqrtdFun d z).re = (z.re : ℚ) + (z.im : ℚ) / 2 :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.47a6c19b437f from=translated src=- shape=b4b92100 vocab=714c2ff8
-/
@[simp]
theorem toQsqrtdFun_im (d : ℤ) (z : ZOnePlusSqrtdOverTwo d) :
    (toQsqrtdFun d z).im = (z.im : ℚ) / 2 :=
  rfl

/--
@isnad1 id=eq.0h2v.s7.13f783c1dcde from=translated src=- shape=d3cb3938 vocab=318e5755
-/
@[simp]
theorem toQsqrtdHom_re (d : ℤ) (z : ZOnePlusSqrtdOverTwo d) :
    (toQsqrtdHom d z).re = (z.re : ℚ) + (z.im : ℚ) / 2 :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.5508bea5c8d8 from=translated src=- shape=708487fe vocab=9f1057be
-/
@[simp]
theorem toQsqrtdHom_im (d : ℤ) (z : ZOnePlusSqrtdOverTwo d) :
    (toQsqrtdHom d z).im = (z.im : ℚ) / 2 :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.ae7d59a66c90 from=translated src=- shape=a8189094 vocab=2e27f360
-/
@[simp]
theorem toQsqrtdHom_mk_re (d x y : ℤ) :
    (toQsqrtdHom d (⟨x, y⟩ : ZOnePlusSqrtdOverTwo d)).re = (x : ℚ) + (y : ℚ) / 2 :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.7267705778ba from=translated src=- shape=537625d5 vocab=2410ae00
-/
@[simp]
theorem toQsqrtdHom_mk_im (d x y : ℤ) :
    (toQsqrtdHom d (⟨x, y⟩ : ZOnePlusSqrtdOverTwo d)).im = (y : ℚ) / 2 :=
  rfl

/-- The canonical map `toQsqrtdHom` is injective.
@isnad1 id=injectiv.0h1v.s6.8d267cc5af25 from=translated src=- shape=401465cd vocab=5521eef8
-/
theorem toQsqrtdHom_injective (d : ℤ) : Function.Injective (toQsqrtdHom d) := by
  intro x y hxy
  -- Equality of images first identifies the `ω`-coefficients from the imaginary parts,
  -- then the constant terms from the real parts.
  have himHalf : (x.im : ℚ) / 2 = (y.im : ℚ) / 2 := by
    simpa [toQsqrtdHom, toQsqrtdFun] using congrArg QuadraticAlgebra.im hxy
  have himQ : (x.im : ℚ) = (y.im : ℚ) := by
    nlinarith [himHalf]
  have hreHalf : (x.re : ℚ) + (x.im : ℚ) / 2 = (y.re : ℚ) + (y.im : ℚ) / 2 := by
    simpa [toQsqrtdHom, toQsqrtdFun] using congrArg QuadraticAlgebra.re hxy
  have hreQ : (x.re : ℚ) = (y.re : ℚ) := by
    nlinarith [hreHalf, himQ]
  ext
  · exact_mod_cast hreQ
  · exact_mod_cast himQ

/-- Candidate carrier set of `ℤ[(1 + √(1 + 4d))/2]` inside `Q(√(1 + 4d))`.-/
def carrierSet (d : ℤ) : Set (Qsqrtd (qParam d)) := Set.range (toQsqrtdFun d)

/-- A half-integer element belongs to the `ℤ[(1 + √(1+4k))/2]` carrier iff the two
numerators have the same parity.
@isnad1 id=iff.0h3v.s6.f4220141119a from=translated src=- shape=502936ba vocab=4265add7
-/
theorem halfInt_mem_carrierSet_iff_same_parity (k a' b' : ℤ) :
    (∃ z : ZOnePlusSqrtdOverTwo k,
      toQsqrtdFun k z = RingOfIntegers.halfInt (1 + 4 * k) a' b') ↔
      a' % 2 = b' % 2 := by
  constructor
  · rintro ⟨z, hz⟩
    -- If `(a' + b'√d)/2 = r + sω`, then necessarily `s = b'`
    -- and `a' = 2r + b'`, so `a'` and `b'` have the same parity.
    have him : z.im / 2 = (b' : ℚ) / 2 := by
      simpa [toQsqrtdFun, RingOfIntegers.halfInt] using
        congrArg QuadraticAlgebra.im hz
    have hbq : z.im = (b' : ℚ) := by
      nlinarith [him]
    have hreq : z.re + z.im / 2 = (a' : ℚ) / 2 := by
      simpa [toQsqrtdFun, RingOfIntegers.halfInt] using
        congrArg QuadraticAlgebra.re hz
    have haq : 2 * z.re + z.im = (a' : ℚ) := by
      nlinarith [hreq]
    have ha : 2 * z.re + z.im = a' := by exact_mod_cast haq
    have hb : z.im = b' := by exact_mod_cast hbq
    have ha' : 2 * z.re + b' = a' := by simpa [hb] using ha
    omega
  · intro hpar
    -- Conversely, same parity means `a' - b' = 2t`, so
    -- `(a' + b'√d)/2 = t + b' * ω`.
    have hmod : (a' - b') % 2 = 0 := by
      omega
    have hdiv : (2 : ℤ) ∣ (a' - b') := Int.dvd_iff_emod_eq_zero.mpr hmod
    rcases hdiv with ⟨t, ht⟩
    have hrepr : a' = 2 * t + b' := by
      omega
    refine ⟨⟨t, b'⟩, ?_⟩
    ext
    · simp [toQsqrtdFun, RingOfIntegers.halfInt, hrepr]
      ring
    · simp [toQsqrtdFun, RingOfIntegers.halfInt]

/-- Equivalent set-membership form of `halfInt_mem_carrierSet_iff_same_parity`.
@isnad1 id=iff.0h3v.s6.2fb115f45117 from=translated src=- shape=eb48e910 vocab=b572f210
-/
theorem halfInt_mem_carrierSet_iff_same_parity_set (k a' b' : ℤ) :
    RingOfIntegers.halfInt (1 + 4 * k) a' b' ∈ carrierSet k ↔
      a' % 2 = b' % 2 :=
  by simpa [carrierSet] using (halfInt_mem_carrierSet_iff_same_parity k a' b')

end Tengoku.QuadraticNumberFields.ZOnePlusSqrtdOverTwo
-- Tengoku: root names of this library moved to Tengoku.QuadraticNumberFields so they do not collide with other libraries (generated)
