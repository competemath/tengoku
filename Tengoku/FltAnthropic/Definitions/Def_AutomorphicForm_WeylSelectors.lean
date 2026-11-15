import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.Seed.MeasureTheory.Measure.Haar.DistribChar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open MeasureTheory NumberField NumberField.AdelicBox IsDedekindDomain
open scoped Classical Pointwise

namespace AutomorphicForm.WeylIntegrable

section Generic

variable {A : Type*} [CommRing A] {ε y z x : A}

structure SelRel (ε y z x : A) : Prop where
  idem : ε * ε = ε
  yz : y * z = 1
  small : (1 - ε) * y = 1 - ε
  big : ε * y = ε * x

def yUnit (h : SelRel ε y z x) : Aˣ :=
  ⟨y, ε * z + (1 - ε), by linear_combination ε * h.yz + h.small, by linear_combination ε * h.yz + h.small⟩

/--
@isnad1 id=eq.1h5v.s5.b2c5ef512970 from=translated src=- shape=8594df3b vocab=d392e9b5
-/
@[simp] theorem coe_yUnit (h : SelRel ε y z x) : (yUnit h : A) = y := rfl
/--
@isnad1 id=eq.1h5v.s6.3adfb51aa3f9 from=translated src=- shape=8c8c88e2 vocab=44266376
-/
theorem coe_yUnit_inv (h : SelRel ε y z x) : (((yUnit h)⁻¹ : Aˣ) : A) = ε * z + (1 - ε) := rfl

end Generic

section Adelic

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

def toAdele' (a : 𝔸∞) (b : 𝔸f) : 𝔸 := (a, b)

def finOfIntegral (f : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : 𝔸f :=
  show RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from
    RestrictedProduct.mk f (.of_forall hf)

/--
@isnad1 id=eq.1h3v.s8.321a0096b634 from=translated src=- shape=378a198f vocab=1a756761
-/
@[simp] theorem finOfIntegral_apply (f : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) : finOfIntegral F f hf v = f v := rfl

def BigInf (a : 𝔸∞) (w : InfinitePlace F) : Prop := 1 < ‖a w‖

def BigFin (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : Prop := b v ∉ v.adicCompletionIntegers F

omit [NumberField F] in
/--
@isnad1 id=ne.1h3v.s6.4ecd85142005 from=translated src=- shape=4f0a0a97 vocab=39e3e17e
-/
theorem ne_zero_of_bigInf {a : 𝔸∞} {w : InfinitePlace F} (h : BigInf F a w) : a w ≠ 0 := by
  intro h0; rw [BigInf, h0, norm_zero] at h; exact (not_lt.mpr zero_le_one) h

/--
@isnad1 id=lt.1h3v.s8.b84d31710c03 from=translated src=- shape=ad27e61f vocab=798bd856
-/
theorem one_lt_valued_of_bigFin {b : 𝔸f} {v : HeightOneSpectrum (𝓞 F)} (h : BigFin F b v) : 1 < Valued.v (b v) := by
  rw [BigFin, HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at h; exact h

/--
@isnad1 id=ne.1h3v.s7.f0bb93cdd0b3 from=translated src=- shape=cfa094e0 vocab=8a6d12c7
-/
theorem ne_zero_of_bigFin {b : 𝔸f} {v : HeightOneSpectrum (𝓞 F)} (h : BigFin F b v) : b v ≠ 0 := by
  intro h0; have := one_lt_valued_of_bigFin F h; rw [h0, map_zero] at this; exact (not_lt.mpr zero_le_one) this

/--
@isnad1 id=mem.1h3v.s8.1262201e143e from=translated src=- shape=3bec0db2 vocab=791bd015
-/
theorem inv_mem_of_bigFin {b : 𝔸f} {v : HeightOneSpectrum (𝓞 F)} (h : BigFin F b v) : (b v)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact ((Valuation.one_lt_val_iff _ (ne_zero_of_bigFin F h)).mp (one_lt_valued_of_bigFin F h)).le

def selE (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then 1 else 0)
  (finOfIntegral F (fun v => if BigFin F b v then 1 else 0) fun v => by split_ifs <;> simp [one_mem, zero_mem])

def selZ (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then (a w)⁻¹ else 1)
  (finOfIntegral F (fun v => if BigFin F b v then (b v)⁻¹ else 1) fun v => by
    split_ifs with h
    · exact inv_mem_of_bigFin F h
    · exact one_mem _)

def selY (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then a w else 1)
  (show RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from
    RestrictedProduct.mk (fun v => if BigFin F b v then b v else 1)
      ((show RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
          (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from b).eventually.mono
        fun v hv => by
          rw [ite_eq_right (show ¬ BigFin F b v from not_not.mpr hv)]
          exact one_mem _))

/--
@isnad1 id=eq.0h4v.s7.ae1adae83bc8 from=translated src=- shape=3469b050 vocab=d1c51ac1
-/
theorem selE_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : (selE F a b).1 w = if BigInf F a w then 1 else 0 := rfl
/--
@isnad1 id=eq.0h4v.s8.b0f9bf4e734a from=translated src=- shape=91d18997 vocab=e8ecf120
-/
theorem selE_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selE F a b).2 v = if BigFin F b v then 1 else 0 := rfl
/--
@isnad1 id=eq.0h4v.s6.96d36243c5be from=translated src=- shape=7470c6c5 vocab=09eb4c51
-/
theorem selY_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : (selY F a b).1 w = if BigInf F a w then a w else 1 := rfl
/--
@isnad1 id=eq.0h4v.s8.a6df9cbb9ae6 from=translated src=- shape=cf7f215d vocab=7ad7e304
-/
theorem selY_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selY F a b).2 v = if BigFin F b v then b v else 1 := rfl
/--
@isnad1 id=eq.0h4v.s7.3cb25c842e17 from=translated src=- shape=82df0f5f vocab=0a3691a0
-/
theorem selZ_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : (selZ F a b).1 w = if BigInf F a w then (a w)⁻¹ else 1 := rfl
/--
@isnad1 id=eq.0h4v.s8.71f7fdf28bf5 from=translated src=- shape=b3e82b02 vocab=e0093935
-/
theorem selZ_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selZ F a b).2 v = if BigFin F b v then (b v)⁻¹ else 1 := rfl
/--
@isnad1 id=eq.0h3v.s5.cbc777c177d8 from=translated src=- shape=15feca4c vocab=a19dddec
-/
theorem toAdele'_fst (a : 𝔸∞) (b : 𝔸f) : (toAdele' F a b).1 = a := rfl
/--
@isnad1 id=eq.0h3v.s6.c7789b667513 from=translated src=- shape=0c54870f vocab=70c2b5f6
-/
theorem toAdele'_snd (a : 𝔸∞) (b : 𝔸f) : (toAdele' F a b).2 = b := rfl

/--
@isnad1 id=eq.0h4v.s8.67d3ee768e34 from=translated src=- shape=bfb00594 vocab=d265dd1b
-/
theorem mul_fst_apply (u u' : 𝔸) (w : InfinitePlace F) : (u * u').1 w = u.1 w * u'.1 w := rfl
/--
@isnad1 id=eq.0h4v.s9.a4c8c18e2572 from=translated src=- shape=167fb59f vocab=c511cb5a
-/
theorem mul_snd_apply (u u' : 𝔸) (v : HeightOneSpectrum (𝓞 F)) : (u * u').2 v = u.2 v * u'.2 v := rfl
/--
@isnad1 id=eq.0h4v.s8.c7cd2d594193 from=translated src=- shape=bfb00594 vocab=b740cec6
-/
theorem sub_fst_apply (u u' : 𝔸) (w : InfinitePlace F) : (u - u').1 w = u.1 w - u'.1 w := rfl
/--
@isnad1 id=eq.0h4v.s9.33c3c4653294 from=translated src=- shape=167fb59f vocab=5dbd8a75
-/
theorem sub_snd_apply (u u' : 𝔸) (v : HeightOneSpectrum (𝓞 F)) : (u - u').2 v = u.2 v - u'.2 v := rfl
/--
@isnad1 id=eq.0h2v.s7.4cb71e142a0e from=translated src=- shape=d0e6ebec vocab=cf93cff9
-/
theorem one_fst_apply (w : InfinitePlace F) : (1 : 𝔸).1 w = 1 := rfl
/--
@isnad1 id=eq.0h2v.s8.bd4d1c45d914 from=translated src=- shape=fd7d0a19 vocab=aa79e485
-/
theorem one_snd_apply (v : HeightOneSpectrum (𝓞 F)) : (1 : 𝔸).2 v = 1 := rfl

/--
@isnad1 id=eq.2h3v.s8.e85c2bebe4ce from=translated src=- shape=c35a655a vocab=03f01c9b
-/
theorem adele_ext {u u' : 𝔸} (h1 : ∀ w, u.1 w = u'.1 w) (h2 : ∀ v, u.2 v = u'.2 v) : u = u' :=
  Prod.ext (funext h1) (Subtype.ext (funext h2))

/--
@isnad1 id=selrel.0h3v.s6.eb6c7e2bdb88 from=translated src=- shape=386b8e94 vocab=ade63d9a
-/
theorem selRel (a : 𝔸∞) (b : 𝔸f) : SelRel (selE F a b) (selY F a b) (selZ F a b) (toAdele' F a b) where
  idem := adele_ext F (fun w => by rw [mul_fst_apply, selE_fst]; split_ifs <;> simp)
    (fun v => by rw [mul_snd_apply, selE_snd]; split_ifs <;> simp)
  yz := adele_ext F
    (fun w => by
      rw [mul_fst_apply, selY_fst, selZ_fst, one_fst_apply]
      split_ifs with h
      · exact mul_inv_cancel₀ (ne_zero_of_bigInf F h)
      · exact mul_one 1)
    (fun v => by
      rw [mul_snd_apply, selY_snd, selZ_snd, one_snd_apply]
      split_ifs with h
      · exact mul_inv_cancel₀ (ne_zero_of_bigFin F h)
      · exact mul_one 1)
  small := adele_ext F
    (fun w => by rw [mul_fst_apply, sub_fst_apply, one_fst_apply, selE_fst, selY_fst]; split_ifs <;> simp)
    (fun v => by rw [mul_snd_apply, sub_snd_apply, one_snd_apply, selE_snd, selY_snd]; split_ifs <;> simp)
  big := adele_ext F
    (fun w => by rw [mul_fst_apply, mul_fst_apply, selE_fst, selY_fst, toAdele'_fst]; split_ifs <;> simp)
    (fun v => by rw [mul_snd_apply, mul_snd_apply, selE_snd, selY_snd, toAdele'_snd]; split_ifs <;> simp)

end Adelic

section Lattice

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

def intLattice : AddSubgroup 𝔸f where
  carrier := integralFiniteAdeles (𝓞 F) F
  zero_mem' := fun _ => zero_mem _
  add_mem' hx hy := fun v => add_mem (hx v) (hy v)
  neg_mem' hx := fun v => neg_mem (hx v)

/--
@isnad1 id=eq.0h1v.s7.916bc593ace8 from=translated src=- shape=e393e868 vocab=0aa36d87
-/
@[simp] theorem coe_intLattice : (intLattice F : Set 𝔸f) = integralFiniteAdeles (𝓞 F) F := rfl

def dilate (y : (𝔸f)ˣ) : AddSubgroup 𝔸f := (intLattice F).map (DistribSMul.toAddMonoidHom 𝔸f (y : 𝔸f))

/--
@isnad1 id=eq.0h2v.s9.97547f506bb1 from=translated src=- shape=6fc2c43d vocab=41675723
-/
theorem coe_dilate (y : (𝔸f)ˣ) : (dilate F y : Set 𝔸f) = (y : 𝔸f) • integralFiniteAdeles (𝓞 F) F := by
  ext z; simp [dilate, Set.mem_smul_set]

/--
@isnad1 id=eq.0h3v.s8.de740c4ebfb7 from=translated src=- shape=e7ba58dc vocab=3383c126
-/
theorem snd_mul (x y : 𝔸) : (x * y).2 = x.2 * y.2 := rfl

def finPart (Y : (𝔸)ˣ) : (𝔸f)ˣ where
  val := (Y : 𝔸).2
  inv := ((Y⁻¹ : (𝔸)ˣ) : 𝔸).2
  val_inv := by rw [← snd_mul, Units.mul_inv]; rfl
  inv_val := by rw [← snd_mul, Units.inv_mul]; rfl

end Lattice

section Modulus

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

def Dy (x : 𝔸) : ℝ := (distribHaarChar 𝔸 (yUnit (selRel F x.1 x.2)) : ℝ)

end Modulus

end AutomorphicForm.WeylIntegrable

end
