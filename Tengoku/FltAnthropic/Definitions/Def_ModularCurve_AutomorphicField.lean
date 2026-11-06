import Tengoku.Seed.NumberTheory.ModularForms.Basic
import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped Manifold MatrixGroups Topology

namespace ModularCurve

def holRing : Subalgebra ℂ (ℍ → ℂ) where
  carrier := {f | MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f}
  mul_mem' hf hg := hf.mul hg
  one_mem' := mdifferentiable_const
  add_mem' hf hg := hf.add hg
  zero_mem' := mdifferentiable_const
  algebraMap_mem' _ := mdifferentiable_const

/--
@isnad1 id=nontrivi.0h0v.s6.62c238d143f6 from=translated src=- shape=77cbcbdc vocab=c23889b1
-/
instance holRing.instNontrivial : Nontrivial ↥holRing :=
  ⟨⟨0, 1, fun h => by simpa using congrArg (fun f : ↥holRing => (f : ℍ → ℂ) UpperHalfPlane.I) h⟩⟩

/--
@isnad1 id=nozerodi.0h0v.s8.24136ec23393 from=translated src=- shape=77cbcbdc vocab=ce196510
-/
instance holRing.instNoZeroDivisors : NoZeroDivisors ↥holRing where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} h := by
    have h' : (f : ℍ → ℂ) * (g : ℍ → ℂ) = 0 := by simpa using congrArg (fun x : ↥holRing => (x : ℍ → ℂ)) h
    rcases (UpperHalfPlane.mul_eq_zero_iff f.2 g.2).1 h' with h0 | h0
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr (Subtype.ext h0)

/--
@isnad1 id=isdomain.0h0v.s6.dcadc0e21e95 from=translated src=- shape=77cbcbdc vocab=d2b5efa0
-/
instance holRing.instIsDomain : IsDomain ↥holRing := NoZeroDivisors.to_isDomain _

end ModularCurve

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

def toHolRing (f : ModularForm Γ k) : ↥ModularCurve.holRing := ⟨f, f.holo'⟩

/--
@isnad1 id=eq.0h3v.s7.281d809ae893 from=translated src=- shape=b610c0ab vocab=51b95b9a
-/
@[simp] theorem coe_toHolRing (f : ModularForm Γ k) : (f.toHolRing : ℍ → ℂ) = f := rfl

/--
@isnad1 id=iff.0h3v.s8.3235195c2f72 from=translated src=- shape=9a5235de vocab=75e58264
-/
theorem toHolRing_eq_zero_iff (f : ModularForm Γ k) : f.toHolRing = 0 ↔ (f : ℍ → ℂ) = 0 := by
  rw [← coe_toHolRing f]
  exact (ZeroMemClass.coe_eq_zero).symm

/--
@isnad1 id=eq.0h4v.s9.92312bc46e41 from=translated src=- shape=4c4655c9 vocab=11ce77d3
-/
theorem toHolRing_add (f g : ModularForm Γ k) : (f + g).toHolRing = f.toHolRing + g.toHolRing := rfl

/--
@isnad1 id=eq.0h3v.s8.03dc276c1a2f from=translated src=- shape=7b1dbd94 vocab=189967be
-/
theorem toHolRing_neg (f : ModularForm Γ k) : (-f).toHolRing = -f.toHolRing := rfl

/--
@isnad1 id=eq.0h5v.s9.a7f8105af5bf from=translated src=- shape=66946a22 vocab=6b584493
-/
theorem toHolRing_mul [Γ.HasDetPlusMinusOne] {k₁ k₂ : ℤ} (f : ModularForm Γ k₁) (g : ModularForm Γ k₂) :
    (f.mul g).toHolRing = f.toHolRing * g.toHolRing :=
  Subtype.ext (coe_mul f g)

end ModularForm

namespace ModularCurve

section

variable (Γ : Subgroup (GL (Fin 2) ℝ))

def automorphicRatioSet : Set (FractionRing ↥holRing) :=
  {x | ∃ (k : ℤ) (g h : ModularForm Γ k), (h : ℍ → ℂ) ≠ 0 ∧
    x = algebraMap (↥holRing) (FractionRing ↥holRing) g.toHolRing /
          algebraMap (↥holRing) (FractionRing ↥holRing) h.toHolRing}

variable {Γ}

private theorem algebraMap_toHolRing_ne_zero {k : ℤ} {h : ModularForm Γ k} (hh : (h : ℍ → ℂ) ≠ 0) :
    algebraMap (↥holRing) (FractionRing ↥holRing) h.toHolRing ≠ 0 := by
  intro h0
  apply hh
  have : h.toHolRing = 0 :=
    (IsFractionRing.injective (↥holRing) (FractionRing ↥holRing)) (by rw [h0, RingHom.map_zero])
  exact (ModularForm.toHolRing_eq_zero_iff h).1 this

private theorem neg_mem_automorphicRatioSet {x : FractionRing ↥holRing}
    (hx : x ∈ automorphicRatioSet Γ) : -x ∈ automorphicRatioSet Γ := by
  obtain ⟨k, g, h, hh, rfl⟩ := hx
  refine ⟨k, -g, h, hh, ?_⟩
  rw [ModularForm.toHolRing_neg, RingHom.map_neg, neg_div]

variable [Γ.HasDetOne]

private theorem coe_ne_zero_of_mul {k₁ k₂ : ℤ} {h₁ : ModularForm Γ k₁} {h₂ : ModularForm Γ k₂}
    (hh₁ : (h₁ : ℍ → ℂ) ≠ 0) (hh₂ : (h₂ : ℍ → ℂ) ≠ 0) : ((h₁.mul h₂ : ModularForm Γ (k₁ + k₂)) : ℍ → ℂ) ≠ 0 := by
  rw [ModularForm.coe_mul]
  intro h0
  rcases (UpperHalfPlane.mul_eq_zero_iff h₁.holo' h₂.holo').1 h0 with h | h
  · exact hh₁ h
  · exact hh₂ h

private theorem one_mem_automorphicRatioSet : (1 : FractionRing ↥holRing) ∈ automorphicRatioSet Γ := by
  have h1 : ((1 : ModularForm Γ 0) : ℍ → ℂ) ≠ 0 := by
    rw [ModularForm.one_coe_eq_one]; exact one_ne_zero
  refine ⟨0, 1, 1, h1, ?_⟩
  rw [div_self (algebraMap_toHolRing_ne_zero h1)]

private theorem zero_mem_automorphicRatioSet : (0 : FractionRing ↥holRing) ∈ automorphicRatioSet Γ := by
  have h1 : ((1 : ModularForm Γ 0) : ℍ → ℂ) ≠ 0 := by
    rw [ModularForm.one_coe_eq_one]; exact one_ne_zero
  refine ⟨0, 0, 1, h1, ?_⟩
  have : (0 : ModularForm Γ 0).toHolRing = 0 := rfl
  rw [this, RingHom.map_zero, zero_div]

private theorem mul_mem_automorphicRatioSet {x y : FractionRing ↥holRing}
    (hx : x ∈ automorphicRatioSet Γ) (hy : y ∈ automorphicRatioSet Γ) : x * y ∈ automorphicRatioSet Γ := by
  obtain ⟨k, g, h, hh, rfl⟩ := hx
  obtain ⟨k', g', h', hh', rfl⟩ := hy
  refine ⟨k + k', g.mul g', h.mul h', coe_ne_zero_of_mul hh hh', ?_⟩
  rw [ModularForm.toHolRing_mul, ModularForm.toHolRing_mul, RingHom.map_mul, RingHom.map_mul, div_mul_div_comm]

private theorem add_mem_automorphicRatioSet {x y : FractionRing ↥holRing}
    (hx : x ∈ automorphicRatioSet Γ) (hy : y ∈ automorphicRatioSet Γ) : x + y ∈ automorphicRatioSet Γ := by
  obtain ⟨k, g, h, hh, rfl⟩ := hx
  obtain ⟨k', g', h', hh', rfl⟩ := hy
  refine ⟨k + k', g.mul h' + h.mul g', h.mul h', coe_ne_zero_of_mul hh hh', ?_⟩
  rw [ModularForm.toHolRing_add, ModularForm.toHolRing_mul, ModularForm.toHolRing_mul,
    ModularForm.toHolRing_mul, RingHom.map_add, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul,
    div_add_div _ _ (algebraMap_toHolRing_ne_zero hh) (algebraMap_toHolRing_ne_zero hh')]

private theorem inv_mem_automorphicRatioSet {x : FractionRing ↥holRing}
    (hx : x ∈ automorphicRatioSet Γ) : x⁻¹ ∈ automorphicRatioSet Γ := by
  obtain ⟨k, g, h, hh, rfl⟩ := hx
  by_cases hg : (g : ℍ → ℂ) = 0
  · have : g.toHolRing = 0 := (ModularForm.toHolRing_eq_zero_iff g).2 hg
    rw [this, RingHom.map_zero, zero_div, inv_zero]
    exact zero_mem_automorphicRatioSet
  · exact ⟨k, h, g, hg, by rw [inv_div]⟩

variable (Γ)

def automorphicField : Subfield (FractionRing ↥holRing) where
  carrier := automorphicRatioSet Γ
  mul_mem' := mul_mem_automorphicRatioSet
  one_mem' := one_mem_automorphicRatioSet
  add_mem' := add_mem_automorphicRatioSet
  zero_mem' := zero_mem_automorphicRatioSet
  neg_mem' := neg_mem_automorphicRatioSet
  inv_mem' _ := inv_mem_automorphicRatioSet

variable {Γ}

variable (Γ)

def automorphicField.constHom : ℂ →+* ↥(automorphicField Γ) :=
  ((algebraMap (↥holRing) (FractionRing ↥holRing)).comp (algebraMap ℂ ↥holRing)).codRestrict
    (automorphicField Γ) (fun c => by
      have h1 : ((1 : ModularForm Γ 0) : ℍ → ℂ) ≠ 0 := by
        rw [ModularForm.one_coe_eq_one]; exact one_ne_zero
      refine ⟨0, ModularForm.const c, 1, h1, ?_⟩
      have e1 : (1 : ModularForm Γ 0).toHolRing = 1 := Subtype.ext ModularForm.one_coe_eq_one
      have e2 : (ModularForm.const c : ModularForm Γ 0).toHolRing = algebraMap ℂ ↥holRing c :=
        Subtype.ext (funext fun τ => by simp [Algebra.algebraMap_eq_smul_one])
      rw [e1, RingHom.map_one, div_one, e2]
      rfl)

instance automorphicField.instAlgebra : Algebra ℂ ↥(automorphicField Γ) :=
  (automorphicField.constHom Γ).toAlgebra

/--
@isnad1 id=eq.0h2v.s15.8a62a6e08c0d from=translated src=- shape=d1b0fba4 vocab=6ede6735
-/
theorem automorphicField.algebraMap_def (c : ℂ) :
    ((algebraMap ℂ ↥(automorphicField Γ) c : ↥(automorphicField Γ)) : FractionRing ↥holRing) =
      algebraMap (↥holRing) (FractionRing ↥holRing) (algebraMap ℂ ↥holRing c) := rfl

end

end ModularCurve

end
