import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ComponentGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime

open ModularCurve Finset

namespace P2mS3VertexGen

variable {ι : Type*} [Fintype ι]

def diffVec [DecidableEq ι] (s s₀ : ι) : characterLattice ι :=
  ⟨Pi.single s 1 - Pi.single s₀ 1, by
    rw [mem_characterLattice]
    simp [Finset.sum_sub_distrib]⟩

/--
@isnad1 id=eq.0h3v.s7.419e36dd0563 from=translated src=- shape=066ba987 vocab=dcb81d4d
-/
@[scoped simp] theorem coe_diffVec [DecidableEq ι] (s s₀ : ι) :
    (diffVec s s₀ : ι → ℤ) = Pi.single s 1 - Pi.single s₀ 1 := rfl

theorem eq_sum_smul_diffVec [DecidableEq ι] (s₀ : ι) (D : characterLattice ι) :
    D = ∑ s, (D : ι → ℤ) s • diffVec s s₀ := by
  apply Subtype.ext
  have hD : ∑ s, (D : ι → ℤ) s = 0 := mem_characterLattice.mp D.2
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, coe_diffVec, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, hD, zero_smul, sub_zero]
  ext x
  simp [Finset.sum_apply, Pi.single_apply]

/--
@isnad1 id=eq.0h4v.s10.3deff1fb6182 from=translated src=- shape=559eac4d vocab=d6516853
-/
theorem dual_apply_eq_sum [DecidableEq ι] (s₀ : ι) (φ : Module.Dual ℤ (characterLattice ι))
    (D : characterLattice ι) :
    φ D = ∑ s, (D : ι → ℤ) s * φ (diffVec s s₀) := by
  conv_lhs => rw [eq_sum_smul_diffVec s₀ D]
  rw [map_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [map_smul, smul_eq_mul]

/--
@isnad1 id=ex.1h3v.s5.ee0a03cf7e18 from=translated src=- shape=468cd428 vocab=a8c341ad
-/
theorem exists_forall_dvd_sub (e : ι → ℕ) (he : Pairwise fun s t => (e s).Coprime (e t))
    (v : ι → ℤ) : ∃ c : ℤ, ∀ s, (e s : ℤ) ∣ v s - c := by
  have hI : Pairwise (Function.onFun IsCoprime fun s => Ideal.span ({(e s : ℤ)} : Set ℤ)) := by
    intro s t hst
    show IsCoprime (Ideal.span {(e s : ℤ)}) (Ideal.span {(e t : ℤ)})
    rw [Ideal.isCoprime_span_singleton_iff]
    exact Nat.isCoprime_iff_coprime.mpr (he hst)
  obtain ⟨c, hc⟩ := Ideal.exists_forall_sub_mem_ideal hI v
  refine ⟨c, fun s => ?_⟩
  have h := Ideal.mem_span_singleton.mp (hc s)
  rw [← dvd_neg, neg_sub]
  exact h

abbrev coord (s₀ : ι) : Module.Dual ℤ (characterLattice ι) :=
  (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype

/--
@isnad1 id=eq.0h3v.s9.e8e0135519f2 from=translated src=- shape=cf28107f vocab=9c2fce7b
-/
theorem coord_apply (s₀ : ι) (D : characterLattice ι) : coord s₀ D = (D : ι → ℤ) s₀ := rfl

/--
@isnad1 id=ex.1h4v.s13.e81d58438911 from=translated src=- shape=8b9d7c9a vocab=6c6c5474
-/
theorem exists_gramMap_eq (e : ι → ℕ) (he : Pairwise fun s t => (e s).Coprime (e t))
    (s₀ : ι) (φ : Module.Dual ℤ (characterLattice ι)) :
    ∃ (k : ℤ) (D : characterLattice ι), gramMap e D = φ - k • ((e s₀ : ℤ) • coord s₀) := by
  classical

  set v : ι → ℤ := fun s => φ (diffVec s s₀) with hv
  obtain ⟨c, hc⟩ := exists_forall_dvd_sub e he v
  choose m hm using hc

  set k : ℤ := ∑ s, m s with hk
  let D₀ : ι → ℤ := fun s => m s - k * (Pi.single s₀ (1 : ℤ) : ι → ℤ) s
  have hD₀ : D₀ ∈ characterLattice ι := by
    rw [mem_characterLattice]
    simp only [D₀, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_pi_single']
    simp [hk]
  refine ⟨k, ⟨D₀, hD₀⟩, ?_⟩
  apply LinearMap.ext
  intro D'
  have hD' : ∑ s, (D' : ι → ℤ) s = 0 := mem_characterLattice.mp D'.2
  rw [gramMap_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    coord_apply, dual_apply_eq_sum s₀ φ D', smul_eq_mul, smul_eq_mul]

  have hvs : ∀ s, φ (diffVec s s₀) = c + (e s : ℤ) * m s := fun s => by
    have := hm s; simp only [hv] at this; linarith
  simp only [hvs, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hD', zero_mul, zero_add]

  simp only [D₀, sub_mul, mul_sub, Finset.sum_sub_distrib]
  have h1 : ∑ s, (e s : ℤ) * (k * (Pi.single s₀ (1 : ℤ) : ι → ℤ) s * (D' : ι → ℤ) s) =
      k * ((e s₀ : ℤ) * (D' : ι → ℤ) s₀) := by
    rw [Finset.sum_eq_single s₀]
    · simp; ring
    · intro s _ hs; simp [hs]
    · intro h; exact absurd (Finset.mem_univ s₀) h
  rw [h1]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

/--
@isnad1 id=eq.1h3v.s14.295610d2987f from=translated src=- shape=9fbe28d1 vocab=4aae8f0a
-/
theorem zmultiples_eq_top (e : ι → ℕ) (he : Pairwise fun s t => (e s).Coprime (e t)) (s₀ : ι) :
    AddSubgroup.zmultiples (componentGroupProj e ((e s₀ : ℤ) • coord s₀)) = ⊤ := by
  rw [AddSubgroup.eq_top_iff']
  intro y
  obtain ⟨φ, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨k, D, hD⟩ := exists_gramMap_eq e he s₀ φ
  have hφ : φ = k • ((e s₀ : ℤ) • coord s₀) + gramMap e D := by rw [hD]; abel
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨k, ?_⟩
  have h0 : (LinearMap.range (gramMap e)).mkQ (gramMap e D) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self _ D
  rw [hφ, map_add, h0, add_zero]
  simp only [map_zsmul]

end P2mS3VertexGen
open scoped _root_.P2MW.S_ModularCurve_zmultiples_componentGroupProj_smul_coord_eq_top_of_pairwise_coprime.P2mS3VertexGen

/--
@isnad1 id=eq.1h3v.s14.3c230d40e1f6 from=translated src=- shape=71b3c0ab vocab=bd113e4e
-/
theorem solution
    {ι : Type*} [Fintype ι] (e : ι → ℕ) (he : Pairwise fun s t => (e s).Coprime (e t))
    (s₀ : ι) :
    AddSubgroup.zmultiples (componentGroupProj e ((e s₀ : ℤ) •
      (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype)) = ⊤ :=
  P2mS3VertexGen.zmultiples_eq_top e he s₀
