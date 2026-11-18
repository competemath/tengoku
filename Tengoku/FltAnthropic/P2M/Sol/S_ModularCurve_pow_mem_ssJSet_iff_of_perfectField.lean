import Tengoku.Seed.FieldTheory.Perfect
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_SupersingularModuli
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_pow_mem_ssJSet_iff_of_perfectField.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`, 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_pow_mem_ssJSet_iff_of_perfectField

open _root_.ModularCurve

set_option autoImplicit false

namespace ModularCurve
export _root_.ModularCurve (ssJSet mem_ssJSet_iff)
open _root_.ModularCurve

open WeierstrassCurve WeierstrassCurve.Affine

section transport

variable {F : Type*} {k : Type*} [Field F] [Field k] (f : F →+* k) {W₀ : WeierstrassCurve F}

/--
@isnad1 id=eq.4h6v.s6.ddf2db84fcca from=translated src=- shape=7ae36cae vocab=a6578b85
-/
theorem solution_aux_some_congr {V : Affine k} {x₁ y₁ x₂ y₂ : k} (hx : x₁ = x₂)
    (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

def solution_aux_map : W₀.toAffine.Point → (W₀.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h)

/--
@isnad1 id=eq.0h4v.s7.e330d4f2652e from=translated src=- shape=e18a98fd vocab=f905dbeb
-/
@[scoped simp]
lemma solution_aux_map_zero : solution_aux_map f (0 : W₀.toAffine.Point) = 0 :=
  rfl

/--
@isnad1 id=eq.1h6v.s7.31bafd0c581d from=translated src=- shape=f0e530fd vocab=24828739
-/
lemma solution_aux_map_some {x y : F} (h : W₀.toAffine.Nonsingular x y) :
    solution_aux_map f (.some x y h)
      = .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h) :=
  rfl

/--
@isnad1 id=injectiv.0h4v.s6.cd5c34d3c1ae from=translated src=- shape=3ac69e5b vocab=620be900
-/
lemma solution_aux_map_injective :
    Function.Injective (solution_aux_map f (W₀ := W₀)) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Affine.Point.some_ne_zero _)
  · exact absurd h (Affine.Point.some_ne_zero _)
  · rw [solution_aux_map_some, solution_aux_map_some, Affine.Point.some.injEq] at h
    exact solution_aux_some_congr (f.injective h.1) (f.injective h.2) _ _

/--
@isnad1 id=eq.0h6v.s7.a32df26022a0 from=translated src=- shape=7587a6b5 vocab=be5ebd3e
-/
theorem solution_aux_map_add [DecidableEq F] [DecidableEq k] (P Q : W₀.toAffine.Point) :
    solution_aux_map f (P + Q) = solution_aux_map f P + solution_aux_map f Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W₀.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, solution_aux_map_zero, solution_aux_map_some,
      solution_aux_map_some,
      Affine.Point.add_of_Y_eq (congrArg f hxy.1) (by rw [hxy.2, Affine.map_negY])]
  · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W₀.map f).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨hx, hy⟩
      rw [Affine.map_negY] at hy
      exact hxy ⟨f.injective hx, f.injective hy⟩
    rw [Affine.Point.add_some hxy, solution_aux_map_some, solution_aux_map_some,
      solution_aux_map_some, Affine.Point.add_some hxy']
    exact solution_aux_some_congr (by rw [Affine.map_slope, Affine.map_addX])
      (by rw [Affine.map_slope, Affine.map_addY]) _ _

def solution_aux_hom [DecidableEq F] [DecidableEq k] :
    W₀.toAffine.Point →+ (W₀.map f).toAffine.Point :=
  AddMonoidHom.mk' (solution_aux_map f) (solution_aux_map_add f)

/--
@isnad1 id=eq.0h5v.s8.95a36cfdb402 from=translated src=- shape=bebf681d vocab=8116dc31
-/
@[scoped simp] lemma solution_aux_hom_apply [DecidableEq F] [DecidableEq k] (P : W₀.toAffine.Point) :
    solution_aux_hom f P = solution_aux_map f P := rfl

end transport

/--
@isnad1 id=mem.1h4v.s7.e9f881e0bc38 from=translated src=- shape=263cb2cf vocab=8e742770
-/
theorem solution_aux_ringEquiv_mem {K : Type*} [Field K] [DecidableEq K] (p : ℕ)
    (σ : K ≃+* K) {a : K} (ha : a ∈ ssJSet p K) : σ a ∈ ssJSet p K := by
  rw [mem_ssJSet_iff] at ha ⊢
  intro W _ hj P hP
  have hj₀ : (W.map (σ.symm : K →+* K)).j = a := by
    rw [W.map_j, hj]; simp
  have h0 : solution_aux_hom (σ.symm : K →+* K) P = 0 :=
    ha _ hj₀ _ (by rw [← map_nsmul, hP, map_zero])
  rw [solution_aux_hom_apply] at h0
  exact solution_aux_map_injective (σ.symm : K →+* K)
    (h0.trans (solution_aux_map_zero _).symm)

end ModularCurve
open scoped _root_.P2MW.S_ModularCurve_pow_mem_ssJSet_iff_of_perfectField.ModularCurve

/--
@isnad1 id=iff.0h3v.s6.4b401466b73c from=translated src=- shape=c0653ce8 vocab=f466681a
-/
theorem solution {K : Type*} [Field K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] [PerfectField K] (a : K) :
    a ^ q ∈ ModularCurve.ssJSet q K ↔ a ∈ ModularCurve.ssJSet q K := by
  rw [← frobeniusEquiv_def K q a]
  exact ⟨fun h => by simpa using ModularCurve.solution_aux_ringEquiv_mem q (frobeniusEquiv K q).symm h,
    ModularCurve.solution_aux_ringEquiv_mem q (frobeniusEquiv K q)⟩
