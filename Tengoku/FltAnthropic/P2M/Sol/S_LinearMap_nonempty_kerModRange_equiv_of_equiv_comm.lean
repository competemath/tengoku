import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm

set_option autoImplicit false

universe u v w

namespace LinearMap
export _root_.LinearMap (mem_range range coe_coe ext submoduleMap ker mem_ker)
open _root_.LinearMap

section KerModRange

variable {R : Type u} [CommRing R] {C : ℕ → Type v} {C' : ℕ → Type w}
  [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, AddCommGroup (C' i)] [∀ i, Module R (C' i)]
  (d : ∀ i, C i →ₗ[R] C (i + 1)) (d' : ∀ i, C' i →ₗ[R] C' (i + 1))
  (e : ∀ i, C i ≃ₗ[R] C' i) (he : ∀ i x, e (i + 1) (d i x) = d' i (e i x))

include he

/--
@isnad1 id=eq.1h7v.s10.93d1c3c5253c from=translated src=- shape=01400246 vocab=1307459d
-/
theorem kerModRange_map_ker (i : ℕ) :
    (LinearMap.ker (d i)).map (e i : C i →ₗ[R] C' i) = LinearMap.ker (d' i) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← he, hx, map_zero]
  · intro hy
    refine ⟨(e i).symm y, ?_, by simp⟩
    apply (e (i + 1)).injective
    rw [he, LinearEquiv.apply_symm_apply, hy, map_zero]

def kerEquivOfComm (i : ℕ) : LinearMap.ker (d i) ≃ₗ[R] LinearMap.ker (d' i) :=
  ((e i).submoduleMap (LinearMap.ker (d i))).trans (LinearEquiv.ofEq _ _ (kerModRange_map_ker d d' e he i))

/--
@isnad1 id=eq.1h8v.s12.648725fe9300 from=translated src=- shape=acc692eb vocab=9cef28aa
-/
theorem kerEquivOfComm_apply (i : ℕ) (x : LinearMap.ker (d i)) :
    ((kerEquivOfComm d d' e he i x : LinearMap.ker (d' i)) : C' i) = e i x := rfl

/--
@isnad1 id=eq.1h7v.s13.4c4a4b264eeb from=translated src=- shape=b7b7a41d vocab=7a5a1047
-/
theorem kerModRange_map_comap (i : ℕ) :
    ((LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype).map
        (kerEquivOfComm d d' e he (i + 1) : LinearMap.ker (d (i + 1)) →ₗ[R] LinearMap.ker (d' (i + 1)))
      = (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range,
    LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, ⟨w, hw⟩, rfl⟩
    refine ⟨e i w, ?_⟩
    rw [kerEquivOfComm_apply, ← he, hw]
  · rintro ⟨w, hw⟩
    refine ⟨(kerEquivOfComm d d' e he (i + 1)).symm y, ⟨(e i).symm w, ?_⟩, by simp⟩
    have h1 : ((kerEquivOfComm d d' e he (i + 1)).symm y : C (i + 1))
        = (e (i + 1)).symm (y : C' (i + 1)) := by
      apply (e (i + 1)).injective
      rw [LinearEquiv.apply_symm_apply, ← kerEquivOfComm_apply d d' e he, LinearEquiv.apply_symm_apply]
    rw [h1]
    apply (e (i + 1)).injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hw]

/--
@isnad1 id=and.1h6v.s14.ffb191b0fee9 from=translated src=- shape=cc737e30 vocab=b271bc19
-/
theorem nonempty_kerModRange_equiv_of_equiv_comm' :
    Nonempty (LinearMap.ker (d 0) ≃ₗ[R] LinearMap.ker (d' 0)) ∧
    ∀ i, Nonempty
      ((LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) ≃ₗ[R]
       (LinearMap.ker (d' (i + 1)) ⧸ (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype)) :=
  ⟨⟨kerEquivOfComm d d' e he 0⟩, fun i =>
    ⟨Submodule.Quotient.equiv _ _ (kerEquivOfComm d d' e he (i + 1)) (kerModRange_map_comap d d' e he i)⟩⟩

end KerModRange

end LinearMap

/--
@isnad1 id=and.1h6v.s14.89a60ed8218b from=translated src=- shape=ccb529f0 vocab=b271bc19
-/
theorem solution
    {R : Type u} [CommRing R] {C C' : ℕ → Type u}
    [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, AddCommGroup (C' i)] [∀ i, Module R (C' i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (d' : ∀ i, C' i →ₗ[R] C' (i + 1))
    (e : ∀ i, C i ≃ₗ[R] C' i) (he : ∀ i x, e (i + 1) (d i x) = d' i (e i x)) :
    Nonempty (LinearMap.ker (d 0) ≃ₗ[R] LinearMap.ker (d' 0)) ∧
    ∀ i, Nonempty
      ((LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) ≃ₗ[R]
       (LinearMap.ker (d' (i + 1)) ⧸ (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype)) :=
  LinearMap.nonempty_kerModRange_equiv_of_equiv_comm' d d' e he
