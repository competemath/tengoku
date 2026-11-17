import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_Ribbon

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_ribbonKernel_unfold_eq_and_ribbonGram_eq_and_heckeKernelMap_eq.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_ribbonKernel_unfold_eq_and_ribbonGram_eq_and_heckeKernelMap_eq

set_option autoImplicit false

open _root_.CerednikDrinfeld open _root_.ModularCurve

namespace CerednikDrinfeld
export _root_.CerednikDrinfeld (DegeneracyData degeneracyMatrix pushforward jointDelta ribbonKernel mem_ribbonKernel ribbonGram ribbonGram_apply HeckeData heckeKernelMap)
namespace Unfold
open _root_.CerednikDrinfeld

variable {E V : Type} [Fintype E] [DecidableEq V]

/--
@isnad1 id=eq.0h5v.s7.7848a390608f from=translated src=- shape=92f7b925 vocab=640bf103
-/
theorem pushforward_apply (f : E → V) (x : E → ℤ) (v : V) :
    pushforward f x v = ∑ e : E, if f e = v then x e else 0 := by
  simp only [pushforward, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, degeneracyMatrix, Matrix.of_apply,
    ite_mul, one_mul, zero_mul]

/--
@isnad1 id=iff.0h4v.s8.b705a38b8e0e from=translated src=- shape=ab99b49c vocab=1f0489c2
-/
theorem mem_ribbonKernel_iff' (D : DegeneracyData E V) (x : E → ℤ) :
    x ∈ ribbonKernel D ↔ pushforward D.a x = 0 ∧ pushforward D.b x = 0 := by
  rw [mem_ribbonKernel]
  constructor
  · intro h
    exact ⟨by simpa [jointDelta] using h 0, by simpa [jointDelta] using h 1⟩
  · rintro ⟨ha, hb⟩ i
    fin_cases i
    · simpa [jointDelta] using ha
    · simpa [jointDelta] using hb

/--
@isnad1 id=eq.0h7v.s8.33932ced9dd0 from=translated src=- shape=c5b0ff15 vocab=b69dbd1d
-/
theorem pushforward_tag_apply (f : E → V) (i : Fin 2) (x : E → ℤ) (v : V) (j : Fin 2) :
    pushforward (fun e => (f e, i)) x (v, j) = if j = i then pushforward f x v else 0 := by
  rw [pushforward_apply, pushforward_apply]
  by_cases hij : j = i
  · rw [ite_eq_left hij]
    refine Finset.sum_congr rfl fun e _ => ?_
    subst hij
    by_cases h : f e = v
    · rw [ite_eq_left h, ite_eq_left (show (f e, j) = (v, j) by rw [h])]
    · rw [ite_eq_right h, ite_eq_right (fun hh : (f e, j) = (v, j) => h (congrArg Prod.fst hh))]
  · rw [ite_eq_right hij]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [ite_eq_right (fun hh : (f e, i) = (v, j) => hij (congrArg Prod.snd hh).symm)]

/--
@isnad1 id=iff.0h5v.s9.5abfd9e7beb4 from=translated src=- shape=a6bf0bd3 vocab=af8a0b7f
-/
theorem pushforward_tag_eq_zero_iff (f : E → V) (i : Fin 2) (x : E → ℤ) :
    pushforward (fun e => (f e, i)) x = 0 ↔ pushforward f x = 0 := by
  constructor
  · intro h
    funext v
    have := congrFun h (v, i)
    rw [pushforward_tag_apply, ite_eq_left rfl] at this
    exact this
  · intro h
    funext vj
    obtain ⟨v, j⟩ := vj
    rw [pushforward_tag_apply, h]
    simp

end CerednikDrinfeld.Unfold

open CerednikDrinfeld.Unfold in
/--
@isnad1 id=other.0h3v.s13.fd83d78ec141 from=translated src=- shape=126dfa19 vocab=beea78c2
-/
theorem solution
    {E V : Type} [Fintype E] [Fintype V] [DecidableEq V] (D : DegeneracyData E V) :
    let D' : DegeneracyData E (V × Fin 2) := ⟨fun e => (D.a e, 0), fun e => (D.b e, 1), D.w⟩
    ribbonKernel D' = ribbonKernel D ∧
    (∀ (x y : E → ℤ) (hx : x ∈ ribbonKernel D) (hy : y ∈ ribbonKernel D)
        (hx' : x ∈ ribbonKernel D') (hy' : y ∈ ribbonKernel D'),
      ribbonGram D' ⟨x, hx'⟩ ⟨y, hy'⟩ = ribbonGram D ⟨x, hx⟩ ⟨y, hy⟩) ∧
    (∀ (H : HeckeData D) (H' : HeckeData D'), (∀ ℓ : Nat.Primes, H'.T ℓ = H.T ℓ) →
      ∀ (ℓ : Nat.Primes) (x : E → ℤ) (hx : x ∈ ribbonKernel D) (hx' : x ∈ ribbonKernel D'),
        ((heckeKernelMap H' ℓ ⟨x, hx'⟩ : ↥(ribbonKernel D')) : E → ℤ) =
          ((heckeKernelMap H ℓ ⟨x, hx⟩ : ↥(ribbonKernel D)) : E → ℤ)) := by
  intro D'

  have hker : ribbonKernel D' = ribbonKernel D := by
    apply Submodule.ext
    intro x
    rw [mem_ribbonKernel_iff', mem_ribbonKernel_iff']
    show (pushforward (fun e => (D.a e, (0 : Fin 2))) x = 0 ∧ pushforward (fun e => (D.b e, (1 : Fin 2))) x = 0) ↔ _
    rw [pushforward_tag_eq_zero_iff, pushforward_tag_eq_zero_iff]
  refine ⟨hker, fun x y hx hy hx' hy' => ?_, fun H H' hT ℓ x hx hx' => ?_⟩
  ·
    rw [ribbonGram_apply, ribbonGram_apply]
  ·
    simp only [heckeKernelMap, LinearMap.coe_restrict_apply, Matrix.mulVecLin_apply, hT ℓ]
