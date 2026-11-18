import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MazurAdmissible_GaloisModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MazurAdmissible_AdmissibleChain_exists_map_addEquiv.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MazurAdmissible_AdmissibleChain_exists_map_addEquiv.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
local notation α "^+" M:51 => FixedPoints.addSubgroup M α

namespace P2MW.S_MazurAdmissible_AdmissibleChain_exists_map_addEquiv


noncomputable section

open _root_.MazurAdmissible

namespace MazurAdmissible
export _root_.MazurAdmissible (OpenAction AdmissibleChain filtAlpha filtLength)
open _root_.MazurAdmissible

open Function

universe u v

namespace AdmissibleChain export _root_.MazurAdmissible.AdmissibleChain (tag hmono step n hact htop hbot hcard) end AdmissibleChain
open scoped _root_.MazurAdmissible.AdmissibleChain in

/--
@isnad1 id=ex.1h7v.s11.b95c0a1175f4 from=translated src=- shape=93296187 vocab=d223db70
-/
theorem AdmissibleChain.exists_map_addEquiv_aux
    {M : Type u} [AddCommGroup M] {M' : Type v} [AddCommGroup M']
    {p : ℕ} {Φ : OpenAction M} {Φ' : OpenAction M'} (e : M ≃+ M')
    (he : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M), Φ'.φ σ (e x) = e (Φ.φ σ x))
    (c : AdmissibleChain p Φ) :
    ∃ c' : AdmissibleChain p Φ', filtAlpha c' = filtAlpha c ∧ filtLength c' = filtLength c := by
  classical
  refine ⟨{ n := c.n
            step := fun i => (c.step i).map e.toAddMonoidHom
            hbot := by rw [c.hbot, AddSubgroup.map_bot]
            htop := by
              rw [c.htop, ← AddMonoidHom.range_eq_map]
              exact AddMonoidHom.range_eq_top.mpr e.surjective
            hmono := fun i => AddSubgroup.map_mono (c.hmono i)
            tag := c.tag
            hcard := fun i => ?_
            hact := fun i => ?_ }, rfl, rfl⟩
  ·
    have h := c.hcard i
    change (c.step i.castSucc).relIndex (c.step i.succ) = p at h
    change ((c.step i.castSucc).map e.toAddMonoidHom).relIndex ((c.step i.succ).map e.toAddMonoidHom) = p
    exact (AddSubgroup.relIndex_map_map_of_injective _ _ e.injective).trans h
  · have hi := c.hact i
    split_ifs at hi ⊢ with ht
    · intro σ y hy
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hy
      refine AddSubgroup.mem_map.mpr ⟨Φ.φ σ x - x, hi σ x hx, ?_⟩
      change e (Φ.φ σ x - x) = Φ'.φ σ (e x) - e x
      rw [map_sub, he]
    · intro σ ζ hζ a ha y hy
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hy
      refine AddSubgroup.mem_map.mpr ⟨Φ.φ σ x - a • x, hi σ ζ hζ a ha x hx, ?_⟩
      change e (Φ.φ σ x - a • x) = Φ'.φ σ (e x) - a • e x
      rw [map_sub, map_nsmul, he]

end MazurAdmissible

open _root_.MazurAdmissible _root_.P2MW.S_MazurAdmissible_AdmissibleChain_exists_map_addEquiv.MazurAdmissible in
/--
@isnad1 id=ex.1h7v.s11.b95c0a1175f4 from=translated src=- shape=93296187 vocab=d223db70
-/
theorem solution
    {M : Type*} [AddCommGroup M] {M' : Type*} [AddCommGroup M']
    {p : ℕ} {Φ : OpenAction M} {Φ' : OpenAction M'} (e : M ≃+ M')
    (he : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M), Φ'.φ σ (e x) = e (Φ.φ σ x))
    (c : AdmissibleChain p Φ) :
    ∃ c' : AdmissibleChain p Φ', filtAlpha c' = filtAlpha c ∧ filtLength c' = filtLength c :=
  MazurAdmissible.AdmissibleChain.exists_map_addEquiv_aux e he c

end
