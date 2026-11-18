import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

local notation α "^+" M:51 => FixedPoints.addSubgroup M α

set_option autoImplicit false
/--
@isnad1 id=ex.2h4v.s16.2f882e420f70 from=translated src=- shape=6c28ea4d vocab=efd54f0e
-/
theorem Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero
    (t : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))))
    (ht : t = Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 0)
                (Multiplicative.ofAdd 1) *
              Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 1)
                (Multiplicative.ofAdd 1))
    (H : Subgroup (Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2)))))
    [H.FiniteIndex] (R : Type) [AddCommGroup R]
    (a : MulAction.orbitRel.Quotient (Subgroup.zpowers t)
          (Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) ⧸ H) → R)
    (ha : ∑ᶠ c, a c = 0) :
    ∃ φ : Additive H →+ R,
      ∀ (g : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))))
        (hg : g⁻¹ * t ^ Function.minimalPeriod (fun x => t • x)
                (g : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) ⧸ H) * g ∈ H),
        φ (Additive.ofMul ⟨_, hg⟩)
          = a (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers t) _)
              (g : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) ⧸ H)) := by exact @_root_.P2MW.S_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero.solution t ht H _ R _ a ha
