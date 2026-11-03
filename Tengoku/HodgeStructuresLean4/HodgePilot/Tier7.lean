import Tengoku.HodgeStructuresLean4.HodgePilot.Tier6
import Tengoku.HodgeStructuresLean4.HodgePilot.Internal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#check @tate` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tier 7 (the TRUE alive-gate per the audit): construct an actual
`QHodgeStructure` — the Tate structure `ℚ(m)` — discharging `isInternal` and
`conj_symm` concretely, sorry-free. -/

open scoped TensorProduct

noncomputable section

namespace HodgePilot

variable (V : Type*) [AddCommGroup V] [Module ℚ V]

/--
@isnad1 id=eq.0h1v.s9.0677693a85c6 from=translated src=- shape=1140bbce vocab=419b2383
-/
@[simp] theorem range_sigmaQ : LinearMap.range (sigmaQ V) = ⊤ :=
  LinearMap.range_eq_top.mpr (sigmaQ_surjective V)

/--
@isnad1 id=eq.0h1v.s10.655ac2e65767 from=translated src=- shape=eb3aac39 vocab=9a1f23c1
-/
@[simp] theorem map_top_sigmaQ :
    (⊤ : Submodule ℂ (ℂ ⊗[ℚ] V)).map (sigmaQ V) = ⊤ := by
  rw [Submodule.map_top, range_sigmaQ]

/--
@isnad1 id=eq.0h1v.s10.d7b462bdc078 from=translated src=- shape=eb3aac39 vocab=90f3beb2
-/
@[simp] theorem map_bot_sigmaQ :
    (⊥ : Submodule ℂ (ℂ ⊗[ℚ] V)).map (sigmaQ V) = ⊥ :=
  Submodule.map_bot _

/-- The Tate Hodge structure `ℚ(m)`: pure of weight `-2m`, one-dimensional,
concentrated in bidegree `(-m, -m)`.-/
def tate (m : ℤ) : QHodgeStructure (-(2 * m)) ℚ where
  H := fun pq => if pq = (-m, -m) then ⊤ else ⊥
  supported := by
    intro pq hpq
    have hne : pq ≠ (-m, -m) := by
      rintro rfl
      exact hpq (by omega)
    simp [hne]
  isInternal := isInternal_of_eq_bot (fun i hi => ite_eq_right hi) (ite_eq_left rfl)
  conj_symm := by
    intro p q
    by_cases h : (p, q) = ((-m : ℤ), (-m : ℤ))
    · have hp : p = -m := (Prod.mk.injEq .. ▸ h).1
      have hq : q = -m := (Prod.mk.injEq .. ▸ h).2
      subst hp; subst hq
      simp
    · have h' : (q, p) ≠ ((-m : ℤ), (-m : ℤ)) := by
        intro hqp
        exact h (by
          have hq : q = -m := (Prod.mk.injEq .. ▸ hqp).1
          have hp : p = -m := (Prod.mk.injEq .. ▸ hqp).2
          subst hp; subst hq; rfl)
      simp [h, h']

end HodgePilot
