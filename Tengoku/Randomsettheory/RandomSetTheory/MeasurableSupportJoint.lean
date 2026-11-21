/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.CastaingRepresentation
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableSupport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Joint measurability of support functions

A Castaing representation reduces the support of a compact random set to a
countable supremum of scalar products.  This yields measurability jointly in
the outcome and the direction, a basic input for functional limit theorems.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set MeasureTheory TopologicalSpace
open scoped InnerProductSpace

noncomputable section

namespace RandomSetTheory

/-- The support function of an Effros-measurable compact nonempty
correspondence into a separable Hilbert space is jointly measurable.-/
theorem measurable_supportFunction_joint
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty) :
    Measurable (fun p : Ω × H => supportFunction (S p.1) p.2) := by
  let f : ℕ → Ω → H :=
    castaingRepresentation hS (fun ω => (hcompact ω).isClosed) hne
  have hf : ∀ n, Measurable (f n) :=
    castaingRepresentation_measurable hS (fun ω => (hcompact ω).isClosed) hne
  have hfmem : ∀ n ω, f n ω ∈ S ω :=
    castaingRepresentation_mem hS (fun ω => (hcompact ω).isClosed) hne
  have hclosure : ∀ ω, closure (Set.range fun n => f n ω) = S ω :=
    closure_range_castaingRepresentation hS (fun ω => (hcompact ω).isClosed) hne
  have hEq : (fun p : Ω × H => supportFunction (S p.1) p.2) =
      fun p => ⨆ n : ℕ, ⟪p.2, f n p.1⟫_ℝ := by
    funext p
    obtain ⟨x, hx, hxmax⟩ :=
      supportFunction_attains (hcompact p.1) (hne p.1) p.2
    have hupper : ∀ n, ⟪p.2, f n p.1⟫_ℝ ≤ supportFunction (S p.1) p.2 :=
      fun n => inner_le_supportFunction (hcompact p.1) (hfmem n p.1) p.2
    have hbdd : BddAbove (Set.range fun n => ⟪p.2, f n p.1⟫_ℝ) :=
      ⟨supportFunction (S p.1) p.2, Set.forall_mem_range.mpr hupper⟩
    rw [hxmax]
    apply le_antisymm
    · have hxclosure : x ∈ closure (Set.range fun n => f n p.1) := by
        rw [hclosure p.1]
        exact hx
      exact closure_minimal
        (by
          rintro _ ⟨n, rfl⟩
          exact le_ciSup hbdd n)
        (isClosed_le (by fun_prop : Continuous fun y : H => ⟪p.2, y⟫_ℝ)
          continuous_const) hxclosure
    · exact ciSup_le fun n => by simpa [hxmax] using hupper n
  rw [hEq]
  exact Measurable.iSup fun n =>
    measurable_snd.inner ((hf n).comp measurable_fst)

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
