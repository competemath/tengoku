import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_TateLocalZeta
import Tengoku.Seed.Topology.Clopen
import Tengoku.Seed.Topology.Compactness.Compact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open LanglandsTunnell.TateLocal

noncomputable section

namespace SchwartzBruhatSpace

section Space

variable (X : Type*) [TopologicalSpace X]

abbrev testSpace : Submodule ℂ (X → ℂ) where
  carrier := {f | IsSchwartzBruhat f}
  zero_mem' := IsSchwartzBruhat.zero
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    refine ⟨?_, ?_⟩
    · exact hf.1.comp (c * ·)
    · exact hf.2.comp_left (g := (c * ·)) (mul_zero c)

variable {X}

/--
@isnad1 id=iff.0h2v.s6.75b0f4a92227 from=translated src=- shape=52ae8fd6 vocab=bd4e06c3
-/
theorem mem_testSpace {f : X → ℂ} : f ∈ testSpace X ↔ IsSchwartzBruhat f :=
  Iff.rfl

/--
@isnad1 id=iff.0h2v.s6.e238ed8e8bbe from=translated src=- shape=fb92f284 vocab=ee8d4147
-/
theorem mem_testSpace_iff {f : X → ℂ} : f ∈ testSpace X ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl

/--
@isnad1 id=islocall.1h2v.s6.489fa0a8032e from=translated src=- shape=80581a73 vocab=55725a9b
-/
theorem isLocallyConstant_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : IsLocallyConstant f :=
  hf.1

/--
@isnad1 id=hascompa.1h2v.s6.ee8895449df4 from=translated src=- shape=80581a73 vocab=ad5ac1dc
-/
theorem hasCompactSupport_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : HasCompactSupport f :=
  hf.2

/--
@isnad1 id=mem.2h2v.s6.1e0c941beea7 from=translated src=- shape=50ecc1b9 vocab=ee8d4147
-/
theorem mem_testSpace_of {f : X → ℂ} (h₁ : IsLocallyConstant f) (h₂ : HasCompactSupport f) :
    f ∈ testSpace X :=
  ⟨h₁, h₂⟩

/--
@isnad1 id=mem.2h3v.s6.e06a268a4d4f from=translated src=- shape=83de2a6b vocab=c2bb93bb
-/
theorem indicator_mem_testSpace {U : Set X} (hU : IsClopen U) (hUc : IsCompact U) (c : ℂ) :
    (U.indicator fun _ => c) ∈ testSpace X :=
  IsSchwartzBruhat.indicator_const hU hUc c

/--
@isnad1 id=mem.2h3v.s7.3cceb3bac0f9 from=translated src=- shape=49cc8df9 vocab=968b5ef5
-/
theorem mul_mem_testSpace {e f : X → ℂ} (he : IsLocallyConstant e) (hf : f ∈ testSpace X) :
    e * f ∈ testSpace X :=
  ⟨he.mul hf.1, hf.2.mul_left⟩

/--
@isnad1 id=isclopen.1h2v.s6.697471189c37 from=translated src=- shape=e0a71a1e vocab=a7767b55
-/
theorem isClopen_support_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : IsClopen (Function.support f) := by
  have h : Function.support f = {x | f x = 0}ᶜ := by
    ext x
    simp only [Function.mem_support, Set.mem_compl_iff, Set.mem_ofPred_eq, ne_eq]
  rw [h]
  exact (hf.1.isClopen_fiber 0).compl

/--
@isnad1 id=iscompac.1h2v.s6.f19ecde1427b from=translated src=- shape=e0a71a1e vocab=b6160e7b
-/
theorem isCompact_support_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : IsCompact (Function.support f) :=
  (hasCompactSupport_of_mem hf).isCompact.of_isClosed_subset (isClopen_support_of_mem hf).isClosed (subset_tsupport _)

end Space

end SchwartzBruhatSpace
