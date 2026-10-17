import Tengoku.OpenaiMath.OAI.Analysis.C0Absorption.Operators

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators

section LocalOnto
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
@isnad1 id=mem.3h7v.s9.3b1ee6a982a9 from=translated src=- shape=b89e91fc vocab=0c714e4c
-/
theorem range_mem_nhds_of_approx {f : E → F} {a : E} (S : E ≃L[ℝ] F)
    (s : Set E) (hs : s∈nhds a) (c : ℝ≥0)
    (hc : c<‖(S.symm : F →L[ℝ] E)‖₊⁻¹) (ha : ApproximatesLinearOn f (S : E →L[ℝ] F) s c) :
    Set.range f∈nhds (f a) := by
  have hh := ha.image_mem_nhds S.toNonlinearRightInverse hs (Or.inr hc)
  exact mem_of_superset hh (Set.image_subset_range f s)

/--
@isnad1 id=surjecti.5h5v.s7.951ef6a90f23 from=translated src=- shape=3fc45a54 vocab=64e4f937
-/
theorem surjective_of_punctured_local_onto {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Nontrivial E]
    (f : E → F) {c C : ℝ≥0} (hf : AntilipschitzWith c f) (hLip : LipschitzWith C f)
    (hzero : f 0=0) (hconn : IsPreconnected ({0}ᶜ : Set F))
    (hlocal : ∀ x≠0, Set.range f∈nhds (f x)) : Function.Surjective f := by
  let K : Set F := {0}ᶜ
  let A : Set K := Subtype.val ⁻¹' Set.range f
  let : PreconnectedSpace K := Subtype.preconnectedSpace hconn
  have hclosed : IsClosed A := (hf.isClosed_range hLip.uniformContinuous).preimage continuous_subtype_val
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨x,hx⟩ := hy
    have hx0 : x≠0 := by
      intro hx0
      have he : y.val=0 := by rw [← hx,hx0,hzero]
      exact y.property (by simpa only [Set.mem_singleton_iff] using he)
    have hn : Set.range f∈nhds y.val := by rw [← hx]; exact hlocal x hx0
    exact continuous_subtype_val.continuousAt hn
  have hne : A.Nonempty := by
    obtain ⟨x,hx⟩ := exists_ne (0 : E)
    have hx' : f x≠0 := by intro he; exact hx (hf.injective (he.trans hzero.symm))
    refine ⟨⟨f x,?_⟩,x,rfl⟩
    simpa only [K,Set.mem_compl_iff,Set.mem_singleton_iff] using hx'
  have heq : A=Set.univ := IsClopen.eq_univ ⟨hclosed,hopen⟩ hne
  intro y
  by_cases hy : y=0
  · exact ⟨0,hzero.trans hy.symm⟩
  · let yy : K := ⟨y,by simpa only [K,Set.mem_compl_iff,Set.mem_singleton_iff] using hy⟩
    have hh : yy∈A := by rw [heq]; trivial
    exact hh

end LocalOnto
end
end C0Absorption

end OAI
