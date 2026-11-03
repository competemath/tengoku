import Tengoku.HodgeStructuresLean4.HodgePilot.Tier7
import Tengoku.HodgeStructuresLean4.HodgePilot.Internal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#check @weightOne` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tier 8 (alive-gate, second half): a WEIGHT-ONE rational Hodge structure on
`V = ℚ²` — the Hodge structure of an elliptic curve, with
`H^{1,0} = ℂ·(e₀ + i e₁)` and `H^{0,1} = ℂ·(e₀ - i e₁) = σ(H^{1,0})`.
This forces a genuine two-piece `DirectSum.IsInternal` discharge. -/

open scoped TensorProduct

noncomputable section

namespace HodgePilot

abbrev V2 : Type := Fin 2 → ℚ

/-- The `ℂ`-basis of `ℂ ⊗[ℚ] ℚ²` base-changed from the standard basis.-/
def bc : Module.Basis (Fin 2) ℂ (ℂ ⊗[ℚ] V2) :=
  Algebra.TensorProduct.basis ℂ (Pi.basisFun ℚ (Fin 2))

/-- `w₁ = e₀ + i e₁`, the holomorphic period vector.-/
def w1 : ℂ ⊗[ℚ] V2 := bc 0 + Complex.I • bc 1

/-- `w₂ = e₀ - i e₁ = σ w₁`.-/
def w2 : ℂ ⊗[ℚ] V2 := bc 0 - Complex.I • bc 1

/--
@isnad1 id=eq.0h1v.s11.04848f30d01b from=translated src=- shape=aaa5ea19 vocab=36b3a225
-/
@[simp] theorem sigmaQR_bc (i : Fin 2) : sigmaQR V2 (bc i) = bc i := by
  simp [bc, Algebra.TensorProduct.basis_apply]

/--
@isnad1 id=eq.0h0v.s10.13b2ed3efa8d from=translated src=- shape=fb936850 vocab=53eaa144
-/
theorem sigmaQ_w1 : sigmaQ V2 w1 = w2 := by
  simp [w1, w2, map_add, map_smulₛₗ, Complex.conj_I, sub_eq_add_neg, neg_smul]

/--
@isnad1 id=eq.0h0v.s10.6f67124157bb from=translated src=- shape=fb936850 vocab=53eaa144
-/
theorem sigmaQ_w2 : sigmaQ V2 w2 = w1 := by
  rw [← sigmaQ_w1]; exact sigmaQ_sigmaQ V2 w1

/-- Coefficient extraction against the base-changed basis.-/
private theorem coeffs_zero (a b : ℂ) (h : a • bc 0 + b • bc 1 = 0) :
    a = 0 ∧ b = 0 := by
  have hli := Fintype.linearIndependent_iff.mp bc.linearIndependent
  have hz := hli (fun j => if j = 0 then a else b)
    (by simpa [Fin.sum_univ_two] using h)
  exact ⟨by simpa using hz 0, by simpa using hz 1⟩

/--
@isnad1 id=not.0h0v.s10.f4cd3b2f44b1 from=translated src=- shape=d72e7874 vocab=3d6c69bc
-/
theorem w2_not_mem_span_w1 : w2 ∉ (ℂ ∙ w1) := by
  rw [Submodule.mem_span_singleton]
  rintro ⟨a, ha⟩
  have ha' : a • (bc 0 + Complex.I • bc 1) = bc 0 - Complex.I • bc 1 := by
    simpa [w1, w2] using ha
  have key : (a - 1) • bc 0 + ((a + 1) * Complex.I) • bc 1 = 0 := by
    linear_combination (norm := module) ha'
  obtain ⟨h0, h1⟩ := coeffs_zero _ _ key
  have ha1 : a = 1 := sub_eq_zero.mp h0
  rw [ha1] at h1
  rcases mul_eq_zero.mp h1 with h | h
  · norm_num at h
  · exact Complex.I_ne_zero h

/--
@isnad1 id=disjoint.0h0v.s10.b9c191ea0ec5 from=translated src=- shape=ccc69f85 vocab=4e459705
-/
theorem disjoint_w1_w2 : Disjoint (ℂ ∙ w1) (ℂ ∙ w2) :=
  Submodule.disjoint_span_singleton.mpr fun h => absurd h w2_not_mem_span_w1

/--
@isnad1 id=mem.0h0v.s11.91832e68ff60 from=translated src=- shape=d3465af7 vocab=4c929a13
-/
theorem bc0_mem : bc 0 ∈ (ℂ ∙ w1) ⊔ (ℂ ∙ w2) := by
  have hw1 : w1 ∈ (ℂ ∙ w1) ⊔ (ℂ ∙ w2) :=
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  have hw2 : w2 ∈ (ℂ ∙ w1) ⊔ (ℂ ∙ w2) :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have h2 : (2 : ℂ) • bc 0 = w1 + w2 := by
    simp only [w1, w2]; module
  have h : bc 0 = (2 : ℂ)⁻¹ • (w1 + w2) := by
    rw [← h2, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hw1 hw2)

/--
@isnad1 id=mem.0h0v.s11.deff2f5ebd6d from=translated src=- shape=d3465af7 vocab=4c929a13
-/
theorem bc1_mem : bc 1 ∈ (ℂ ∙ w1) ⊔ (ℂ ∙ w2) := by
  have hw1 : w1 ∈ (ℂ ∙ w1) ⊔ (ℂ ∙ w2) :=
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  have hw2 : w2 ∈ (ℂ ∙ w1) ⊔ (ℂ ∙ w2) :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have h2I : ((2 : ℂ) * Complex.I) • bc 1 = w1 - w2 := by
    simp only [w1, w2]; module
  have hne : (2 : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero two_ne_zero Complex.I_ne_zero
  have h : bc 1 = ((2 : ℂ) * Complex.I)⁻¹ • (w1 - w2) := by
    rw [← h2I, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hw1 hw2)

/--
@isnad1 id=eq.0h0v.s11.29a05bc06b24 from=translated src=- shape=4d5b5e44 vocab=ebba9824
-/
theorem span_w_top : (ℂ ∙ w1) ⊔ (ℂ ∙ w2) = ⊤ := by
  rw [eq_top_iff, ← bc.span_eq, Submodule.span_le, Set.range_subset_iff]
  rw [Fin.forall_fin_two]
  exact ⟨bc0_mem, bc1_mem⟩

/--
@isnad1 id=eq.0h0v.s10.cfa6efb7596e from=translated src=- shape=939c1e84 vocab=babe3dfa
-/
theorem map_span_w1 : (ℂ ∙ w1).map (sigmaQ V2) = ℂ ∙ w2 := by
  rw [Submodule.map_span, Set.image_singleton, sigmaQ_w1]

/--
@isnad1 id=eq.0h0v.s10.f2c66230fe95 from=translated src=- shape=939c1e84 vocab=babe3dfa
-/
theorem map_span_w2 : (ℂ ∙ w2).map (sigmaQ V2) = ℂ ∙ w1 := by
  rw [Submodule.map_span, Set.image_singleton, sigmaQ_w2]

/-- The weight-one example: the rational Hodge structure of an elliptic curve
on `V = ℚ²`, with `H^{1,0} = ℂ·w₁` and `H^{0,1} = ℂ·w₂`.-/
def weightOne : QHodgeStructure 1 V2 where
  H := fun pq =>
    if pq = ((1 : ℤ), (0 : ℤ)) then ℂ ∙ w1
    else if pq = ((0 : ℤ), (1 : ℤ)) then ℂ ∙ w2
    else ⊥
  supported := by
    intro pq hpq
    have h10 : pq ≠ ((1 : ℤ), (0 : ℤ)) := by rintro rfl; exact hpq (by norm_num)
    have h01 : pq ≠ ((0 : ℤ), (1 : ℤ)) := by rintro rfl; exact hpq (by norm_num)
    simp [h10, h01]
  isInternal := by
    apply isInternal_of_isCompl_of_eq_bot
      (i₀ := ((1 : ℤ), (0 : ℤ))) (i₁ := ((0 : ℤ), (1 : ℤ)))
    · simp
    · intro i h0 h1
      rw [ite_eq_right h0, ite_eq_right h1]
    · rw [ite_eq_left rfl, ite_eq_right (by decide), ite_eq_left rfl]
      exact ⟨disjoint_w1_w2, codisjoint_iff.mpr span_w_top⟩
  conj_symm := by
    intro p q
    by_cases h10 : (p, q) = ((1 : ℤ), (0 : ℤ))
    · rw [Prod.mk.injEq] at h10
      obtain ⟨rfl, rfl⟩ := h10
      simp +decide [map_span_w1]
    · by_cases h01 : (p, q) = ((0 : ℤ), (1 : ℤ))
      · rw [Prod.mk.injEq] at h01
        obtain ⟨rfl, rfl⟩ := h01
        simp +decide [map_span_w2]
      · have h10' : (q, p) ≠ ((1 : ℤ), (0 : ℤ)) := by
          intro hc
          rw [Prod.mk.injEq] at hc
          exact h01 (by rw [Prod.mk.injEq]; exact ⟨hc.2, hc.1⟩)
        have h01' : (q, p) ≠ ((0 : ℤ), (1 : ℤ)) := by
          intro hc
          rw [Prod.mk.injEq] at hc
          exact h10 (by rw [Prod.mk.injEq]; exact ⟨hc.2, hc.1⟩)
        simp [h10, h01, h10', h01']

end HodgePilot
