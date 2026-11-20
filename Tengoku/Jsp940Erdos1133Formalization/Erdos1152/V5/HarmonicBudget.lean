import Tengoku.Jsp940Erdos1133Formalization.Erdos1152.V5.CircleInterpolation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open scoped BigOperators Real
open Finset Set Filter
namespace Erdos1152.V5

/-- A dyadic block contributes at least one half.
@isnad1 id=le.1h1v.s5.1b45ac7914fc from=translated src=- shape=d90d1f22 vocab=bf6721ee
-/
theorem harmonicHeight_double (n : ℕ) (hn : 0<n) :
    harmonicHeight n+1/2≤harmonicHeight (2*n) := by
  rw [show 2*n=n+n by omega]
  unfold harmonicHeight
  rw [sum_range_add]
  apply add_le_add le_rfl
  calc
    (1:ℝ)/2 = ∑j∈range n,(1:ℝ)/(2*n) := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      field_simp
    _ ≤ ∑j∈range n,(1:ℝ)/(n+j+1:ℕ) := by
      apply sum_le_sum
      intro j hj
      apply one_div_le_one_div_of_le
      · positivity
      · have := mem_range.mp hj
        exact_mod_cast (show n+j+1≤2*n by omega)

/--
@isnad1 id=le.0h1v.s5.5ab9737b48a0 from=translated src=- shape=0d2594b3 vocab=f89255a9
-/
theorem harmonicHeight_pow_two (j : ℕ) :
    1+(j:ℝ)/2≤harmonicHeight (2^j) := by
  induction j with
  | zero => simp [harmonicHeight]
  | succ j ih =>
    have hs := harmonicHeight_double (2^j) (by positivity)
    rw [Nat.mul_comm 2 (2^j)] at hs
    rw [pow_succ]
    push_cast
    nlinarith [hs]

/--
@isnad1 id=ex.0h1v.s4.2bc49e5b9865 from=translated src=- shape=cefffa79 vocab=34dca7c6
-/
theorem exists_harmonicHeight_ge (B : ℝ) :
    ∃A : ℕ,0<A ∧ B≤harmonicHeight A := by
  obtain ⟨j,hj⟩ := exists_nat_gt (2*B)
  refine ⟨2^j,by positivity,?_⟩
  exact (show B≤1+(j:ℝ)/2 by linarith).trans (harmonicHeight_pow_two j)

/-- Explicit parameter family for the finite Bernstein localization.
`m=4q`, `k=32q A²`, `ρ=k+2q`, `R₀=k+q` gives an exact node budget
and a band gap independent of the scale parameter `q`.-/
def localizationDegree (A q : ℕ) : ℕ := 32*q*A*A
def localizationRadius (A q : ℕ) : ℕ := localizationDegree A q+2*q
noncomputable def localizationInner (A q : ℕ) : ℝ := localizationDegree A q+q
noncomputable def localizationBandwidth (A : ℕ) : ℝ :=
  Real.pi*(32*A*A)/(32*A*A+1)
noncomputable def localizationGamma (A : ℕ) : ℝ :=
  Real.pi/(16*(32*A*A+1))

/--
@isnad1 id=eq.0h2v.s6.39b79691d494 from=translated src=- shape=e9d36767 vocab=d5fbaa14
-/
theorem localization_node_budget (A q : ℕ) :
    2*localizationRadius A q+1=2*(8*(4*q)*A*A)+4*q+1 := by
  unfold localizationRadius localizationDegree
  ring

/--
@isnad1 id=eq.1h2v.s5.f4e57d43f71a from=translated src=- shape=b857cc6c vocab=d5188e0b
-/
theorem localization_frequency (A q : ℕ) (hq : 0<q) :
    Real.pi*localizationDegree A q/localizationInner A q=localizationBandwidth A := by
  unfold localizationInner localizationBandwidth localizationDegree
  push_cast
  have hqr : (q:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hd : (32*(A:ℝ)*A+1)≠0 := by positivity
  field_simp [hqr,hd]

/--
@isnad1 id=and.0h1v.s5.cb1b33807951 from=translated src=- shape=2a1cd095 vocab=7c62e4e8
-/
theorem localization_gap (A : ℕ) :
    localizationBandwidth A+16*localizationGamma A=Real.pi ∧
      0<localizationGamma A := by
  unfold localizationBandwidth localizationGamma
  constructor
  · field_simp
  · positivity

/--
@isnad1 id=eq.0h2v.s4.e8406bce669b from=translated src=- shape=129c390d vocab=9166ca92
-/
theorem localization_margin (A q : ℕ) :
    (localizationRadius A q:ℝ)-localizationInner A q=q := by
  unfold localizationRadius localizationInner
  push_cast
  ring

end Erdos1152.V5
