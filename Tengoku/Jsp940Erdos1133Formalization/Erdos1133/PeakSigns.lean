import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open Set Finset

namespace Erdos1133

def peakDirection (v : ℝ) : ℝ := if 0 < v then 1 else -1

/--
@isnad1 id=eq.0h1v.s4.58b47a2e5e69 from=translated src=- shape=38becc55 vocab=9733edd7
-/
theorem abs_peakDirection (v : ℝ) : |peakDirection v| = 1 := by
  unfold peakDirection
  split_ifs <;> norm_num

/--
@isnad1 id=eq.0h1v.s4.471ba39388e5 from=translated src=- shape=9a232c61 vocab=d1be778a
-/
theorem peakDirection_mul (v : ℝ) : peakDirection v * v = |v| := by
  unfold peakDirection
  split_ifs with h
  · simp [abs_of_pos h]
  · simp [abs_of_nonpos (le_of_not_gt h)]

/--
@isnad1 id=lt.2h3v.s6.cc8deef3b882 from=translated src=- shape=36be8711 vocab=179d45d5
-/
theorem alternating_direction_positive {v u : ℝ} (hv : v ≠ 0) (j : ℕ)
    (hu : 0 < ((-1 : ℝ)^j * peakDirection v) * u) :
    0 < (-1 : ℝ)^j * (u/v) := by
  have hpos : 0 < |v| := abs_pos.mpr hv
  have heq : ((-1 : ℝ)^j * (u/v)) * |v| =
      ((-1 : ℝ)^j * peakDirection v) * u := by
    rw [← peakDirection_mul v]
    field_simp
  exact (mul_pos_iff_of_pos_right hpos).mp (heq.symm ▸ hu)

/--
@isnad1 id=lt.2h3v.s6.fdcc2ceb53cc from=translated src=- shape=41dfe8b7 vocab=5b6eea88
-/
theorem alternating_products_negative {u v : ℝ} (j : ℕ)
    (hu : 0 < (-1 : ℝ)^j*u) (hv : 0 < (-1 : ℝ)^(j+1)*v) : u*v < 0 := by
  rw [pow_succ] at hv
  rcases neg_one_pow_eq_or (R := ℝ) j with hj | hj
  · rw [hj] at hu hv
    nlinarith
  · rw [hj] at hu hv
    nlinarith

/-- Choose all packet signs before constructing their superposition. Any
result with those strict peak signs has alternating quotients by the fixed,
nonzero node-product values.
@isnad1 id=ex.2h3v.s9.7b222aa0a73f from=translated src=- shape=c930d580 vocab=4534cc8a
-/
theorem choose_alternating_peak_signs (s : Finset ℤ) {k : ℕ}
    (hs : s.card = k+1) (v : ℤ → ℝ) (hv : ∀ j ∈ s, v j ≠ 0) :
    ∃ ψ : ℤ → ℝ, (∀ j, |ψ j| = 1) ∧
      ∀ u : ℤ → ℝ, (∀ j ∈ s, 0 < ψ j*u j) →
        ∀ i : Fin k,
          (u (s.orderEmbOfFin hs i.castSucc) / v (s.orderEmbOfFin hs i.castSucc)) *
          (u (s.orderEmbOfFin hs i.succ) / v (s.orderEmbOfFin hs i.succ)) < 0 := by
  classical
  let e := s.orderIsoOfFin hs
  let ψ : ℤ → ℝ := fun j => if hj : j ∈ s then
    (-1 : ℝ)^((e.symm ⟨j,hj⟩).val) * peakDirection (v j) else 1
  have hψ : ∀ j, |ψ j| = 1 := by
    intro j
    dsimp [ψ]
    split_ifs <;> simp [abs_mul,abs_pow,abs_peakDirection]
  have heval (i : Fin (k+1)) :
      ψ (s.orderEmbOfFin hs i) = (-1 : ℝ)^i.val * peakDirection (v (s.orderEmbOfFin hs i)) := by
    simp [ψ,← Finset.coe_orderIsoOfFin_apply,e]
  refine ⟨ψ,hψ,?_⟩
  intro u hu i
  have hleft := hu _ (s.orderEmbOfFin_mem hs i.castSucc)
  have hright := hu _ (s.orderEmbOfFin_mem hs i.succ)
  rw [heval] at hleft hright
  exact alternating_products_negative i.val
    (alternating_direction_positive (hv _ (s.orderEmbOfFin_mem hs i.castSucc)) _ hleft)
    (alternating_direction_positive (hv _ (s.orderEmbOfFin_mem hs i.succ)) _ hright)

/--
@isnad1 id=strictmo.4h6v.s7.83d5dfdb0cc6 from=translated src=- shape=3b4130f4 vocab=d979c6e9
-/
theorem separated_peaks_strictMono (s : Finset ℤ) {k : ℕ}
    (hs : s.card = k) (c p : ℤ → ℝ) {D ρ : ℝ} (hgap : 2*ρ < D)
    (hcenters : ∀ i ∈ s, ∀ j ∈ s, i < j → D ≤ c j-c i)
    (hp : ∀ j ∈ s, |p j-c j| ≤ ρ) :
    StrictMono (fun i : Fin k => p (s.orderEmbOfFin hs i)) := by
  intro i j hij
  have hi := s.orderEmbOfFin_mem hs i
  have hj := s.orderEmbOfFin_mem hs j
  have hc := hcenters _ hi _ hj ((s.orderEmbOfFin hs).strictMono hij)
  have hpi := abs_le.mp (hp _ hi)
  have hpj := abs_le.mp (hp _ hj)
  linarith

/--
@isnad1 id=not.2h3v.s6.bc0a25d9507b from=translated src=- shape=e0803848 vocab=a48811db
-/
theorem peak_not_mem_nodes (Γ : Finset ℝ) (g : ℂ → ℂ) (p : ℝ)
    (hnodes : ∀ x ∈ Γ, ‖g x‖ ≤ 1) (hpeak : 1 < (g p).re) : p ∉ Γ := by
  intro hp
  have h := (Complex.re_le_norm (g p)).trans (hnodes p hp)
  linarith

end Erdos1133
