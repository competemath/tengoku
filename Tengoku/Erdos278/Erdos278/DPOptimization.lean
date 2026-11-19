import Tengoku.Erdos278.Erdos278.RadixDP
import Tengoku.Erdos278.Erdos278.AsymptoticDensity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

/-- Complement relation of a separation mask, with the reflexive diagonal.-/
def maskGraph {r : ℕ} (H : SeparationMask r) (i j : Fin r) : Prop :=
  ∀ p : PairIndex r,
    ((p.1.1 = i ∧ p.1.2 = j) ∨ (p.1.1 = j ∧ p.1.2 = i)) → p ∉ H

theorem mask_graph_exact {r : ℕ} (n : Fin r → ℕ) (a : Fin r → ℤ) (i j : Fin r) :
    maskGraph (incompatibilityMask n a) i j ↔ Compatible n a i j := by
  classical
  have hs (i j : Fin r) : Compatible n a i j ↔ Compatible n a j i := by
    simp only [Compatible, Nat.gcd_comm (n j) (n i), Int.modEq_comm]
  constructor
  · intro h
    rcases lt_trichotomy i j with hij | hij | hji
    · have hh := h ⟨(i,j), hij⟩ (Or.inl ⟨rfl, rfl⟩)
      simpa [incompatibilityMask] using hh
    · subst j
      exact Int.ModEq.refl _
    · apply (hs i j).mpr
      have hh := h ⟨(j,i), hji⟩ (Or.inr ⟨rfl, rfl⟩)
      simpa [incompatibilityMask] using hh
  · intro h p hp
    simp only [incompatibilityMask, mem_filter, mem_univ, true_and, not_not]
    rcases hp with ⟨hi, hj⟩ | ⟨hj, hi⟩
    · simpa [hi, hj] using h
    · simpa [hi, hj] using (hs i j).mp h

noncomputable def maskDensity {r : ℕ} (n : Fin r → ℕ) (H : SeparationMask r) : ℚ :=
  graphValue univ n (maskGraph H)

theorem mask_density_exact {r : ℕ} (n : Fin r → ℕ) (hn : ∀ i, 0 < n i)
    (a : Fin r → ℤ) :
    maskDensity n (incompatibilityMask n a) = density univ n a := by
  rw [density_eq_graphValue univ n (fun i _ => hn i)]
  unfold maskDensity
  congr 1
  funext i j
  exact propext (mask_graph_exact n a i j)

/-- The DP attains exactly the original density values, given a checked radix
representation. No assumption about an optimal graph or a digit encoder is used.-/
theorem radix_dp_density_exact {r : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (hr : 0 < r) (n : Fin r → ℕ) (b : β → ℕ) (e : Fin r → β → ℕ)
    (hb : ∀ j, 0 < b j) (hc : Pairwise (fun j k => (b j).Coprime (b k)))
    (hn : ∀ i, radixModulus b (e i) = n i) (d : ℚ) :
    (∃ H ∈ radixDP b e, maskDensity n H = d) ↔
      ∃ a : Fin r → ℤ, density univ n a = d := by
  have heq : (fun i => radixModulus b (e i)) = n := funext hn
  have hpos (i : Fin r) : 0 < n i := hn i ▸ radix_modulus_pos b (e i) hb
  constructor
  · rintro ⟨H, hH, hd⟩
    obtain ⟨a, ha⟩ := (radix_dp_realizable_exact hr b e hb hc H).mp hH
    rw [heq] at ha
    refine ⟨a, ?_⟩
    rw [ha, mask_density_exact n hpos a] at hd
    exact hd
  · rintro ⟨a, rfl⟩
    refine ⟨incompatibilityMask n a, ?_, mask_density_exact n hpos a⟩
    apply (radix_dp_realizable_exact hr b e hb hc _).mpr
    exact ⟨a, by rw [heq]⟩

/-- Maximizing the finite DP objective gives an attained global optimum of
the original density, and every maximizing DP state has an integer witness.-/
theorem radix_dp_maximum {r : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (hr : 0 < r) (n : Fin r → ℕ) (b : β → ℕ) (e : Fin r → β → ℕ)
    (hb : ∀ j, 0 < b j) (hc : Pairwise (fun j k => (b j).Coprime (b k)))
    (hn : ∀ i, radixModulus b (e i) = n i) :
    ∃ H ∈ radixDP b e, ∃ a : Fin r → ℤ,
      maskDensity n H = density univ n a ∧
      (∀ K ∈ radixDP b e, maskDensity n K ≤ maskDensity n H) ∧
      (∀ x : Fin r → ℤ, density univ n x ≤ density univ n a) := by
  classical
  have hex := (radix_dp_density_exact hr n b e hb hc hn (density univ n (fun _ => 0))).mpr
    ⟨fun _ => 0, rfl⟩
  obtain ⟨H₀, hH₀, _⟩ := hex
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image (radixDP b e) (maskDensity n) ⟨H₀, hH₀⟩
  obtain ⟨a, ha⟩ := (radix_dp_density_exact hr n b e hb hc hn (maskDensity n H)).mp
    ⟨H, hH, rfl⟩
  refine ⟨H, hH, a, ha.symm, hmax, ?_⟩
  intro x
  obtain ⟨K, hK, hx⟩ := (radix_dp_density_exact hr n b e hb hc hn (density univ n x)).mpr
    ⟨x, rfl⟩
  rw [← hx, ha]
  exact hmax K hK

end Erdos278
