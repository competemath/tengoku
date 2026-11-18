import Tengoku.Seed.Data.Finset.Lattice.Fold
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Algebra.Order.BigOperators.Ring.Finset
import Tengoku
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The genuine finite endpoint-counting model and its oscillation potential. -/

namespace Oscillation

noncomputable section
open Finset

def endpointWeight (p c : ℕ) : ℝ :=
  (if p < c then 1 else 0) + (if p = c then (1 / 2 : ℝ) else 0)

def endpointValue {n : ℕ} (χ : Fin n → ℝ) (p Y : Fin n → ℕ)
    (c y : ℕ) : ℝ :=
  ∑ i, χ i * (if Y i < y then 1 else 0) * endpointWeight (p i) c

def gridMax {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hm⟩, mem_univ _⟩ f

def gridOsc {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) : ℝ :=
  gridMax hm f + gridMax hm (fun t => -f t)

def blockValues {n m : ℕ} (χ : Fin n → ℝ) (p Y : Fin n → ℕ)
    (c v : ℕ) (t : Fin m) : ℝ :=
  endpointValue χ p Y c (v * m + t.val + 1)

def gridPotential {n : ℕ} (K V m : ℕ) (hm : 0 < m)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) : ℝ :=
  (∑ c : Fin K, ∑ v : Fin V, gridOsc hm (blockValues χ p Y c.val v.val)) /
    (K * V : ℕ)

def gridMaxPotential {n : ℕ} (K V m : ℕ) (hm : 0 < m)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) : ℝ :=
  (∑ c : Fin K, ∑ v : Fin V, gridMax hm (blockValues χ p Y c.val v.val)) /
    (K * V : ℕ)

def refinedPositions {n b : ℕ} (p : Fin n → ℕ) (r : Fin n → Fin b) : Fin n → ℕ :=
  fun i => b * p i + (r i).val

/--
@isnad1 id=le.0h2v.s4.a1ee27aec069 from=translated src=- shape=5ffe46ab vocab=5ac07bb0
-/
lemma endpointWeight_nonneg (p c : ℕ) : 0 ≤ endpointWeight p c := by
  unfold endpointWeight
  split_ifs <;> norm_num

/--
@isnad1 id=le.0h2v.s4.99501993ffc0 from=translated src=- shape=628a94f6 vocab=5ac07bb0
-/
lemma endpointWeight_le_one (p c : ℕ) : endpointWeight p c ≤ 1 := by
  unfold endpointWeight
  split_ifs <;> norm_num at * <;> omega

/--
@isnad1 id=le.0h3v.s5.4a20442df7e6 from=translated src=- shape=d9c65061 vocab=0c750e03
-/
lemma abs_endpointWeight_sub_le (p q c : ℕ) :
    |endpointWeight p c - endpointWeight q c| ≤ 1 := by
  have hp := endpointWeight_nonneg p c
  have hq := endpointWeight_nonneg p q
  have hp' := endpointWeight_le_one p c
  have hq' := endpointWeight_le_one q c
  have hq := endpointWeight_nonneg q c
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/--
@isnad1 id=le.1h3v.s4.58411beef49d from=translated src=- shape=77030ca4 vocab=1abb11ce
-/
lemma le_gridMax {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) (t : Fin m) :
    f t ≤ gridMax hm f := by
  exact Finset.le_sup' (f := f) (mem_univ t)

/--
@isnad1 id=le.2h3v.s5.d12701ad652e from=translated src=- shape=f03e4c2c vocab=1abb11ce
-/
lemma gridMax_le {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) {a : ℝ}
    (h : ∀ t, f t ≤ a) : gridMax hm f ≤ a := by
  exact (Finset.sup'_le_iff _ f).mpr (fun t _ => h t)

/--
@isnad1 id=le.2h3v.s5.71bc758d3405 from=translated src=- shape=22dd04a5 vocab=1abb11ce
-/
lemma gridMax_mono {m : ℕ} (hm : 0 < m) {f g : Fin m → ℝ}
    (h : ∀ t, f t ≤ g t) : gridMax hm f ≤ gridMax hm g := by
  exact gridMax_le hm f (fun t => (h t).trans (le_gridMax hm g t))

/--
@isnad1 id=eq.1h2v.s4.8dbe3ab3feec from=translated src=- shape=e003fe57 vocab=0f98b72c
-/
lemma gridMax_const {m : ℕ} (hm : 0 < m) (a : ℝ) :
    gridMax hm (fun _ => a) = a := by
  exact Finset.sup'_const _ a

/--
@isnad1 id=eq.2h3v.s5.1ddb9367d7ce from=translated src=- shape=22dd04a5 vocab=0f98b72c
-/
lemma gridMax_congr {m : ℕ} (hm : 0 < m) {f g : Fin m → ℝ}
    (h : ∀ t, f t = g t) : gridMax hm f = gridMax hm g := by
  congr 1
  funext t
  exact h t

/--
@isnad1 id=eq.1h3v.s5.fa8e37218f2b from=translated src=- shape=d72e198d vocab=9439b7dd
-/
lemma gridMax_add_const {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) (a : ℝ) :
    gridMax hm (fun t => f t + a) = gridMax hm f + a := by
  apply le_antisymm
  · exact gridMax_le hm _ (fun t => by have := le_gridMax hm f t; linarith)
  · have h : gridMax hm f ≤ gridMax hm (fun t => f t + a) - a := by
      apply gridMax_le hm
      intro t
      have := le_gridMax hm (fun t => f t + a) t
      linarith
    linarith

/--
@isnad1 id=ex.1h2v.s5.ad4da0144255 from=translated src=- shape=76593c0d vocab=0f98b72c
-/
lemma gridMax_exists {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) :
    ∃ t, gridMax hm f = f t := by
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_eq_sup' ⟨⟨0, hm⟩, mem_univ _⟩ f
  exact ⟨t, ht⟩

/--
@isnad1 id=le.1h2v.s4.481079f4d9a6 from=translated src=- shape=4419c6b6 vocab=9083f76f
-/
lemma gridOsc_nonneg {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) :
    0 ≤ gridOsc hm f := by
  have h₁ := le_gridMax hm f ⟨0, hm⟩
  have h₂ := le_gridMax hm (fun t => -f t) ⟨0, hm⟩
  unfold gridOsc
  linarith

/--
@isnad1 id=eq.1h3v.s5.be0eef222bd8 from=translated src=- shape=3e102f34 vocab=0d70182e
-/
lemma gridOsc_add_const {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) (a : ℝ) :
    gridOsc hm (fun t => f t + a) = gridOsc hm f := by
  unfold gridOsc
  rw [gridMax_add_const]
  have hn : gridMax hm (fun t => -(f t + a)) = gridMax hm (fun t => -f t) - a := by
    calc
      _ = gridMax hm (fun t => -f t + -a) := gridMax_congr hm (by intro t; ring)
      _ = _ := by rw [gridMax_add_const]; ring
  rw [hn]
  ring

/--
@isnad1 id=le.2h3v.s5.479e22ab9311 from=translated src=- shape=f99233d8 vocab=a64e07e1
-/
lemma gridOsc_le {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) {B : ℝ}
    (h : ∀ t, |f t| ≤ B) : gridOsc hm f ≤ 2 * B := by
  have h₁ := gridMax_le hm f (fun t => (abs_le.mp (h t)).2)
  have h₂ := gridMax_le hm (fun t => -f t) (fun t => neg_le.mpr (abs_le.mp (h t)).1)
  unfold gridOsc
  linarith

/--
@isnad1 id=eq.0h1v.s4.079f9f30a66a from=translated src=- shape=f1efd941 vocab=03c6fc47
-/
lemma gridOsc_singleton (f : Fin 1 → ℝ) : gridOsc (by decide) f = 0 := by
  have h : ∀ t : Fin 1, t = 0 := by intro t; exact Fin.eq_zero t
  have h₁ : gridMax (by decide) f = f 0 :=
    (gridMax_congr (by decide) (fun t => by rw [h t])).trans (gridMax_const _ _)
  have h₂ : gridMax (by decide) (fun t => -f t) = -f 0 :=
    (gridMax_congr (by decide) (fun t => by rw [h t])).trans (gridMax_const _ _)
  unfold gridOsc
  rw [h₁, h₂]
  ring

/--
@isnad1 id=le.1h7v.s5.7bd248d22b52 from=translated src=- shape=2fc49837 vocab=9a91e429
-/
lemma gridPotential_nonneg {n : ℕ} (K V m : ℕ) (hm : 0 < m)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) : 0 ≤ gridPotential K V m hm χ p Y := by
  apply div_nonneg
  · exact sum_nonneg fun c _ => sum_nonneg fun v _ => gridOsc_nonneg hm _
  · positivity

/--
@isnad1 id=eq.0h6v.s5.dd6e7497b053 from=translated src=- shape=2ea0adce vocab=045948af
-/
lemma gridPotential_one {n : ℕ} (K V : ℕ) (χ : Fin n → ℝ) (p Y : Fin n → ℕ) :
    gridPotential K V 1 (by decide) χ p Y = 0 := by
  simp only [gridPotential, gridOsc_singleton, sum_const_zero, zero_div]

/--
@isnad1 id=eq.0h6v.s5.109ebd0a117b from=translated src=- shape=725e7081 vocab=46491841
-/
lemma endpointValue_neg {n : ℕ} (χ : Fin n → ℝ) (p Y : Fin n → ℕ) (c y : ℕ) :
    endpointValue (fun i => -χ i) p Y c y = -endpointValue χ p Y c y := by
  unfold endpointValue
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i _
  ring

/--
@isnad1 id=eq.1h7v.s6.70c084e3b287 from=translated src=- shape=eccce399 vocab=6faa36f2
-/
lemma gridPotential_eq_max_add_neg {n : ℕ} (K V m : ℕ) (hm : 0 < m)
    (χ : Fin n → ℝ) (p Y : Fin n → ℕ) :
    gridPotential K V m hm χ p Y = gridMaxPotential K V m hm χ p Y +
      gridMaxPotential K V m hm (fun i => -χ i) p Y := by
  have he : ∀ c v : ℕ, blockValues (fun i => -χ i) p Y c v =
      (fun t : Fin m => -blockValues χ p Y c v t) := by
    intro c v
    funext t
    exact endpointValue_neg χ p Y c _
  unfold gridPotential gridMaxPotential gridOsc
  simp_rw [he]
  rw [← add_div]
  congr 1
  simp only [sum_add_distrib]

/--
@isnad1 id=le.4h8v.s6.f56e029d173c from=translated src=- shape=50bce123 vocab=0010bf91
-/
lemma gridPotential_le_of_values {n K V m : ℕ} (hK : 0 < K) (hV : 0 < V)
    (hm : 0 < m) (χ : Fin n → ℝ) (p Y : Fin n → ℕ) (B : ℝ)
    (h : ∀ (c : Fin K) (v : Fin V) (t : Fin m),
      |blockValues χ p Y c.val v.val t| ≤ B) :
    gridPotential K V m hm χ p Y ≤ 2 * B := by
  have hh : (∑ c : Fin K, ∑ v : Fin V,
      gridOsc hm (blockValues χ p Y c.val v.val)) ≤ (K * V : ℕ) * (2 * B) := by
    calc
      _ ≤ ∑ _c : Fin K, ∑ _v : Fin V, (2 * B) := by
        apply sum_le_sum
        intro c _
        exact sum_le_sum fun v _ => gridOsc_le hm _ (h c v)
      _ = _ := by simp; ring
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (K * V : ℕ))).mpr (by
    simpa [gridPotential, mul_comm] using hh)

end
end Oscillation
