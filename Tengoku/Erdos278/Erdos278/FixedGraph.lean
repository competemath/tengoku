import Tengoku.Erdos278.Erdos278.Dimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

/-- For a prescribed graph, its edge bits are constants, not variables.-/
def prescribedPair (d t q : ℤ) (edge : Bool) : Prop :=
  if edge then t = d * q else 1 ≤ t - d * q ∧ t - d * q ≤ d - 1

/--
@isnad1 id=iff.1h3v.s5.43efe9a9314e from=translated src=- shape=01066dc4 vocab=39790645
-/
theorem prescribed_pair_exact (d t : ℤ) (hd : 0 < d) (edge : Bool) :
    (∃ q, prescribedPair d t q edge) ↔ (edge = true ↔ d ∣ t) := by
  cases edge with
  | false =>
    simp only [prescribedPair, Bool.false_eq_true, ↓reduceIte, false_iff]
    constructor
    · rintro ⟨q, hlo, hhi⟩ ht
      have hdiv : d ∣ t - d * q := dvd_sub ht (dvd_mul_right d q)
      have hpos : 0 < t - d * q := by omega
      have := Int.le_of_dvd hpos hdiv
      omega
    · intro ht
      refine ⟨t / d, ?_⟩
      have hnonneg := Int.emod_nonneg t hd.ne'
      have hlt := Int.emod_lt_of_pos t hd
      have hne : t % d ≠ 0 := mt Int.dvd_of_emod_eq_zero ht
      have hrem := Int.emod_add_mul_ediv t d
      omega
  | true =>
    simp only [prescribedPair, ↓reduceIte, true_iff]
    exact ⟨fun ⟨q, h⟩ => ⟨q, h⟩, fun ⟨q, h⟩ => ⟨q, h⟩⟩

/-- Pure integer feasibility for one fixed graph; original modulus bounds are
used, so this route does not need interaction compression or real variables.-/
def FixedGraphFeasible {r : ℕ} (n : Fin r → ℕ) (i₀ : Fin r)
    (G : PairIndex r → Bool) (x : Fin r → ℤ) (q : PairIndex r → ℤ) : Prop :=
  x i₀ = 0 ∧ (∀ i, 0 ≤ x i ∧ x i < n i) ∧
    ∀ e, prescribedPair ((n e.1.1).gcd (n e.1.2))
      (x e.1.1 - x e.1.2) (q e) (G e)

/--
@isnad1 id=iff.1h4v.s7.a1b703fa56f5 from=translated src=- shape=4ef26b30 vocab=71fe96d9
-/
theorem fixed_graph_feasible_iff {r : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, 0 < n i) (i₀ : Fin r) (G : PairIndex r → Bool) :
    (∃ a : Fin r → ℤ, ∀ e, G e = true ↔ Compatible n a e.1.1 e.1.2) ↔
      ∃ x q, FixedGraphFeasible n i₀ G x q := by
  constructor
  · rintro ⟨a, ha⟩
    let x : Fin r → ℤ := fun i => (a i - a i₀) % n i
    have hx (i j : Fin r) : Compatible n x i j ↔ Compatible n a i j :=
      (reduce_preserves_compatibility n (fun i => a i - a i₀) i j).trans
        (translate_preserves_compatibility n a (a i₀) i j)
    have hq (e : PairIndex r) : ∃ q, prescribedPair
        ((n e.1.1).gcd (n e.1.2)) (x e.1.1 - x e.1.2) q (G e) := by
      apply (prescribed_pair_exact _ _ (by
        exact_mod_cast Nat.gcd_pos_of_pos_left (n e.1.2) (hn e.1.1)) _).mpr
      exact ((ha e).trans (hx e.1.1 e.1.2).symm).trans
        (compatible_iff_dvd n x e.1.1 e.1.2)
    classical
    refine ⟨x, fun e => Classical.choose (hq e), ?_, ?_, ?_⟩
    · simp [x]
    · intro i
      have hp : (0 : ℤ) < n i := by exact_mod_cast hn i
      exact ⟨Int.emod_nonneg _ hp.ne', Int.emod_lt_of_pos _ hp⟩
    · exact fun e => Classical.choose_spec (hq e)
  · rintro ⟨x, q, _, _, hq⟩
    refine ⟨x, fun e => ?_⟩
    have h := (prescribed_pair_exact _ _ (by
      exact_mod_cast Nat.gcd_pos_of_pos_left (n e.1.2) (hn e.1.1)) (G e)).mp
        ⟨q e, hq e⟩
    exact h.trans (compatible_iff_dvd n x e.1.1 e.1.2).symm

/-- The fixed-graph route needs r-1 residue variables and one quotient per pair.
The finite graph enumeration is outside the integer program.
@isnad1 id=eq.0h2v.s7.419d49849a66 from=translated src=- shape=903e117f vocab=1f4479df
-/
theorem fixed_graph_integer_count {r : ℕ} (i₀ : Fin r) :
    ((univ : Finset (Fin r)).erase i₀).card + Fintype.card (PairIndex r) =
      r - 1 + r * (r - 1) / 2 := by
  have hp := twice_pair_count r
  simp only [Finset.card_erase_of_mem (mem_univ i₀), Finset.card_univ, Fintype.card_fin]
  omega

/-- The common gcd-based period appearing in older disjoint-class arguments.-/
def pairGCDPeriod {r : ℕ} (n : Fin r → ℕ) : ℕ :=
  (univ : Finset (PairIndex r)).lcm (fun e => (n e.1.1).gcd (n e.1.2))

/-- Exact comparison with gcd(n_i, H), where H is the lcm of all pairwise gcds.
This identity is useful for comparing the candidate's compression with the
quantity in O'Bryant (2006), Lemma 5, rather than claiming it as a new quantity.
@isnad1 id=eq.1h3v.s5.5490e7297dee from=translated src=- shape=e021d9a6 vocab=c057f1c6
-/
theorem interaction_eq_gcd_pair_period {r : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, 0 < n i) (i : Fin r) :
    interactionModulus n i = (n i).gcd (pairGCDPeriod n) := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (interaction_dvd_modulus n i)
    apply Finset.lcm_dvd
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    rcases lt_trichotomy i j with hij | hij | hji'
    · exact Finset.dvd_lcm (f := fun e : PairIndex r => (n e.1.1).gcd (n e.1.2))
        (Finset.mem_univ (⟨(i, j), hij⟩ : PairIndex r))
    · exact (hji hij.symm).elim
    · have h := Finset.dvd_lcm (f := fun e : PairIndex r => (n e.1.1).gcd (n e.1.2))
        (Finset.mem_univ (⟨(j, i), hji'⟩ : PairIndex r))
      simpa only [pairGCDPeriod, Nat.gcd_comm] using h
  · rw [pairGCDPeriod, gcd_finset_lcm univ
      (fun e : PairIndex r => (n e.1.1).gcd (n e.1.2)) (n i) (hn i).ne'
      (fun e _ => (Nat.gcd_pos_of_pos_left (n e.1.2) (hn e.1.1)).ne')]
    apply Finset.lcm_dvd
    intro e _
    by_cases hi : e.1.1 = i
    · have hji : e.1.2 ≠ i := by
        intro hj
        have hlt := e.2
        simp [hi, hj] at hlt
      have hd : (n i).gcd ((n e.1.1).gcd (n e.1.2)) ∣ (n i).gcd (n e.1.2) :=
        Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
          ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
      exact hd.trans (gcd_dvd_interaction n hji)
    · have hd : (n i).gcd ((n e.1.1).gcd (n e.1.2)) ∣ (n i).gcd (n e.1.1) :=
        Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
          ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))
      exact hd.trans (gcd_dvd_interaction n hi)

end Erdos278
