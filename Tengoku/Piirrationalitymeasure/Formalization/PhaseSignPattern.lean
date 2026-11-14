import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Descartes' rule for the seven strict monomial coefficient signs in (6.50). -/

namespace PiIrrationality

def PhaseCoefficientSigns (q : Polynomial ℝ) : Prop :=
  0 < q.coeff 0 ∧ 0 < q.coeff 1 ∧ 0 < q.coeff 2 ∧ 0 < q.coeff 3 ∧
    q.coeff 4 < 0 ∧ q.coeff 5 < 0 ∧ q.coeff 6 < 0

theorem PhaseCoefficientSigns.ne_zero {q : Polynomial ℝ} (hq : PhaseCoefficientSigns q) : q ≠ 0 := by
  intro h
  have h0 := hq.1
  simp [h] at h0

theorem PhaseCoefficientSigns.natDegree {q : Polynomial ℝ} (hq : PhaseCoefficientSigns q)
    (hd : q.natDegree ≤ 6) : q.natDegree = 6 :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hd hq.2.2.2.2.2.2.ne

theorem PhaseCoefficientSigns.coeffList {q : Polynomial ℝ} (hq : PhaseCoefficientSigns q)
    (hd : q.natDegree ≤ 6) :
    q.coeffList = [q.coeff 6, q.coeff 5, q.coeff 4, q.coeff 3, q.coeff 2, q.coeff 1, q.coeff 0] := by
  rw [Polynomial.coeffList, Polynomial.withBotSucc_degree_eq_natDegree_add_one hq.ne_zero,
    hq.natDegree hd]
  norm_num [List.range_succ]

theorem PhaseCoefficientSigns.signVariations {q : Polynomial ℝ} (hq : PhaseCoefficientSigns q)
    (hd : q.natDegree ≤ 6) : q.signVariations = 1 := by
  have hlist := hq.coeffList hd
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hq
  rw [Polynomial.signVariations, hlist]
  norm_num [sign_pos h0, sign_pos h1, sign_pos h2, sign_pos h3,
    sign_neg h4, sign_neg h5, sign_neg h6, List.destutter, List.destutter']

theorem PhaseCoefficientSigns.positive_root_count {q : Polynomial ℝ}
    (hq : PhaseCoefficientSigns q) (hd : q.natDegree ≤ 6) :
    q.roots.countP (0 < ·) ≤ 1 := by
  have h := q.roots_countP_pos_le_signVariations
  rwa [hq.signVariations hd] at h

theorem PhaseCoefficientSigns.positive_root_unique {q : Polynomial ℝ}
    (hq : PhaseCoefficientSigns q) (hd : q.natDegree ≤ 6) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hpx : q.eval x = 0) (hpy : q.eval y = 0) : x = y := by
  classical
  let roots := q.roots.filter (0 < ·)
  have hxmem : x ∈ roots := by
    simp [roots, Polynomial.mem_roots hq.ne_zero, Polynomial.IsRoot, hpx, hx]
  have hymem : y ∈ roots := by
    simp [roots, Polynomial.mem_roots hq.ne_zero, Polynomial.IsRoot, hpy, hy]
  have hcard : roots.card ≤ 1 := by
    simpa only [Multiset.countP_eq_card_filter] using hq.positive_root_count hd
  have hpos : 0 < roots.card := Multiset.card_pos_iff_exists_mem.mpr ⟨x, hxmem⟩
  obtain ⟨z, hz⟩ := Multiset.card_eq_one.mp (show roots.card = 1 by omega)
  rw [hz, Multiset.mem_singleton] at hxmem hymem
  exact hxmem.trans hymem.symm

end PiIrrationality
