import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Descartes' rule for the seven strict monomial coefficient signs in (6.50). -/

namespace PiIrrationality

def PhaseCoefficientSigns (q : Polynomial ℝ) : Prop :=
  0 < q.coeff 0 ∧ 0 < q.coeff 1 ∧ 0 < q.coeff 2 ∧ 0 < q.coeff 3 ∧
    q.coeff 4 < 0 ∧ q.coeff 5 < 0 ∧ q.coeff 6 < 0

/--
@isnad1 id=ne.1h1v.s4.f54f87dfe826 from=translated src=- shape=ceee38ea vocab=5de239a1
-/
theorem PhaseCoefficientSigns.ne_zero {q : Polynomial ℝ} (hq : PhaseCoefficientSigns q) : q ≠ 0 := by
  intro h
  have h0 := hq.1
  simp [h] at h0

/--
@isnad1 id=eq.2h1v.s4.4d641a6d9733 from=translated src=- shape=9acb6318 vocab=608e2590
-/
theorem PhaseCoefficientSigns.natDegree {q : Polynomial ℝ} (hq : PhaseCoefficientSigns q)
    (hd : q.natDegree ≤ 6) : q.natDegree = 6 :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hd hq.2.2.2.2.2.2.ne

/--
@isnad1 id=eq.2h1v.s6.91d49534a4d1 from=translated src=- shape=c6e34971 vocab=3dbc76f1
-/
theorem PhaseCoefficientSigns.coeffList {q : Polynomial ℝ} (hq : PhaseCoefficientSigns q)
    (hd : q.natDegree ≤ 6) :
    q.coeffList = [q.coeff 6, q.coeff 5, q.coeff 4, q.coeff 3, q.coeff 2, q.coeff 1, q.coeff 0] := by
  rw [Polynomial.coeffList, Polynomial.withBotSucc_degree_eq_natDegree_add_one hq.ne_zero,
    hq.natDegree hd]
  norm_num [List.range_succ]

/--
@isnad1 id=eq.2h1v.s5.465ef5bdec6a from=translated src=- shape=c459abbe vocab=46baabed
-/
theorem PhaseCoefficientSigns.signVariations {q : Polynomial ℝ} (hq : PhaseCoefficientSigns q)
    (hd : q.natDegree ≤ 6) : q.signVariations = 1 := by
  have hlist := hq.coeffList hd
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hq
  rw [Polynomial.signVariations, hlist]
  norm_num [sign_pos h0, sign_pos h1, sign_pos h2, sign_pos h3,
    sign_neg h4, sign_neg h5, sign_neg h6, List.destutter, List.destutter']

/--
@isnad1 id=le.2h1v.s5.d7d635aaa7b9 from=translated src=- shape=6e055579 vocab=55bb0959
-/
theorem PhaseCoefficientSigns.positive_root_count {q : Polynomial ℝ}
    (hq : PhaseCoefficientSigns q) (hd : q.natDegree ≤ 6) :
    q.roots.countP (0 < ·) ≤ 1 := by
  have h := q.roots_countP_pos_le_signVariations
  rwa [hq.signVariations hd] at h

/--
@isnad1 id=eq.6h3v.s6.47acc3519fc3 from=translated src=- shape=49edc0c4 vocab=ae23d52b
-/
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
