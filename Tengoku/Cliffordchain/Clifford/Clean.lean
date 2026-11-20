import Tengoku.Cliffordchain.Clifford.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Clifford's second theorem without the non-degeneracy hypothesis

`clifford_two_clean`: for five circles through `M` in general position the five Miquel points
lie on a *generalized circle*: they are `Cospherical` (a genuine circle) or `Collinear` (a line).

All five points satisfy `k0 - z k1 - conj z k2 + z conj z k3 = 0` with `k3` real and
`k2 = conj k1` (`clifford_points_on`). We split:
* `k3 ≠ 0`: a circle (`clifford_two`);
* `k3 = 0`, `k1 ≠ 0`: a line (`collinear_of_line`);
* `k3 = 0`, `k1 = 0`: then also `k0 = 0`, so the Clifford equation vanishes identically in
  `z`, `Z`; by Desnanot–Jacobi (`kK_dj`) all five Miquel points coincide
  (`miquel_eq_of_kK_zero`), and a single point is cospherical.
-/

namespace Clifford

open Complex ComplexConjugate EuclideanGeometry

/-- A point satisfying a non-trivial real-linear equation `g₀ - z g₁ - conj z conj g₁ = 0` lies on
the line through `g₀ / (2 g₁)` with direction `I / g₁`.
@isnad1 id=ex.2h3v.s7.4289f95649ee from=translated src=- shape=b025c0e8 vocab=f9f65c0a
-/
theorem mem_line_of {g₀ g₁ z : ℂ} (hg : g₁ ≠ 0) (hz : g₀ - z * g₁ - conj z * conj g₁ = 0) :
    ∃ t : ℝ, z = g₀ / (2 * g₁) + t • (I / g₁) := by
  refine ⟨(z * g₁).im, ?_⟩
  have h0 : g₀ = z * g₁ + conj (z * g₁) := by rw [map_mul]; linear_combination hz
  have hw : z * g₁ = ((z * g₁).im : ℂ) * I + (z * g₁ + conj (z * g₁)) / 2 := by
    apply Complex.ext <;> simp; ring
  rw [Complex.real_smul, h0]
  field_simp
  linear_combination (2 : ℂ) * hw

/-- A set of points satisfying a non-trivial real-linear equation
`g₀ - z g₁ - conj z conj g₁ = 0` is collinear.
@isnad1 id=collinea.2h3v.s7.3e3a302814f1 from=translated src=- shape=c54e325c vocab=cb8039da
-/
theorem collinear_of_line {s : Set ℂ} {g₀ g₁ : ℂ} (hg : g₁ ≠ 0)
    (hs : ∀ z ∈ s, g₀ - z * g₁ - conj z * conj g₁ = 0) : Collinear ℝ s := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  exact ⟨g₀ / (2 * g₁), I / g₁, fun z hz => by
    obtain ⟨t, ht⟩ := mem_line_of hg (hs z hz); exact ⟨t, by rw [vadd_eq_add, add_comm]; exact ht⟩⟩

/-- The five Miquel points satisfy the Clifford equation.
@isnad1 id=eq.2h6v.s6.f5e2eeb9501d from=translated src=- shape=ed335381 vocab=5365980e
-/
theorem clifford_points_on {a b c d e : ℂ} (h : GenPos5 a b c d e) :
    ∀ z ∈ ({miquel a b c d, miquel a b c e, miquel a b d e, miquel a c d e, miquel b c d e} :
      Set ℂ), cliffordEq a b c d e z = 0 := by
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl
  · exact h.pos4_abcd.cliffordEq_miquel e
  · have h1 := h.pos4_abce.cliffordEq_miquel d
    rw [cliffordEq, kK_p12354, neg_eq_zero] at h1; exact h1
  · have h1 := h.pos4_abde.cliffordEq_miquel c
    rw [cliffordEq, kK_p12453] at h1; exact h1
  · have h1 := h.pos4_acde.cliffordEq_miquel b
    rw [cliffordEq, kK_p13452, neg_eq_zero] at h1; exact h1
  · have h1 := h.pos4_bcde.cliffordEq_miquel a
    rw [cliffordEq, kK_p23451] at h1; exact h1

/-- If the Clifford equation vanishes identically (in independent `z`, `Z`), the Miquel points
of `{a,b,c,d}` and `{a,b,c,e}` coincide (Desnanot–Jacobi, `kK_dj`, at `Z ≠ conj P_abcd`).
@isnad1 id=eq.8h5v.s9.012e5bda7611 from=translated src=- shape=c2bb3ced vocab=12e7d8d5
-/
theorem miquel_eq_of_kK_zero {a b c d e : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (he : e ≠ 0) (hD4 : mD a b c d (conj a) (conj b) (conj c) (conj d) ≠ 0)
    (hD5 : mD a b c e (conj a) (conj b) (conj c) (conj e) ≠ 0)
    (H : ∀ z Z, kK a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) z Z = 0) :
    miquel a b c d = miquel a b c e := by
  have hD4b : mD (conj a) (conj b) (conj c) (conj d) a b c d ≠ 0 := by
    rw [← conj_mD]; exact (map_ne_zero _).2 hD4
  set N4b := mN (conj a) (conj b) (conj c) (conj d) a b c d
  set D4b := mD (conj a) (conj b) (conj c) (conj d) a b c d
  have hdj := kK_dj a b c d e (conj a) (conj b) (conj c) (conj d) (conj e)
    (miquel a b c d) (N4b / D4b - 1)
  rw [H, zero_mul, miquel_mul a b c d hD4] at hdj
  have hV : mN (conj a) (conj b) (conj c) (conj d) a b c d -
      (N4b / D4b - 1) * mD (conj a) (conj b) (conj c) (conj d) a b c d = D4b := by
    field_simp; ring
  rw [hV] at hdj
  have hne : conj a * conj b * conj c * conj d * D4b * (a * b * c * e) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_)
      hD4b) (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) he) <;>
      exact conj_ne_zero' ‹_›
  have key : (mN a b c e (conj a) (conj b) (conj c) (conj e) -
      miquel a b c d * mD a b c e (conj a) (conj b) (conj c) (conj e)) = 0 := by
    have : conj a * conj b * conj c * conj d * D4b * (a * b * c * e) *
        (mN a b c e (conj a) (conj b) (conj c) (conj e) -
          miquel a b c d * mD a b c e (conj a) (conj b) (conj c) (conj e)) = 0 := by
      linear_combination -hdj
    exact (mul_eq_zero.1 this).resolve_left hne
  rw [eq_comm, miquel, div_eq_iff hD5]
  linear_combination key

/-- If the Clifford equation of five circles in general position vanishes identically, all five
Miquel points coincide.
@isnad1 id=eq.3h6v.s8.6253fb1accac from=translated src=- shape=5a991066 vocab=c169d0f3
-/
theorem miquel_all_eq {a b c d e : ℂ} (h : GenPos5 a b c d e)
    (H : ∀ z Z, kK a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) z Z = 0) :
    ∀ z ∈ ({miquel a b c d, miquel a b c e, miquel a b d e, miquel a c d e, miquel b c d e} :
      Set ℂ), z = miquel a b c d := by
  have ha := h.ab.left_ne_zero; have hb := h.bc.left_ne_zero; have hc := h.cd.left_ne_zero
  have hd := h.de.left_ne_zero; have he := h.de.right_ne_zero
  have D1 := h.pos4_abcd.mD_ne_zero; have D2 := h.pos4_abce.mD_ne_zero
  have D3 := h.pos4_abde.mD_ne_zero; have D4 := h.pos4_acde.mD_ne_zero
  have D5 := h.pos4_bcde.mD_ne_zero
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact (miquel_eq_of_kK_zero ha hb hc hd he D1 D2 H).symm
  · rw [← miquel_p1243 a b c d]
    refine miquel_eq_of_kK_zero ha hb hd he hc D3 ?_ fun z Z => ?_
    · rw [mD_p1243]; exact neg_ne_zero.2 D1
    · rw [kK_p12453]; exact H z Z
  · rw [← miquel_p1342 a b c d]
    refine miquel_eq_of_kK_zero ha hc hd he hb D4 ?_ fun z Z => ?_
    · rw [mD_p1342]; exact D1
    · rw [kK_p13452, H, neg_zero]
  · rw [← miquel_p2341 a b c d]
    refine miquel_eq_of_kK_zero hb hc hd he ha D5 ?_ fun z Z => ?_
    · rw [mD_p2341]; exact neg_ne_zero.2 D1
    · rw [kK_p23451]; exact H z Z

/-- **Clifford's second theorem, hypothesis-free form** (`n = 5`). For five circles through `M`
with centres `a, b, c, d, e` in general position, the five points `P_S` of `clifford_one` lie on a
generalized circle: a circle (`Cospherical`) or a line (`Collinear`).
@isnad1 id=or.1h5v.s7.3445a3bef976 from=translated src=- shape=f77819a5 vocab=dc2686b8
-/
theorem clifford_two_clean {a b c d e : ℂ} (h : GenPos5 a b c d e) :
    Cospherical ({miquel a b c d, miquel a b c e, miquel a b d e, miquel a c d e, miquel b c d e} :
      Set ℂ) ∨
    Collinear ℝ ({miquel a b c d, miquel a b c e, miquel a b d e, miquel a c d e, miquel b c d e} :
      Set ℂ) := by
  by_cases hk : CliffordNondeg a b c d e
  · exact Or.inl (clifford_two h hk)
  have hk3 : k3 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) = 0 := not_not.1 hk
  have hon := clifford_points_on h
  have hconj : conj (k1 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e)) =
      k2 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) := by
    rw [map_k1]; simp only [starRingEnd_self_apply]; rw [k2_swap]
  by_cases hk1 : k1 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) = 0
  · left
    have hk2 : k2 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) = 0 := by
      rw [← hconj, hk1, map_zero]
    have hk0 : k0 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) = 0 := by
      have h1 := hon (miquel a b c d) (by simp)
      rw [cliffordEq, kK_expand, hk1, hk2, hk3] at h1
      linear_combination h1
    have H : ∀ z Z, kK a b c d e (conj a) (conj b) (conj c) (conj d) (conj e) z Z = 0 := by
      intro z Z; rw [kK_expand, hk0, hk1, hk2, hk3]; ring
    exact ⟨miquel a b c d, 0, fun z hz => by rw [miquel_all_eq h H z hz, dist_self]⟩
  · right
    refine collinear_of_line hk1 (g₀ := k0 a b c d e (conj a) (conj b) (conj c) (conj d) (conj e))
      fun z hz => ?_
    have h1 := hon z hz
    rw [cliffordEq, kK_expand, hk3, ← hconj] at h1
    linear_combination h1

/-! ## The general Clifford chain -/

/-- A generalized circle: a circle (`Metric.sphere`) or a line.-/
def IsGCircle (X : Set ℂ) : Prop :=
  (∃ o : ℂ, ∃ r : ℝ, X = Metric.sphere o r) ∨
    ∃ p v : ℂ, v ≠ 0 ∧ X = {z | ∃ t : ℝ, z = p + t • v}

/-- `Chain n c X`: `X` is a Clifford object of the `n` circles through `M = 0` with centres `c`.
Levels `0, 1, 2` are explicit (`M`, the circle itself, the second intersection point). For
`n ≥ 3` the levels alternate: for odd `n`, `X` is a generalized circle containing, for each `i`,
a Clifford point of the `n - 1` circles obtained by omitting circle `i`; for even `n`, `X = {p}`
where `p` lies, for each `i`, on a Clifford object of the circles without circle `i`.-/
def Chain : (n : ℕ) → (Fin n → ℂ) → Set ℂ → Prop
  | 0, _, X => X = {0}
  | 1, c, X => X = Metric.sphere (c 0) ‖c 0‖
  | 2, c, X => X = {second (c 0) (c 1)}
  | n + 3, c, X =>
    if n % 2 = 0 then
      IsGCircle X ∧ ∀ i : Fin (n + 3), ∃ p, Chain (n + 2) (c ∘ i.succAbove) {p} ∧ p ∈ X
    else
      ∃ p, X = {p} ∧ ∀ i : Fin (n + 3), ∃ Y, Chain (n + 2) (c ∘ i.succAbove) Y ∧ p ∈ Y

/-- `n` circles through `M` in general position (pairwise transversal, every triple in general
position).-/
def GenPosN {n : ℕ} (c : Fin n → ℂ) : Prop :=
  (∀ i j, i ≠ j → Transversal (c i) (c j)) ∧
    ∀ i j k, i < j → j < k → GenTriple (c i) (c j) (c k)

/-- **The Clifford chain** for `n` circles: in general position the Clifford object of level `n`
exists (odd `n ≥ 3`: the points of level `n - 1` are concyclic, on a generalized circle;
even `n ≥ 4`: the circles of level `n - 1` are concurrent).-/
def CliffordChain (n : ℕ) : Prop := ∀ c : Fin n → ℂ, GenPosN c → ∃ X, Chain n c X

/--
@isnad1 id=ex.1h2v.s7.ea996aeb932f from=translated src=- shape=30cb73dc vocab=1ece8696
-/
theorem chain3_of (c : Fin 3 → ℂ) (q : ℂ)
    (hq : OnCircle3 (second (c 0) (c 1)) (second (c 0) (c 2)) (second (c 1) (c 2)) q) :
    ∃ Y, Chain 3 c Y ∧ q ∈ Y := by
  obtain ⟨o, r, hr⟩ := hq
  have hm : ∀ z, z ∈ ({second (c 0) (c 1), second (c 0) (c 2), second (c 1) (c 2), q} : Set ℂ) →
      z ∈ Metric.sphere o r := fun z hz => by rw [Metric.mem_sphere]; exact hr z hz
  refine ⟨Metric.sphere o r, ?_, hm q (by simp)⟩
  refine ⟨Or.inl ⟨o, r, rfl⟩, fun i => ?_⟩
  fin_cases i
  · exact ⟨second (c 1) (c 2), rfl, hm _ (by simp)⟩
  · exact ⟨second (c 0) (c 2), rfl, hm _ (by simp)⟩
  · exact ⟨second (c 0) (c 1), rfl, hm _ (by simp)⟩

/--
@isnad1 id=chain.1h1v.s7.db786d2037d7 from=translated src=- shape=f409a842 vocab=11e1fb8e
-/
theorem chain4_of (c : Fin 4 → ℂ) (h : GenPos4 (c 0) (c 1) (c 2) (c 3)) :
    Chain 4 c {miquel (c 0) (c 1) (c 2) (c 3)} := by
  obtain ⟨h1, h2, h3, h4⟩ := clifford_one h
  refine ⟨_, rfl, fun i => ?_⟩
  fin_cases i
  · exact chain3_of (c ∘ Fin.succAbove 0) _ h4
  · exact chain3_of (c ∘ Fin.succAbove 1) _ h3
  · exact chain3_of (c ∘ Fin.succAbove 2) _ h2
  · exact chain3_of (c ∘ Fin.succAbove 3) _ h1

/--
@isnad1 id=genpos4.1h1v.s6.a910649dd2c3 from=translated src=- shape=3646f8a6 vocab=5ba8384a
-/
theorem GenPosN.pos4 {c : Fin 4 → ℂ} (h : GenPosN c) : GenPos4 (c 0) (c 1) (c 2) (c 3) :=
  ⟨h.1 0 1 (by decide), h.1 0 2 (by decide), h.1 0 3 (by decide), h.1 1 2 (by decide),
    h.1 1 3 (by decide), h.1 2 3 (by decide), h.2 0 1 2 (by decide) (by decide),
    h.2 0 1 3 (by decide) (by decide), h.2 0 2 3 (by decide) (by decide),
    h.2 1 2 3 (by decide) (by decide)⟩

/--
@isnad1 id=genpos5.1h1v.s6.b3b5b591caa2 from=translated src=- shape=80057986 vocab=6e0e08a6
-/
theorem GenPosN.pos5 {c : Fin 5 → ℂ} (h : GenPosN c) : GenPos5 (c 0) (c 1) (c 2) (c 3) (c 4) :=
  ⟨h.1 0 1 (by decide), h.1 0 2 (by decide), h.1 0 3 (by decide), h.1 0 4 (by decide),
    h.1 1 2 (by decide), h.1 1 3 (by decide), h.1 1 4 (by decide), h.1 2 3 (by decide),
    h.1 2 4 (by decide), h.1 3 4 (by decide), h.2 0 1 2 (by decide) (by decide),
    h.2 0 1 3 (by decide) (by decide), h.2 0 1 4 (by decide) (by decide),
    h.2 0 2 3 (by decide) (by decide), h.2 0 2 4 (by decide) (by decide),
    h.2 0 3 4 (by decide) (by decide), h.2 1 2 3 (by decide) (by decide),
    h.2 1 2 4 (by decide) (by decide), h.2 1 3 4 (by decide) (by decide),
    h.2 2 3 4 (by decide) (by decide)⟩

/-- Base case `n = 4` of the Clifford chain (Clifford's first theorem).
@isnad1 id=clifford.0h0v.s2.fd0f6aecede3 from=translated src=- shape=e590c3e1 vocab=5675b229
-/
theorem cliffordChain_four : CliffordChain 4 :=
  fun c h => ⟨_, chain4_of c h.pos4⟩

/-- A cospherical or collinear set lies on a generalized circle.
@isnad1 id=ex.1h1v.s6.0fc418e8d0e8 from=translated src=- shape=2f76e61c vocab=73afb293
-/
theorem exists_gcircle {s : Set ℂ} (h : Cospherical s ∨ Collinear ℝ s) :
    ∃ X, IsGCircle X ∧ s ⊆ X := by
  rcases h with ⟨o, r, hr⟩ | h
  · exact ⟨Metric.sphere o r, Or.inl ⟨o, r, rfl⟩, fun z hz => hr z hz⟩
  · obtain ⟨p, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).1 h
    by_cases h0 : v = 0
    · refine ⟨{z | ∃ t : ℝ, z = p + t • (1 : ℂ)}, Or.inr ⟨p, 1, one_ne_zero, rfl⟩,
        fun z hz => ⟨0, ?_⟩⟩
      obtain ⟨t, ht⟩ := hv z hz
      rw [ht, h0, smul_zero, zero_smul, vadd_eq_add, zero_add, add_zero]
    · refine ⟨{z | ∃ t : ℝ, z = p + t • v}, Or.inr ⟨p, v, h0, rfl⟩, fun z hz => ?_⟩
      obtain ⟨t, ht⟩ := hv z hz
      exact ⟨t, by rw [ht, vadd_eq_add, add_comm]⟩

/-- Base case `n = 5` of the Clifford chain (Clifford's second theorem, `clifford_two_clean`).
@isnad1 id=clifford.0h0v.s2.06388a029eed from=translated src=- shape=e590c3e1 vocab=5675b229
-/
theorem cliffordChain_five : CliffordChain 5 := by
  intro c h
  have h5 := h.pos5
  obtain ⟨X, hX, hs⟩ := exists_gcircle (clifford_two_clean h5)
  refine ⟨X, hX, fun i => ?_⟩
  fin_cases i
  · exact ⟨miquel (c 1) (c 2) (c 3) (c 4), chain4_of (c ∘ Fin.succAbove 0) h5.pos4_bcde, hs (by simp)⟩
  · exact ⟨miquel (c 0) (c 2) (c 3) (c 4), chain4_of (c ∘ Fin.succAbove 1) h5.pos4_acde, hs (by simp)⟩
  · exact ⟨miquel (c 0) (c 1) (c 3) (c 4), chain4_of (c ∘ Fin.succAbove 2) h5.pos4_abde, hs (by simp)⟩
  · exact ⟨miquel (c 0) (c 1) (c 2) (c 4), chain4_of (c ∘ Fin.succAbove 3) h5.pos4_abce, hs (by simp)⟩
  · exact ⟨miquel (c 0) (c 1) (c 2) (c 3), chain4_of (c ∘ Fin.succAbove 4) h5.pos4_abcd, hs (by simp)⟩

end Clifford
