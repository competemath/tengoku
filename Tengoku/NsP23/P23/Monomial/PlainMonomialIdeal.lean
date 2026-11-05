import Tengoku.NsP23.P23.Monomial.PlainGeometry
import Tengoku.NsP23.P23.Presentation.KernelMinimality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Actual ordinary monomial ideals and their intrinsic finite survivor roots. -/
namespace P23.Monomial
noncomputable section
open scoped BigOperators
local instance plainIdealDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (k : Type*) [Field k]

def plainMonomialIdeal (G : Finset PlainExp) : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span ((fun p => MvPolynomial.monomial p (1 : k)) '' (↑G : Set PlainExp))

theorem mem_plainMonomialIdeal_iff_support (G : Finset PlainExp)
    (f : MvPolynomial (Fin 3) k) :
    f ∈ plainMonomialIdeal k G ↔ ∀ p ∈ f.support, ∃ g ∈ G, plainDivides g p := by
  exact MvPolynomial.mem_ideal_span_monomial_image

theorem monomial_mem_plainMonomialIdeal_iff (G : Finset PlainExp) (p : PlainExp) :
    MvPolynomial.monomial p (1 : k) ∈ plainMonomialIdeal k G ↔
      ∃ g ∈ G, plainDivides g p := by
  rw [mem_plainMonomialIdeal_iff_support]
  simp

def plainSurvivors (G : Finset PlainExp) : Set PlainExp :=
  {p | MvPolynomial.monomial p (1 : k) ∉ plainMonomialIdeal k G}

theorem plainSurvivors_downward (G : Finset PlainExp) {p q : PlainExp}
    (hq : q ∈ plainSurvivors k G) (hpq : plainDivides p q) :
    p ∈ plainSurvivors k G := by
  intro hp
  obtain ⟨g,hg,hgp⟩ := (monomial_mem_plainMonomialIdeal_iff k G p).mp hp
  exact hq ((monomial_mem_plainMonomialIdeal_iff k G q).mpr
    ⟨g,hg,plainDivides_trans hgp hpq⟩)

theorem plainMonomialIdeal_coeff_zero (G : Finset PlainExp) {p : PlainExp}
    (hp : p ∈ plainSurvivors k G) (f : MvPolynomial (Fin 3) k)
    (hf : f ∈ plainMonomialIdeal k G) : f.coeff p = 0 := by
  by_contra hn
  have hsup : p ∈ f.support := MvPolynomial.mem_support_iff.mpr hn
  exact hp ((monomial_mem_plainMonomialIdeal_iff k G p).mpr
    ((mem_plainMonomialIdeal_iff_support k G f).mp hf p hsup))

theorem plain_surviving_quotient_monomials_independent (G : Finset PlainExp) :
    LinearIndependent k (fun p : ↥(plainSurvivors k G) =>
      Ideal.Quotient.mk (plainMonomialIdeal k G) (MvPolynomial.monomial p.1 (1 : k))) := by
  apply linearIndependent_iff'.mpr
  intro s t hz j hj
  have hm : (∑ q ∈ s, t q • MvPolynomial.monomial q.1 (1 : k)) ∈ plainMonomialIdeal k G := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (Ideal.Quotient.mkₐ k (plainMonomialIdeal k G))
      (∑ q ∈ s, t q • MvPolynomial.monomial q.1 (1 : k)) = 0
    simpa only [map_sum, map_smul, Ideal.Quotient.mkₐ_eq_mk] using hz
  have hc := plainMonomialIdeal_coeff_zero k G j.2 _ hm
  have hmono (q : ↥(plainSurvivors k G)) :
      (MvPolynomial.monomial q.1 (1 : k)).coeff j.1 = if q = j then 1 else 0 := by
    simp only [MvPolynomial.coeff_monomial, Subtype.val_inj]
  simpa [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, hmono, hj] using hc

theorem plainSurvivors_finite (G : Finset PlainExp)
    [Module.Finite k (MvPolynomial (Fin 3) k ⧸ plainMonomialIdeal k G)] :
    (plainSurvivors k G).Finite := by
  haveI := (plain_surviving_quotient_monomials_independent k G).finite
  exact Set.toFinite _

def plainSurvivorRoots (G : Finset PlainExp) (hf : (plainSurvivors k G).Finite) :
    Finset PlainExp :=
  hf.toFinset.filter (fun p => ∀ q ∈ hf.toFinset, plainDivides p q → p = q)

theorem plainSurvivorRoots_antichain (G : Finset PlainExp)
    (hf : (plainSurvivors k G).Finite) : PlainRootAntichain (plainSurvivorRoots k G hf) := by
  intro p hp q hq hpq
  exact (Finset.mem_filter.mp hp).2 q (Finset.mem_filter.mp hq).1 hpq

def plainWeight (p : PlainExp) : ℕ := p 0 + p 1 + p 2

theorem plainWeight_strict {p q : PlainExp} (hpq : plainDivides p q) (hne : p ≠ q) :
    plainWeight p < plainWeight q := by
  have h0 := hpq 0
  have h1 := hpq 1
  have h2 := hpq 2
  have hex : p 0 ≠ q 0 ∨ p 1 ≠ q 1 ∨ p 2 ≠ q 2 := by
    by_contra hn
    push Not at hn
    apply hne
    ext j
    fin_cases j <;> simp_all
  unfold plainWeight
  omega

theorem plainSurvivorRoots_standard_iff (G : Finset PlainExp)
    (hf : (plainSurvivors k G).Finite) (p : PlainExp) :
    p ∈ plainStandardSet (plainSurvivorRoots k G hf) ↔ p ∈ plainSurvivors k G := by
  constructor
  · rintro ⟨s,hs,hps⟩
    exact plainSurvivors_downward k G
      (hf.mem_toFinset.mp (Finset.mem_filter.mp hs).1) hps
  · intro hp
    let K := hf.toFinset.filter (fun q => plainDivides p q)
    have hpK : p ∈ K := Finset.mem_filter.mpr ⟨hf.mem_toFinset.mpr hp,plainDivides_refl p⟩
    obtain ⟨s,hs,hmax⟩ := K.exists_max_image plainWeight ⟨p,hpK⟩
    have hsu := (Finset.mem_filter.mp hs).1
    have hps := (Finset.mem_filter.mp hs).2
    refine ⟨s,Finset.mem_filter.mpr ⟨hsu,?_⟩,hps⟩
    intro q hq hsq
    by_contra hne
    have hqK : q ∈ K := Finset.mem_filter.mpr ⟨hq,plainDivides_trans hps hsq⟩
    have hle := hmax q hqK
    have hlt := plainWeight_strict hsq hne
    omega

theorem plainSurvivorRoots_nonempty (G : Finset PlainExp)
    (hf : (plainSurvivors k G).Finite) (h0 : (0 : PlainExp) ∈ plainSurvivors k G) :
    (plainSurvivorRoots k G hf).Nonempty := by
  obtain ⟨s,hs,_⟩ := (plainSurvivorRoots_standard_iff k G hf 0).mpr h0
  exact ⟨s,hs⟩

theorem plainGenerators_eq_border (G : Finset PlainExp)
    (hf : (plainSurvivors k G).Finite) (hG : PlainRootAntichain G) :
    G = plainBorderFinset (plainSurvivorRoots k G hf) := by
  ext g
  rw [plain_border_iff_minimalKilled]
  constructor
  · intro hg
    refine ⟨?_,?_⟩
    · intro hs
      have hsurv := (plainSurvivorRoots_standard_iff k G hf g).mp hs
      exact hsurv ((monomial_mem_plainMonomialIdeal_iff k G g).mpr ⟨g,hg,plainDivides_refl g⟩)
    · intro p hpg hpne
      apply (plainSurvivorRoots_standard_iff k G hf p).mpr
      intro hp
      obtain ⟨q,hq,hqp⟩ := (monomial_mem_plainMonomialIdeal_iff k G p).mp hp
      have he := hG q hq g hg (plainDivides_trans hqp hpg)
      have hgp : plainDivides g p := he ▸ hqp
      exact hpne (plainDivides_antisymm hpg hgp)
  · intro hb
    have hkill : MvPolynomial.monomial g (1 : k) ∈ plainMonomialIdeal k G := by
      by_contra hn
      exact hb.1 ((plainSurvivorRoots_standard_iff k G hf g).mpr hn)
    obtain ⟨q,hq,hqg⟩ := (monomial_mem_plainMonomialIdeal_iff k G g).mp hkill
    by_cases he : q = g
    · exact he ▸ hq
    · have hs := (plainSurvivorRoots_standard_iff k G hf q).mp (hb.2 q hqg he)
      exact False.elim (hs ((monomial_mem_plainMonomialIdeal_iff k G q).mpr ⟨q,hq,plainDivides_refl q⟩))

theorem plainGenerators_antichain_of_minimal (G : Finset PlainExp)
    (hmin : P23.Presentation.HasMinimalGeneratorCard (plainMonomialIdeal k G) G.card) :
    PlainRootAntichain G := by
  intro g hg q hq hgq
  by_contra hne
  let H := (G.erase q).image (fun p => MvPolynomial.monomial p (1 : k))
  have hspan : Ideal.span (↑H : Set (MvPolynomial (Fin 3) k)) = plainMonomialIdeal k G := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro f hf
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hf
      exact Ideal.subset_span ⟨p,(Finset.mem_erase.mp hp).2,rfl⟩
    · apply Ideal.span_le.mpr
      rintro f ⟨p,hp,rfl⟩
      by_cases he : p = q
      · subst p
        have hgH : MvPolynomial.monomial g (1 : k) ∈ Ideal.span (↑H : Set _) :=
          Ideal.subset_span (Finset.mem_image.mpr ⟨g,Finset.mem_erase.mpr ⟨hne,hg⟩,rfl⟩)
        obtain ⟨d,hd⟩ := le_iff_exists_add.mp (show g ≤ q from hgq)
        have hm := (Ideal.span (↑H : Set (MvPolynomial (Fin 3) k))).mul_mem_left
          (MvPolynomial.monomial d 1) hgH
        simpa [MvPolynomial.monomial_mul_monomial,add_comm,← hd] using hm
      · exact Ideal.subset_span (Finset.mem_image.mpr ⟨p,Finset.mem_erase.mpr ⟨he,hp⟩,rfl⟩)
  have hlow := hmin.2 H hspan
  have hc : H.card = G.card - 1 := by
    dsimp only [H]
    rw [Finset.card_image_of_injective _ (MvPolynomial.monomial_left_injective one_ne_zero),
      Finset.card_erase_of_mem hq]
  have hpos : 0 < G.card := Finset.card_pos.mpr ⟨q,hq⟩
  omega
variable {k} in
theorem plain_idealGeneratorMu_eq_of_minimal
    (I : Ideal (MvPolynomial (Fin 3) k)) (n : ℕ)
    (hmin : P23.Presentation.HasMinimalGeneratorCard I n) :
    P23.Presentation.idealGeneratorMu I = n := by
  classical
  rcases hmin.1 with ⟨G0, hG0, hcard0⟩
  have hex : ∃ m, ∃ G : Finset (MvPolynomial (Fin 3) k),
      Ideal.span (↑G : Set _) = I ∧ G.card = m := ⟨n, G0, hG0, hcard0⟩
  rw [P23.Presentation.idealGeneratorMu, dite_eq_left hex]
  apply Nat.le_antisymm
  · exact Nat.find_min' hex ⟨G0, hG0, hcard0⟩
  · rcases Nat.find_spec hex with ⟨G, hG, hcard⟩
    rw [← hcard]
    exact hmin.2 G hG

end
end P23.Monomial
