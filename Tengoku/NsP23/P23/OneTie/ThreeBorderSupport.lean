import Tengoku.NsP23.P23.OneTie.CoverGeometry
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Coordinate support and live-tie restrictions, independent of semigroup tags. -/
namespace P23.OneTie
variable {a b c : ℕ} [NeZero a]

def normalSupport (q : Normal a b c) : Finset (Fin 3) :=
  Finset.univ.filter (fun j => if j = 0 then 0 < q.x else if j = 1 then 0 < q.y else 0 < q.z)

def NormalHasFullSupport (q : Normal a b c) : Prop := 0 < q.x ∧ 0 < q.y ∧ 0 < q.z

def NormalIsPureX (q : Normal a b c) : Prop := 0 < q.x ∧ q.y = 0 ∧ q.z = 0

theorem normalSupport_card_le_three (q : Normal a b c) : (normalSupport q).card ≤ 3 := by
  simpa [normalSupport] using Finset.card_le_card (Finset.filter_subset
    (fun j : Fin 3 => if j = 0 then 0 < q.x else if j = 1 then 0 < q.y else 0 < q.z) Finset.univ)

theorem normalSupport_eq_univ_iff (q : Normal a b c) :
    normalSupport q = Finset.univ ↔ NormalHasFullSupport q := by
  constructor
  · intro he
    have h0 : (0 : Fin 3) ∈ normalSupport q := he ▸ Finset.mem_univ _
    have h1 : (1 : Fin 3) ∈ normalSupport q := he ▸ Finset.mem_univ _
    have h2 : (2 : Fin 3) ∈ normalSupport q := he ▸ Finset.mem_univ _
    simpa [normalSupport, NormalHasFullSupport] using And.intro h0 (And.intro h1 h2)
  · rintro ⟨hx,hy,hz⟩
    ext j
    fin_cases j <;> simp [normalSupport,hx,hy,hz]

theorem normalSupport_card_le_two_of_not_full (q : Normal a b c)
    (h : ¬NormalHasFullSupport q) : (normalSupport q).card ≤ 2 := by
  have hne : normalSupport q ≠ Finset.univ := by
    intro he; exact h ((normalSupport_eq_univ_iff q).mp he)
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_univ _, hne⟩)
  have hu : (Finset.univ : Finset (Fin 3)).card = 3 := by decide
  omega

theorem pure_x_divides_liveTiePoint (q : Normal a b c) (hq : NormalIsPureX q) :
    q ∣ (liveTiePoint : Normal a b c) := by
  apply (Normal.exact_divides_iff q liveTiePoint).mpr
  rcases hq with ⟨hx,hy,hz⟩
  simp [Normal.DividesCriterion, liveTiePoint, hy,hz]

theorem border_not_pure_x {S : Finset (Normal a b c)}
    (hS : S.Nonempty) (hl : IsLiveTie S) {q : Normal a b c}
    (hq : q ∈ borderFinset S) : ¬NormalIsPureX q := by
  intro hp
  have hk := ((mem_borderFinset_iff hS q).mp hq).1
  exact hk (standardSet_dvd_closed S hl.2.2.2 (pure_x_divides_liveTiePoint q hp))
end P23.OneTie
