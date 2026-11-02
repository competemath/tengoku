import Tengoku.HodgeStructuresLean4.HodgePilot.Tier6
import Tengoku.HodgeStructuresLean4.HodgePilot.Internal
import Tengoku.HodgeStructuresLean4.HodgePilot.Morphisms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The Hodge filtration

The decreasing filtration `F^p = ⊕_{p' ≥ p} H^{p',q'}` attached to a pure
Hodge structure, and the two classical structure theorems relating it to the
decomposition:

* **Theorem 1** (`H_eq_filtration_inf_conj`): for `p + q = n`,
  `H^{p,q} = F^p ∩ σ(F^q)` — the decomposition is recovered from the
  filtration, so the two presentations of a Hodge structure are equivalent.
* **Theorem 2** (`isCompl_filtration_conj`): for `p + q = n + 1`, `F^p` and
  `σ(F^q)` are complementary — the filtration is `n`-opposed to its conjugate
  in the sense of Deligne (Théorie de Hodge II, §1.2).

The hard inclusions rest on internality via
`biSup_inf_biSup_le_of_iSupIndep`. -/

open scoped TensorProduct

noncomputable section

namespace HodgePilot

variable {n : ℤ} {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- The Hodge filtration: `F^p` is the span of the pieces `H^{p',q'}` with
`p' ≥ p`.-/
def QHodgeStructure.filtration (h : QHodgeStructure n V) (p : ℤ) :
    Submodule ℂ (ℂ ⊗[ℚ] V) :=
  ⨆ (pq : ℤ × ℤ) (_ : p ≤ pq.1), h.H pq

theorem QHodgeStructure.filtration_antitone (h : QHodgeStructure n V) :
    Antitone h.filtration := by
  intro p q hpq
  exact iSup₂_le fun pq hq =>
    le_iSup₂ (f := fun pq' (_ : p ≤ pq'.1) => h.H pq') pq (hpq.trans hq)

theorem QHodgeStructure.H_le_filtration (h : QHodgeStructure n V)
    (pq : ℤ × ℤ) : h.H pq ≤ h.filtration pq.1 :=
  le_iSup₂ (f := fun pq' (_ : pq.1 ≤ pq'.1) => h.H pq') pq le_rfl

/-- The easy half of the classical `H^{p,q} = F^p ∩ σ(F^q)`: each piece sits
inside the intersection. The reverse inclusion requires internality and is
the substance of the decomposition ↔ filtration equivalence.-/
theorem QHodgeStructure.H_le_filtration_inf_conj (h : QHodgeStructure n V)
    (p q : ℤ) :
    h.H (p, q) ≤ h.filtration p ⊓ (h.filtration q).map (sigmaQ V) := by
  refine le_inf (h.H_le_filtration (p, q)) ?_
  rw [← h.conj_symm q p]
  exact Submodule.map_mono (h.H_le_filtration (q, p))

/-- `σ` carries the filtration onto the "column filtration": the image
`σ(F^q)` is the span of the pieces `H^{r,s}` with `s ≥ q`.-/
theorem QHodgeStructure.map_filtration_sigmaQ (h : QHodgeStructure n V)
    (q : ℤ) :
    (h.filtration q).map (sigmaQ V) =
      ⨆ (pq : ℤ × ℤ) (_ : q ≤ pq.2), h.H pq := by
  have hswap : ∀ pq : ℤ × ℤ, (h.H pq).map (sigmaQ V) = h.H (pq.2, pq.1) := by
    rintro ⟨a, b⟩
    exact h.conj_symm a b
  rw [show h.filtration q = ⨆ (pq : ℤ × ℤ) (_ : q ≤ pq.1), h.H pq from rfl]
  simp_rw [Submodule.map_iSup, hswap]
  refine le_antisymm (iSup₂_le fun pq hq => ?_) (iSup₂_le fun ab hb => ?_)
  · exact le_iSup₂ (f := fun ab (_ : q ≤ ab.2) => h.H ab) (pq.2, pq.1) hq
  · exact le_iSup₂ (f := fun pq (_ : q ≤ pq.1) => h.H (pq.2, pq.1))
      (ab.2, ab.1) hb

/-- Core estimate for both structure theorems: `F^p ∩ σ(F^q)` is contained in
the span of the pieces `H^{r,s}` with `r ≥ p` **and** `s ≥ q`. This is where
internality (independence of the pieces) enters, through
`biSup_inf_biSup_le_of_iSupIndep`.-/
theorem QHodgeStructure.filtration_inf_conj_le_biSup (h : QHodgeStructure n V)
    (p q : ℤ) :
    h.filtration p ⊓ (h.filtration q).map (sigmaQ V) ≤
      ⨆ (pq : ℤ × ℤ) (_ : p ≤ pq.1 ∧ q ≤ pq.2), h.H pq := by
  rw [h.map_filtration_sigmaQ q]
  exact biSup_inf_biSup_le_of_iSupIndep h.isInternal.submodule_iSupIndep
    (fun pq => p ≤ pq.1) (fun pq => q ≤ pq.2)

/-- The hard half of Theorem 1: for `p + q = n` the intersection
`F^p ∩ σ(F^q)` collapses onto the single piece `H^{p,q}`.-/
theorem QHodgeStructure.filtration_inf_conj_le (h : QHodgeStructure n V)
    {p q : ℤ} (hpq : p + q = n) :
    h.filtration p ⊓ (h.filtration q).map (sigmaQ V) ≤ h.H (p, q) := by
  refine (h.filtration_inf_conj_le_biSup p q).trans (iSup₂_le ?_)
  rintro ⟨a, b⟩ ⟨hpa, hqb⟩
  have hpa' : p ≤ a := hpa
  have hqb' : q ≤ b := hqb
  by_cases hn : a + b = n
  · obtain rfl : a = p := by omega
    obtain rfl : b = q := by omega
    exact le_rfl
  · rw [h.supported (a, b) hn]
    exact bot_le

/-- **Theorem 1** (decomposition ↔ filtration equivalence): for a weight-`n`
pure Hodge structure and `p + q = n`, the Hodge piece is recovered from the
filtration as `H^{p,q} = F^p ∩ σ(F^q)`. Together with
`H_le_filtration_inf_conj` this shows the decomposition and filtration
presentations of a pure Hodge structure carry the same data.-/
theorem QHodgeStructure.H_eq_filtration_inf_conj (h : QHodgeStructure n V)
    {p q : ℤ} (hpq : p + q = n) :
    h.H (p, q) = h.filtration p ⊓ (h.filtration q).map (sigmaQ V) :=
  le_antisymm (h.H_le_filtration_inf_conj p q) (h.filtration_inf_conj_le hpq)

/-- Below the antidiagonal the filtration meets its conjugate trivially:
if `n < p + q` then `F^p ∩ σ(F^q) = 0`.-/
theorem QHodgeStructure.filtration_inf_conj_eq_bot (h : QHodgeStructure n V)
    {p q : ℤ} (hpq : n < p + q) :
    h.filtration p ⊓ (h.filtration q).map (sigmaQ V) = ⊥ := by
  rw [eq_bot_iff]
  refine (h.filtration_inf_conj_le_biSup p q).trans (iSup₂_le ?_)
  rintro ⟨a, b⟩ ⟨hpa, hqb⟩
  have hpa' : p ≤ a := hpa
  have hqb' : q ≤ b := hqb
  exact le_of_eq (h.supported (a, b) (by omega))

/-- Above the antidiagonal the filtration and its conjugate jointly span:
if `p + q ≤ n + 1` then `F^p + σ(F^q) = ⊤`.-/
theorem QHodgeStructure.filtration_sup_conj_eq_top (h : QHodgeStructure n V)
    {p q : ℤ} (hpq : p + q ≤ n + 1) :
    h.filtration p ⊔ (h.filtration q).map (sigmaQ V) = ⊤ := by
  rw [eq_top_iff, ← h.isInternal.submodule_iSup_eq_top]
  refine iSup_le ?_
  rintro ⟨a, b⟩
  by_cases hn : a + b = n
  · by_cases hp : p ≤ a
    · exact le_sup_of_le_left
        ((h.H_le_filtration (a, b)).trans (h.filtration_antitone hp))
    · refine le_sup_of_le_right ?_
      rw [h.map_filtration_sigmaQ q]
      exact le_iSup₂ (f := fun pq (_ : q ≤ pq.2) => h.H pq) (a, b) (by omega)
  · rw [h.supported (a, b) hn]
    exact bot_le

/-- **Theorem 2** (opposedness): for `p + q = n + 1`, the filtration and its
conjugate are complementary, `F^p ⊕ σ(F^q) = ℂ ⊗ V`. This is Deligne's
condition that `F` and `σ(F)` are `n`-opposed (Théorie de Hodge II, §1.2),
here derived from internality of the decomposition.-/
theorem QHodgeStructure.isCompl_filtration_conj (h : QHodgeStructure n V)
    {p q : ℤ} (hpq : p + q = n + 1) :
    IsCompl (h.filtration p) ((h.filtration q).map (sigmaQ V)) :=
  ⟨disjoint_iff.mpr (h.filtration_inf_conj_eq_bot (by omega)),
    codisjoint_iff.mpr (h.filtration_sup_conj_eq_top (by omega))⟩

/-- Morphisms of Hodge structures are automatically filtered: the
complexification of a `HodgeHom` carries `F^p` into `F^p`.-/
theorem HodgeHom.maps_filtration {W : Type*} [AddCommGroup W] [Module ℚ W]
    [Module.Finite ℚ W] {hV : QHodgeStructure n V} {hW : QHodgeStructure n W}
    (f : HodgeHom hV hW) (p : ℤ) :
    (hV.filtration p).map (f.toLinearMap.baseChange ℂ) ≤ hW.filtration p := by
  rw [show hV.filtration p = ⨆ (pq : ℤ × ℤ) (_ : p ≤ pq.1), hV.H pq from rfl]
  simp_rw [Submodule.map_iSup]
  exact iSup₂_le fun pq hpq => (f.maps_pieces pq).trans
    ((hW.H_le_filtration pq).trans (hW.filtration_antitone hpq))

end HodgePilot
