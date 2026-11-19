import Tengoku
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.ContentBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The `(n,k)`-generalized counterpart of `Conj.lean`: the conjugation action of
`H = Perm (Fin n) × Perm (Fin k)` (embedded via `sumCongrHom`) on
`Perm (Fin n ⊕ Fin k)`, for unequal `n,k` — needed for the general-`(n,k,p)`
lower bound of `thm:optimal-divisor` (`Conj.lean`'s `n = k` version stays as-is,
since `StrongTwoAdic.lean` depends on it).
-/

namespace CongruenceTheory

open Equiv Equiv.Perm Nat

variable (n k : ℕ)

/-- `H = Perm A × Perm B`, embedded in `Perm (Fin n ⊕ Fin k)` via `sumCongrHom`, as a
`Subgroup`.-/
noncomputable def HgrpPair : Subgroup (Equiv.Perm (Fin n ⊕ Fin k)) :=
  (Equiv.Perm.sumCongrHom (Fin n) (Fin k)).range

/-- The `H`-embedding, as a `Finset` (mirrors `HSet`, generalized to unequal `n,k`).-/
noncomputable def HSetPair : Finset (Equiv.Perm (Fin n ⊕ Fin k)) :=
  Finset.univ.filter (· ∈ (Equiv.Perm.sumCongrHom (Fin n) (Fin k)).range)

/--
@isnad1 id=iff.0h3v.s6.7b82f8202d7b from=translated src=- shape=2826f63e vocab=ac429d4b
-/
lemma mem_HgrpPair_iff (g : Equiv.Perm (Fin n ⊕ Fin k)) : g ∈ HgrpPair n k ↔ g ∈ HSetPair n k := by
  simp [HgrpPair, HSetPair]

noncomputable instance : Fintype ↥(HgrpPair n k) := by unfold HgrpPair; infer_instance

/-- Conjugation action of `H` on the ambient permutation group.-/
noncomputable instance : MulAction ↥(HgrpPair n k) (Equiv.Perm (Fin n ⊕ Fin k)) where
  smul h g := h.1 * g * h.1⁻¹
  one_smul g := by
    change (1 : ↥(HgrpPair n k)).1 * g * (1 : ↥(HgrpPair n k)).1⁻¹ = g
    simp
  mul_smul h1 h2 g := by
    change (h1 * h2 : ↥(HgrpPair n k)).1 * g * (h1 * h2 : ↥(HgrpPair n k)).1⁻¹ =
      h1.1 * (h2.1 * g * h2.1⁻¹) * h1.1⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group

/--
@isnad1 id=eq.0h4v.s10.62652a9756f0 from=translated src=- shape=d2933656 vocab=9e1bd0af
-/
lemma smul_def_pair (h : ↥(HgrpPair n k)) (g : Equiv.Perm (Fin n ⊕ Fin k)) :
    h • g = h.1 * g * h.1⁻¹ := rfl

/-- `HSetPair n k`ᶜ is invariant under `H`-conjugation.
@isnad1 id=mem.1h4v.s10.121f2fc2c334 from=translated src=- shape=368b11ed vocab=390bd2ba
-/
lemma compl_HSetPair_invariant (h : ↥(HgrpPair n k)) (g : Equiv.Perm (Fin n ⊕ Fin k))
    (hg : g ∈ (HSetPair n k)ᶜ) : h • g ∈ (HSetPair n k)ᶜ := by
  rw [Finset.mem_compl] at hg ⊢
  rw [smul_def_pair]
  intro hmem
  apply hg
  rw [← mem_HgrpPair_iff] at hmem ⊢
  have : g = h.1⁻¹ * (h.1 * g * h.1⁻¹) * h.1 := by group
  rw [this]
  exact (HgrpPair n k).mul_mem ((HgrpPair n k).mul_mem (Subgroup.inv_mem _ h.2) hmem) h.2

/-- The `H`-conjugation orbit relation.-/
noncomputable abbrev orbRelPair : Setoid (Equiv.Perm (Fin n ⊕ Fin k)) :=
  MulAction.orbitRel ↥(HgrpPair n k) (Equiv.Perm (Fin n ⊕ Fin k))

/-- `|H| = n! * k!`.
@isnad1 id=eq.0h2v.s6.50303d2bd2a8 from=translated src=- shape=21b1333d vocab=c1407120
-/
theorem card_HgrpPair : Fintype.card ↥(HgrpPair n k) = (n !) * (k !) := by
  have h1 : Fintype.card ↥(HgrpPair n k) = Fintype.card (Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) :=
    Equiv.Perm.sumCongrHom.card_range
  rw [h1]
  simp [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]

open scoped Classical in
/-- The `H`-conjugation class of `g` (as a `Finset`) is exactly its orbit.
@isnad1 id=eq.0h3v.s11.20e765dcc60a from=translated src=- shape=761afcf4 vocab=f7c262f9
-/
theorem filter_orbRelPair_eq_orbit_toFinset (g : Equiv.Perm (Fin n ⊕ Fin k)) :
    Finset.univ.filter ((orbRelPair n k).r g) = (MulAction.orbit ↥(HgrpPair n k) g).toFinset := by
  ext g'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
  exact MulAction.mem_orbit_symm

open scoped Classical in
/-- **Orbit-stabilizer**, specialized: the class size of `g` times the stabilizer size
equals `|H| = n! * k!`.
@isnad1 id=eq.0h3v.s10.4a5c607cb0c2 from=translated src=- shape=7fe9c86d vocab=1fd98637
-/
theorem class_card_mul_stabilizer_card_pair (g : Equiv.Perm (Fin n ⊕ Fin k)) :
    (Finset.univ.filter ((orbRelPair n k).r g)).card *
      Fintype.card ↥(MulAction.stabilizer ↥(HgrpPair n k) g) = (n !) * (k !) := by
  rw [filter_orbRelPair_eq_orbit_toFinset, Set.toFinset_card]
  rw [MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥(HgrpPair n k) g, card_HgrpPair]

end CongruenceTheory
