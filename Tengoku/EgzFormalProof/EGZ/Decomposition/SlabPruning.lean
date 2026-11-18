import Tengoku.EgzFormalProof.EGZ.Decomposition.ThinDirections
import Tengoku.EgzFormalProof.EGZ.Decomposition.Mass
import Tengoku.EgzFormalProof.EGZ.Decomposition.CenteredLift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Restricting a weight to selected thin slabs

A finite union bound controls the mass removed by intersecting thin slabs.
The stage errors form a geometric sum, leaving enough thickness outside the
maximal space of selected directions. Retained points also have bounded
integer coordinates in the selected directions.
-/

open scoped BigOperators

namespace EGZ

section Restriction

variable {α I : Type*} [Fintype α] [Fintype I]

/-- Delete all mass outside a set.-/
noncomputable def restrictWeight (w : α → ℕ) (S : Set α) : α → ℕ := by
  classical
  exact fun v ↦ if v ∈ S then w v else 0

omit [Fintype α] in
/--
@isnad1 id=le.0h3v.s4.c1fd15787792 from=translated src=- shape=6d262495 vocab=fa7283ec
-/
theorem restrictWeight_le (w : α → ℕ) (S : Set α) : restrictWeight w S ≤ w := by
  classical
  intro v
  change (if v ∈ S then w v else 0) ≤ w v
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

omit [Fintype α] in
/--
@isnad1 id=iff.0h4v.s5.dff81197a7aa from=translated src=- shape=b1e18a7c vocab=ffd9e765
-/
@[simp]
theorem restrictWeight_ne_zero_iff (w : α → ℕ) (S : Set α) (v : α) :
    restrictWeight w S v ≠ 0 ↔ v ∈ S ∧ w v ≠ 0 := by
  classical
  by_cases hv : v ∈ S <;> simp [restrictWeight, hv]

/--
@isnad1 id=eq.0h3v.s4.8dda980f16d9 from=translated src=- shape=75d351f6 vocab=6fa1fd80
-/
@[simp]
theorem natMass_restrictWeight (w : α → ℕ) (S : Set α) :
    natMass (restrictWeight w S) = natMassOn w S := rfl

/--
@isnad1 id=eq.0h3v.s5.7a5d5f10f3d7 from=translated src=- shape=8bf5c2e9 vocab=e0498e6f
-/
theorem restrictWeight_loss_eq_compl (w : α → ℕ) (S : Set α) :
    (natMass w : ℝ) - natMass (restrictWeight w S) = (natMassOn w Sᶜ : ℝ) := by
  have h : (natMassOn w S : ℝ) + natMassOn w Sᶜ = natMass w := by
    exact_mod_cast natMassOn_add_compl w S
  rw [natMass_restrictWeight]
  linarith

/-- Finite union bound for the mass outside an intersection.
@isnad1 id=le.0h4v.s6.6cfd0f5141d7 from=translated src=- shape=d25420a4 vocab=2295b7dd
-/
theorem natMassOn_compl_intersection_le (w : α → ℕ) (S : I → Set α) :
    natMassOn w {v | ∀ i, v ∈ S i}ᶜ ≤ ∑ i, natMassOn w (S i)ᶜ := by
  classical
  unfold natMassOn
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : ∀ i, v ∈ S i
  · simp [hv]
  · obtain ⟨i, hi⟩ := not_forall.mp hv
    have hle := Finset.single_le_sum
      (f := fun i ↦ if v ∈ (S i)ᶜ then w v else 0)
      (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    simpa only [Set.mem_compl_iff, Set.mem_ofPred_eq, hv, not_false_eq_true,
      ite_true, hi] using hle

/-- Relative complement bounds add when the retained sets are intersected.
@isnad1 id=le.1h5v.s7.f3687a4cb75f from=translated src=- shape=14c11399 vocab=08960dbf
-/
theorem restrictWeight_intersection_loss_le (w : α → ℕ) (S : I → Set α)
    (ε : I → ℝ)
    (hS : ∀ i, (natMassOn w (S i)ᶜ : ℝ) ≤ ε i * natMass w) :
    (natMass w : ℝ) - natMass (restrictWeight w {v | ∀ i, v ∈ S i}) ≤
      (∑ i, ε i) * natMass w := by
  rw [restrictWeight_loss_eq_compl]
  calc
    (natMassOn w {v | ∀ i, v ∈ S i}ᶜ : ℝ) ≤ ∑ i, (natMassOn w (S i)ᶜ : ℝ) := by
      exact_mod_cast natMassOn_compl_intersection_le w S
    _ ≤ ∑ i, ε i * natMass w := Finset.sum_le_sum (fun i _ ↦ hS i)
    _ = (∑ i, ε i) * natMass w := (Finset.sum_mul _ _ _).symm

/--
@isnad1 id=le.1h4v.s6.30bba8287906 from=translated src=- shape=848edcf9 vocab=f84c2bf2
-/
theorem restrictWeight_retainedMass_ge (w : α → ℕ) (S : Set α) (ε : ℝ)
    (hloss : (natMass w : ℝ) - natMass (restrictWeight w S) ≤ ε * natMass w) :
    (1 - ε) * (natMass w : ℝ) ≤ natMass (restrictWeight w S) := by
  linarith

/--
@isnad1 id=ex.3h4v.s6.d6b879236a22 from=translated src=- shape=07f10309 vocab=5fdae3dc
-/
theorem restrictWeight_nonzero_of_loss_lt_one (w : α → ℕ) (S : Set α) (ε : ℝ)
    (hw : ∃ v, w v ≠ 0) (hε : ε < 1)
    (hloss : (natMass w : ℝ) - natMass (restrictWeight w S) ≤ ε * natMass w) :
    ∃ v, restrictWeight w S v ≠ 0 := by
  obtain ⟨v, hv⟩ := hw
  have hmass : 0 < natMass w := (Nat.pos_of_ne_zero hv).trans_le
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ v))
  have hmass' : (0 : ℝ) < natMass w := by exact_mod_cast hmass
  have hret := restrictWeight_retainedMass_ge w S ε hloss
  have hpos : (0 : ℝ) < natMass (restrictWeight w S) :=
    (mul_pos (sub_pos.mpr hε) hmass').trans_le hret
  have hn : natMass (restrictWeight w S) ≠ 0 := by exact_mod_cast ne_of_gt hpos
  obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact ⟨v, hv⟩

end Restriction

/--
@isnad1 id=le.1h6v.s7.888459515d11 from=translated src=- shape=d75fb0b9 vocab=04401f64
-/
theorem IsThinAlong.compl_mass_le {p d : ℕ} [NeZero p]
    {w : FpCoord p d → ℕ} {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p}
    {t : ℕ} {ε : ℝ} (h : IsThinAlong w ξ t ε) :
    (natMassOn w (slab ξ t)ᶜ : ℝ) ≤ ε * natMass w := by
  have hthin := (isThinAlong_iff_natMass w ξ t ε).mp h
  have htotal : (natMassOn w (slab ξ t) : ℝ) + natMassOn w (slab ξ t)ᶜ = natMass w := by
    exact_mod_cast natMassOn_add_compl w (slab ξ t)
  linarith

/-- The intersection of the first `k` stage-indexed slabs.-/
def slabIntersection {p d : ℕ} (k : ℕ)
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p) (t : ℕ → ℕ) : Set (FpCoord p d) :=
  {v | ∀ i : Fin k, v ∈ slab (ξ i) (t (i + 1))}

/--
@isnad1 id=le.0h1v.s6.df3f46c1600e from=translated src=- shape=80e1fbff vocab=597d8c2b
-/
theorem sum_three_pow_succ_le (k : ℕ) :
    (∑ i : Fin k, (3 : ℝ) ^ (i.val + 1)) ≤ 3 ^ (k + 1) - 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hpow : (0 : ℝ) ≤ 3 ^ (k + 1) := by positivity
    rw [show (3 : ℝ) ^ (k + 1 + 1) = 3 ^ (k + 1) * 3 from pow_succ _ _]
    nlinarith

namespace DirectionChain

variable {p d k : ℕ} [Fact p.Prime]
    {W : Submodule (ZMod p) (FpCoord p d →ᵃ[ZMod p] ZMod p)}
    {w : FpCoord p d → ℕ} {t : ℕ → ℕ} {δ : ℝ}
    (D : DirectionChain W
      (fun i ξ ↦ IsThinAlong w ξ (t (i + 1)) ((3 : ℝ) ^ (i + 1) * δ)) k)

/--
@isnad1 id=le.0h8v.s11.258f42bfe424 from=translated src=- shape=d3dc4941 vocab=4e86f00b
-/
theorem slabIntersection_loss_le_sum :
    (natMass w : ℝ) - natMass (restrictWeight w (slabIntersection k D.direction t)) ≤
      (∑ i : Fin k, (3 : ℝ) ^ (i.val + 1) * δ) * natMass w :=
  restrictWeight_intersection_loss_le w (fun i : Fin k ↦ slab (D.direction i) (t (i + 1)))
    (fun i ↦ (3 : ℝ) ^ (i.val + 1) * δ)
    (fun i ↦ (D.selected i i.isLt).compl_mass_le)

/--
@isnad1 id=le.1h8v.s11.5967343ae009 from=translated src=- shape=0c7360ee vocab=1cf7f0a3
-/
theorem slabIntersection_loss_le (hδ : 0 ≤ δ) :
    (natMass w : ℝ) - natMass (restrictWeight w (slabIntersection k D.direction t)) ≤
      ((3 : ℝ) ^ (k + 1) - 1) * δ * natMass w := by
  apply D.slabIntersection_loss_le_sum.trans
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (sum_three_pow_succ_le k) hδ) (Nat.cast_nonneg _)

/--
@isnad1 id=le.2h8v.s11.3f232810343b from=translated src=- shape=0ce476c8 vocab=1cf7f0a3
-/
theorem slabIntersection_loss_le_dimension (hδ : 0 ≤ δ) (hkd : k ≤ d) :
    (natMass w : ℝ) - natMass (restrictWeight w (slabIntersection k D.direction t)) ≤
      (3 : ℝ) ^ (d + 1) * δ * natMass w := by
  apply (D.slabIntersection_loss_le hδ).trans
  have hpow : (3 : ℝ) ^ (k + 1) ≤ 3 ^ (d + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hkd 1)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right (by linarith) hδ

/--
@isnad1 id=le.2h8v.s11.42c9a796c1cd from=translated src=- shape=faf7d57d vocab=1cf7f0a3
-/
theorem slabIntersection_retainedMass_ge (hδ : 0 ≤ δ) (hkd : k ≤ d) :
    (1 - (3 : ℝ) ^ (d + 1) * δ) * natMass w ≤
      (natMass (restrictWeight w (slabIntersection k D.direction t)) : ℝ) :=
  restrictWeight_retainedMass_ge _ _ _ (D.slabIntersection_loss_le_dimension hδ hkd)

/--
@isnad1 id=ex.4h8v.s11.a226b132823d from=translated src=- shape=64d4d9cc vocab=9db128ee
-/
theorem slabIntersection_nonzero (hδ : 0 ≤ δ) (hkd : k ≤ d)
    (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1) (hw : ∃ v, w v ≠ 0) :
    ∃ v, restrictWeight w (slabIntersection k D.direction t) v ≠ 0 :=
  restrictWeight_nonzero_of_loss_lt_one _ _ _ hw hsmall
    (D.slabIntersection_loss_le_dimension hδ hkd)

/-- The geometric error budget leaves thickness `δ` after intersecting all
chosen slabs. No monotonicity assumptions on the widths are needed.
@isnad1 id=isthicka.2h9v.s11.e47f93a5339b from=translated src=- shape=6d388c7f vocab=c52ce7d0
-/
theorem thick_slabIntersection (hδ : 0 ≤ δ)
    {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p}
    (hthick : IsThickAlong w ξ (t (k + 1)) ((3 : ℝ) ^ (k + 1) * δ)) :
    IsThickAlong (restrictWeight w (slabIntersection k D.direction t)) ξ (t (k + 1)) δ := by
  have hpow : (1 : ℝ) ≤ 3 ^ (k + 1) := one_le_pow₀ (by norm_num)
  have heq : (3 : ℝ) ^ (k + 1) * δ - ((3 : ℝ) ^ (k + 1) - 1) * δ / 1 = δ := by ring
  have h := hthick.of_pruning (restrictWeight_le _ _) (ε := 1) (M := natMass w)
    (by norm_num) (mul_nonneg (sub_nonneg.mpr hpow) hδ) (by simp)
    (D.slabIntersection_loss_le hδ) (by rw [heq]; exact hδ)
  rwa [heq] at h

/--
@isnad1 id=isthicka.3h9v.s12.8826bfbe74b9 from=translated src=- shape=3fbcc69e vocab=a94ff552
-/
theorem thick_slabIntersection_of_maximal (hδ : 0 ≤ δ)
    (hmax : ∀ ξ, ξ ∉ D.space k → IsThickAlong w ξ (t (k + 1)) ((3 : ℝ) ^ (k + 1) * δ))
    (ξ : FpCoord p d →ᵃ[ZMod p] ZMod p) (hξ : ξ ∉ D.space k) :
    IsThickAlong (restrictWeight w (slabIntersection k D.direction t)) ξ (t (k + 1)) δ :=
  D.thick_slabIntersection hδ (hmax ξ hξ)

end DirectionChain

/-- A small bounded representative agrees with the centered representative.
@isnad1 id=le.2h3v.s5.c5f08d29bfba from=translated src=- shape=2c517532 vocab=b190f9c7
-/
theorem HasBoundedRepresentative.valMinAbs_natAbs_le {p K : ℕ} [NeZero p]
    {a : ZMod p} (ha : HasBoundedRepresentative p K a) (hK : 2 * K < p) :
    a.valMinAbs.natAbs ≤ K := by
  obtain ⟨z, hz, hza⟩ := ha
  have hval : a.valMinAbs = z := (ZMod.valMinAbs_spec a z).mpr ⟨hza.symm, by
    constructor <;> omega⟩
  rwa [hval]

/-- Integer coordinates supplied by the selected affine functionals.-/
def slabCoordinates {p d : ℕ} (k : ℕ)
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p) (v : FpCoord p d) : IntCoord k :=
  fun i ↦ (ξ i v).valMinAbs

/--
@isnad1 id=eq.0h5v.s8.6c745d2de341 from=translated src=- shape=752e82cc vocab=c15cd461
-/
@[simp]
theorem slabCoordinates_mod {p d k : ℕ}
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p) (v : FpCoord p d) :
    (slabCoordinates k ξ v).mod p = fun i : Fin k ↦ ξ i v := by
  funext i
  exact ZMod.coe_valMinAbs _

/--
@isnad1 id=le.2h7v.s7.ebb3826a256f from=translated src=- shape=d96a98b5 vocab=04d17d41
-/
theorem slabCoordinates_apply_bound {p d k : ℕ} [NeZero p]
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p) (t : ℕ → ℕ)
    {v : FpCoord p d} (hv : v ∈ slabIntersection k ξ t)
    (i : Fin k) (hsmall : 2 * t (i + 1) < p) :
    (slabCoordinates k ξ v i).natAbs ≤ t (i + 1) :=
  (hv i).valMinAbs_natAbs_le hsmall

/--
@isnad1 id=le.3h6v.s7.297e70a8fc70 from=translated src=- shape=48f922fa vocab=746e6b0e
-/
theorem slabCoordinates_bound {p d k : ℕ} [NeZero p]
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p) (t : ℕ → ℕ)
    (ht : Monotone t) (hsmall : ∀ i : Fin k, 2 * t (i + 1) < p)
    {v : FpCoord p d} (hv : v ∈ slabIntersection k ξ t) :
    latticeSupNorm (slabCoordinates k ξ v) ≤ t k := by
  rw [latticeSupNorm_le_iff]
  intro i
  exact (slabCoordinates_apply_bound ξ t hv i (hsmall i)).trans (ht (by omega))

end EGZ
