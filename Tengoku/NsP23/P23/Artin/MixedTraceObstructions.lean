import Tengoku.NsP23.P23.Artin.CanonicalRelations
import Tengoku.NsP23.P23.Artin.Trace
import Tengoku.NsP23.P23.OneTie.MixedCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact mixed survivor-family trace obstructions

Direct coefficient contradictions for the Run-03 YZ, YQ, ZP, and PQ
families.  This file does not contain an arbitrary-dominant reduction.
-/

namespace P23.Artin

noncomputable section

open P23.OneTie

variable {k : Type*} [Field k]

private theorem a_pos_of_neZero {a : ℕ} [NeZero a] : 0 < a :=
  Nat.pos_of_ne_zero (NeZero.ne a)

/-! ## M3 / YZ -/

/--
@isnad1 id=other.3h3v.s6.f0e74bb3f373 from=translated src=- shape=577c182e vocab=1635193c
-/
theorem mixedYZ_card_eq_three {a u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    let hr : 0 < a - 1 := by omega
    (mixedSoclesYZ (a := a) (b := 1) (c := 1) 0 u v hr).card = 3 := by
  dsimp
  simp [mixedSoclesYZ, mixedCore, mixedY, mixedZ, Normal.ext_iff]

/--
@isnad1 id=other.3h3v.s6.811b472e148c from=translated src=- shape=e5de9932 vocab=6a53d9d4
-/
theorem mixedYZ_isRootAntichain {a u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    let hr : 0 < a - 1 := by omega
    IsRootAntichain
      (mixedSoclesYZ (a := a) (b := 1) (c := 1) 0 u v hr) := by
  dsimp
  simp only [IsRootAntichain]
  intro p hp q hq hpq
  simp only [mixedSoclesYZ, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  all_goals
    simp_all [Normal.exact_divides_iff, Normal.DividesCriterion,
      mixedCore, mixedY, mixedZ, Normal.ext_iff]
  all_goals omega

/--
@isnad1 id=other.3h3v.s6.6b683f1be067 from=translated src=- shape=e5de9932 vocab=d3e8cb01
-/
theorem mixedYZ_isLiveTie {a u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    let hr : 0 < a - 1 := by omega
    IsLiveTie (mixedSoclesYZ (a := a) (b := 1) (c := 1) 0 u v hr) := by
  dsimp
  simp [IsLiveTie, standardSet, mixedSoclesYZ, liveTiePoint,
    Normal.exact_divides_iff, Normal.DividesCriterion,
    mixedCore, mixedY, mixedZ, Normal.xGenerator,
    show a ≠ 1 by omega, Normal.yGenerator, Normal.zGenerator]
  omega

/--
@isnad1 id=other.3h4v.s9.73efaf3b7787 from=translated src=- shape=72728808 vocab=41b274e3
-/
theorem mixedYZ_y_not_mem_trace {a u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    let hr : 0 < a - 1 := by omega
    let S := mixedSoclesYZ (a := a) (b := 1) (c := 1) 0 u v hr
    let hyS : (Normal.yGenerator : Normal a 1 1) ∈ standardFinset S :=
      (mem_standardFinset_iff_standardSet S _).2
        (mixedYZ_isLiveTie ha hu hv).2.1
    X (k := k) S Normal.yGenerator hyS ∉ TraceSubmodule k S := by
  dsimp only
  let hr : 0 < a - 1 := by omega
  let S := mixedSoclesYZ (a := a) (b := 1) (c := 1) 0 u v hr
  let C : Normal a 1 1 := mixedCore 0 u v (by omega)
  let Y : Normal a 1 1 := mixedY u
  let Z : Normal a 1 1 := mixedZ v
  have hC : C ∈ S := by simp [S, C, mixedSoclesYZ]
  have hY : Y ∈ S := by simp [S, Y, mixedSoclesYZ]
  have hZ : Z ∈ S := by simp [S, Z, mixedSoclesYZ]
  have hcard3 : S.card = 3 := mixedYZ_card_eq_three ha hu hv
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hanti : IsRootAntichain S := mixedYZ_isRootAntichain ha hu hv
  have hlive : IsLiveTie S := mixedYZ_isLiveTie ha hu hv
  have hyS : (Normal.yGenerator : Normal a 1 1) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.2.1
  have hzS : (Normal.zGenerator : Normal a 1 1) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.2.2.1
  let zv : Normal a 1 1 := ⟨0, 0, v, a_pos_of_neZero⟩
  let yu : Normal a 1 1 := ⟨0, u, 0, a_pos_of_neZero⟩
  let yzv : Normal a 1 1 := ⟨0, 1, v, a_pos_of_neZero⟩
  let yz : Normal a 1 1 := ⟨0, 1, 1, a_pos_of_neZero⟩
  let yy : Normal a 1 1 := ⟨0, 2, 0, a_pos_of_neZero⟩
  have hzvS : zv ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet]
    rw [mem_standardSet_mixedSoclesYZ_iff (hb := by omega) (hc := by omega)
      (hu := hu) (hv := hv) (hr := hr)]
    simp [zv]
  have hyuS : yu ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet]
    rw [mem_standardSet_mixedSoclesYZ_iff (hb := by omega) (hc := by omega)
      (hu := hu) (hv := hv) (hr := hr)]
    simp [yu]
  have hyzvS : yzv ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet]
    rw [mem_standardSet_mixedSoclesYZ_iff (hb := by omega) (hc := by omega)
      (hu := hu) (hv := hv) (hr := hr)]
    simp [yzv]
    omega
  have hyzS : yz ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet]
    rw [mem_standardSet_mixedSoclesYZ_iff (hb := by omega) (hc := by omega)
      (hu := hu) (hv := hv) (hr := hr)]
    simp [yz]
    omega
  have hyyS : yy ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet]
    rw [mem_standardSet_mixedSoclesYZ_iff (hb := by omega) (hc := by omega)
      (hu := hu) (hv := hv) (hr := hr)]
    simp [yy]
    omega
  intro htrace
  obtain ⟨F, s, hs, hcoeff⟩ :=
    exists_root_image_with_variable_coeff_of_mem_trace (k := k) S
      hS (by omega) hanti
      (by exact ⟨ha, Or.inl ⟨by omega, by omega⟩⟩) .y hyS htrace
  have hs' : s = C ∨ s = Y ∨ s = Z := by
    simpa [S, C, Y, Z, mixedSoclesYZ] using hs
  rcases hs' with rfl | rfl | rfl
  · let mi : MonomialIndex S := ⟨zv, hzvS⟩
    let ni : MonomialIndex S := ⟨Normal.yGenerator, hyS⟩
    let qi : MonomialIndex S := ⟨yu, hyuS⟩
    let ei : MonomialIndex S := ⟨Normal.yGenerator, hyS⟩
    let hi : MonomialIndex S := ⟨zv, hzvS⟩
    let wi : MonomialIndex S := ⟨yzv, hyzvS⟩
    have htransfer := coeff_transfer_of_common_quotient (k := k) S F
      mi ni qi ei hi wi (rootIndex S C hC) (rootIndex S Y hY)
      (by apply Normal.ext <;> simp [mi, qi, C, zv, yu, mixedCore, rootIndex])
      (by apply Normal.ext <;>
        simp [ni, qi, Y, yu, mixedY, Normal.yGenerator, rootIndex] <;> omega)
      (by apply Normal.ext <;> simp [mi, ei, wi, zv, yzv, Normal.yGenerator])
      (by apply Normal.ext <;> simp [ni, hi, wi, zv, yzv, Normal.yGenerator])
    have hnot : ¬(Normal.zGenerator : Normal a 1 1) ∣ Y := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.zGenerator, Y, mixedY]
    have hzero : X (k := k) S Normal.zGenerator hzS •
        U (k := k) S (rootIndex S Y hY) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S Y hY
        (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)).2 hnot
    have hzcoeff := coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S) hi (rootIndex S Z hZ)
      (rootIndex S Y hY) hzero
      (by apply Normal.ext <;>
        simp [hi, Z, zv, mixedZ, Normal.zGenerator, rootIndex] <;> omega)
    exact hcoeff (htransfer.trans hzcoeff)
  · have hnot : ¬(Normal.zGenerator : Normal a 1 1) ∣ Y := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.zGenerator, Y, mixedY]
    have hzero : X (k := k) S Normal.zGenerator hzS •
        U (k := k) S (rootIndex S Y hY) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S Y hY
        (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)).2 hnot
    have hvanish := coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S) ⟨yz, hyzS⟩
      (rootIndex S Y hY) hzero
      (by apply Normal.ext <;> simp [yz, Normal.yGenerator, Normal.zGenerator])
    exact hcoeff hvanish
  · have hnot : ¬(Normal.yGenerator : Normal a 1 1) ∣ Z := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.yGenerator, Z, mixedZ]
    have hzero : X (k := k) S Normal.yGenerator hyS •
        U (k := k) S (rootIndex S Z hZ) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S Z hZ
        (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)).2 hnot
    have hvanish := coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S) ⟨yy, hyyS⟩
      (rootIndex S Z hZ) hzero
      (by apply Normal.ext <;> simp [yy, Normal.yGenerator])
    exact hcoeff hvanish

/-! ## M4 / YQ -/

/--
@isnad1 id=eq.5h5v.s6.64168494076a from=translated src=- shape=57a021c4 vocab=cf203be6
-/
theorem mixedYQ_card_eq_three {a b r u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hu : b ≤ u) (hv : 1 ≤ v)
    (hr : r < a - 1) :
    (mixedSoclesYQ (a := a) (b := b) (c := 1) r u v hr).card = 3 := by
  simp [mixedSoclesYQ, mixedCore, mixedY, mixedQ, Normal.ext_iff]

/--
@isnad1 id=isrootan.5h5v.s6.014054fa8fcc from=translated src=- shape=5b4df898 vocab=2fe6da69
-/
theorem mixedYQ_isRootAntichain {a b r u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hu : b ≤ u) (hv : 1 ≤ v)
    (hr : r < a - 1) :
    IsRootAntichain
      (mixedSoclesYQ (a := a) (b := b) (c := 1) r u v hr) := by
  simp only [IsRootAntichain]
  intro p hp q hq hpq
  simp only [mixedSoclesYQ, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  all_goals
    simp_all [Normal.exact_divides_iff, Normal.DividesCriterion,
      mixedCore, mixedY, mixedQ, Normal.ext_iff]
  all_goals omega

/--
@isnad1 id=isliveti.5h5v.s6.2ad3fb27bce9 from=translated src=- shape=5b4df898 vocab=e881ca99
-/
theorem mixedYQ_isLiveTie {a b r u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hu : b ≤ u) (hv : 1 ≤ v)
    (hr : r < a - 1) :
    IsLiveTie (mixedSoclesYQ (a := a) (b := b) (c := 1) r u v hr) := by
  simp [IsLiveTie, standardSet, mixedSoclesYQ, liveTiePoint,
    Normal.exact_divides_iff, Normal.DividesCriterion,
    mixedCore, mixedY, mixedQ, Normal.xGenerator,
    show a ≠ 1 by omega, Normal.yGenerator, Normal.zGenerator]
  omega

/--
@isnad1 id=other.5h6v.s9.207a87f58fc5 from=translated src=- shape=d2003c91 vocab=5fccab75
-/
theorem mixedYQ_y_not_mem_trace {a b r u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hu : b ≤ u) (hv : 1 ≤ v)
    (hr : r < a - 1) :
    let S := mixedSoclesYQ (a := a) (b := b) (c := 1) r u v hr
    let hyS : (Normal.yGenerator : Normal a b 1) ∈ standardFinset S :=
      (mem_standardFinset_iff_standardSet S _).2
        (mixedYQ_isLiveTie ha hb hu hv hr).2.1
    X (k := k) S Normal.yGenerator hyS ∉ TraceSubmodule k S := by
  dsimp only
  let S := mixedSoclesYQ (a := a) (b := b) (c := 1) r u v hr
  let C : Normal a b 1 := mixedCore r u v (by omega)
  let Y : Normal a b 1 := mixedY u
  let Q : Normal a b 1 := mixedQ r v hr
  have hC : C ∈ S := by simp [S, C, mixedSoclesYQ]
  have hY : Y ∈ S := by simp [S, Y, mixedSoclesYQ]
  have hQ : Q ∈ S := by simp [S, Q, mixedSoclesYQ]
  have hcard3 : S.card = 3 := mixedYQ_card_eq_three ha hb hu hv hr
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hanti : IsRootAntichain S := mixedYQ_isRootAntichain ha hb hu hv hr
  have hlive : IsLiveTie S := mixedYQ_isLiveTie ha hb hu hv hr
  have hxS : (Normal.xGenerator : Normal a b 1) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.1
  have hyS : (Normal.yGenerator : Normal a b 1) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.2.1
  have hzS : (Normal.zGenerator : Normal a b 1) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.2.2.1
  let m : Normal a b 1 := ⟨r, 0, v, by omega⟩
  let q : Normal a b 1 := ⟨0, u, 0, a_pos_of_neZero⟩
  let w : Normal a b 1 := ⟨r, 1, v, by omega⟩
  let yz : Normal a b 1 := ⟨0, 1, 1, a_pos_of_neZero⟩
  let yy : Normal a b 1 := ⟨0, 2, 0, a_pos_of_neZero⟩
  have hmS : m ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesYQ_iff hb (by omega) hu hv hr]
    simp [m, mixedYQStandardNat]
  have hqS : q ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesYQ_iff hb (by omega) hu hv hr]
    simp [q, mixedYQStandardNat]
  have hwS : w ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesYQ_iff hb (by omega) hu hv hr]
    simp [w, mixedYQStandardNat]
    omega
  have hyzS : yz ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesYQ_iff hb (by omega) hu hv hr]
    simp [yz, mixedYQStandardNat]
    omega
  have hyyS : yy ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesYQ_iff hb (by omega) hu hv hr]
    simp [yy, mixedYQStandardNat]
    omega
  intro htrace
  obtain ⟨F, s, hs, hcoeff⟩ :=
    exists_root_image_with_variable_coeff_of_mem_trace (k := k) S hS
      (by omega) hanti (by exact ⟨ha, Or.inl ⟨hb, by omega⟩⟩) .y hyS htrace
  have hs' : s = C ∨ s = Y ∨ s = Q := by
    simpa [S, C, Y, Q, mixedSoclesYQ] using hs
  rcases hs' with rfl | rfl | rfl
  · have hrlt : r < a := by omega
    have hr1lt : 1 + r < a := by omega
    have htransfer := coeff_transfer_of_common_quotient (k := k) S F
      (⟨m, hmS⟩ : MonomialIndex S)
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)
      (⟨q, hqS⟩ : MonomialIndex S)
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)
      (⟨m, hmS⟩ : MonomialIndex S) (⟨w, hwS⟩ : MonomialIndex S)
      (rootIndex S C hC) (rootIndex S Y hY)
      (by apply Normal.ext <;>
        simp [m, q, C, mixedCore, rootIndex, Nat.mod_eq_of_lt hrlt,
          Nat.div_eq_of_lt hrlt])
      (by apply Normal.ext <;>
        simp [q, Y, mixedY, Normal.yGenerator, rootIndex] <;> omega)
      (by apply Normal.ext <;>
        simp [m, w, Normal.yGenerator, Nat.mod_eq_of_lt hrlt,
          Nat.div_eq_of_lt hrlt])
      (by apply Normal.ext <;>
        simp [m, w, Normal.yGenerator, Nat.mod_eq_of_lt hrlt,
          Nat.div_eq_of_lt hrlt])
    have hnot : ¬(Normal.xGenerator : Normal a b 1) ∣ Y := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.xGenerator, show a ≠ 1 by omega, Y, mixedY]
    have hzero : X (k := k) S Normal.xGenerator hxS •
        U (k := k) S (rootIndex S Y hY) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S Y hY
        (⟨Normal.xGenerator, hxS⟩ : MonomialIndex S)).2 hnot
    have hvanish := coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.xGenerator, hxS⟩ : MonomialIndex S)
      (⟨m, hmS⟩ : MonomialIndex S) (rootIndex S Q hQ)
      (rootIndex S Y hY) hzero
      (by apply Normal.ext <;>
        simp [m, Q, mixedQ, Normal.xGenerator, show a ≠ 1 by omega,
          rootIndex, Nat.mod_eq_of_lt hr1lt,
          Nat.div_eq_of_lt hr1lt] <;> omega)
    exact hcoeff (htransfer.trans hvanish)
  · have hnot : ¬(Normal.zGenerator : Normal a b 1) ∣ Y := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.zGenerator, Y, mixedY]
    have hzero : X (k := k) S Normal.zGenerator hzS •
        U (k := k) S (rootIndex S Y hY) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S Y hY
        (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)).2 hnot
    exact hcoeff (coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S) ⟨yz, hyzS⟩
      (rootIndex S Y hY) hzero
      (by apply Normal.ext <;> simp [yz, Normal.yGenerator, Normal.zGenerator]))
  · have hnot : ¬(Normal.yGenerator : Normal a b 1) ∣ Q := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.yGenerator, Q, mixedQ]
    have hzero : X (k := k) S Normal.yGenerator hyS •
        U (k := k) S (rootIndex S Q hQ) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S Q hQ
        (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)).2 hnot
    exact hcoeff (coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S) ⟨yy, hyyS⟩
      (rootIndex S Q hQ) hzero
      (by apply Normal.ext <;> simp [yy, Normal.yGenerator]))

/-! ## Reflected M4 / ZP, proved directly -/

/--
@isnad1 id=eq.5h5v.s6.ec879452cd8c from=translated src=- shape=73cf73af vocab=8927c9aa
-/
theorem mixedZP_card_eq_three {a c r u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hc : 1 ≤ c) (hu : 1 ≤ u) (hv : c ≤ v)
    (hr : r < a - 1) :
    (mixedSoclesZP (a := a) (b := 1) (c := c) r u v hr).card = 3 := by
  simp [mixedSoclesZP, mixedCore, mixedZ, mixedP, Normal.ext_iff]

/--
@isnad1 id=isrootan.5h5v.s6.7df6da431b8e from=translated src=- shape=a69f0007 vocab=21f37aff
-/
theorem mixedZP_isRootAntichain {a c r u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hc : 1 ≤ c) (hu : 1 ≤ u) (hv : c ≤ v)
    (hr : r < a - 1) :
    IsRootAntichain
      (mixedSoclesZP (a := a) (b := 1) (c := c) r u v hr) := by
  simp only [IsRootAntichain]
  intro p hp q hq hpq
  simp only [mixedSoclesZP, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  all_goals
    simp_all [Normal.exact_divides_iff, Normal.DividesCriterion,
      mixedCore, mixedZ, mixedP, Normal.ext_iff]
  all_goals omega

/--
@isnad1 id=isliveti.5h5v.s6.9442a1c11f7e from=translated src=- shape=a69f0007 vocab=6a4141ed
-/
theorem mixedZP_isLiveTie {a c r u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hc : 1 ≤ c) (hu : 1 ≤ u) (hv : c ≤ v)
    (hr : r < a - 1) :
    IsLiveTie (mixedSoclesZP (a := a) (b := 1) (c := c) r u v hr) := by
  simp [IsLiveTie, standardSet, mixedSoclesZP, liveTiePoint,
    Normal.exact_divides_iff, Normal.DividesCriterion,
    mixedCore, mixedZ, mixedP, Normal.xGenerator,
    show a ≠ 1 by omega, Normal.yGenerator, Normal.zGenerator]
  omega

/--
@isnad1 id=other.5h6v.s9.29cfecea499d from=translated src=- shape=32e70ed1 vocab=a01b9d65
-/
theorem mixedZP_z_not_mem_trace {a c r u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hc : 1 ≤ c) (hu : 1 ≤ u) (hv : c ≤ v)
    (hr : r < a - 1) :
    let S := mixedSoclesZP (a := a) (b := 1) (c := c) r u v hr
    let hzS : (Normal.zGenerator : Normal a 1 c) ∈ standardFinset S :=
      (mem_standardFinset_iff_standardSet S _).2
        (mixedZP_isLiveTie ha hc hu hv hr).2.2.1
    X (k := k) S Normal.zGenerator hzS ∉ TraceSubmodule k S := by
  dsimp only
  let S := mixedSoclesZP (a := a) (b := 1) (c := c) r u v hr
  let C : Normal a 1 c := mixedCore r u v (by omega)
  let Z : Normal a 1 c := mixedZ v
  let P : Normal a 1 c := mixedP r u hr
  have hC : C ∈ S := by simp [S, C, mixedSoclesZP]
  have hZ : Z ∈ S := by simp [S, Z, mixedSoclesZP]
  have hP : P ∈ S := by simp [S, P, mixedSoclesZP]
  have hcard3 : S.card = 3 := mixedZP_card_eq_three ha hc hu hv hr
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hanti : IsRootAntichain S := mixedZP_isRootAntichain ha hc hu hv hr
  have hlive : IsLiveTie S := mixedZP_isLiveTie ha hc hu hv hr
  have hxS : (Normal.xGenerator : Normal a 1 c) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.1
  have hyS : (Normal.yGenerator : Normal a 1 c) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.2.1
  have hzS : (Normal.zGenerator : Normal a 1 c) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.2.2.1
  let m : Normal a 1 c := ⟨r, u, 0, by omega⟩
  let q : Normal a 1 c := ⟨0, 0, v, a_pos_of_neZero⟩
  let w : Normal a 1 c := ⟨r, u, 1, by omega⟩
  let yz : Normal a 1 c := ⟨0, 1, 1, a_pos_of_neZero⟩
  let zz : Normal a 1 c := ⟨0, 0, 2, a_pos_of_neZero⟩
  have hmS : m ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet]
    simp [standardSet, S, mixedSoclesZP, Normal.exact_divides_iff,
      Normal.DividesCriterion, mixedCore, mixedZ, mixedP, m]
  have hqS : q ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet]
    simp [standardSet, S, mixedSoclesZP, Normal.exact_divides_iff,
      Normal.DividesCriterion, mixedCore, mixedZ, mixedP, q]
  have hwS : w ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet]
    simp [standardSet, S, mixedSoclesZP, Normal.exact_divides_iff,
      Normal.DividesCriterion, mixedCore, mixedZ, mixedP, w]
    omega
  have hyzS : yz ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet]
    simp [standardSet, S, mixedSoclesZP, Normal.exact_divides_iff,
      Normal.DividesCriterion, mixedCore, mixedZ, mixedP, yz]
    omega
  have hzzS : zz ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet]
    simp [standardSet, S, mixedSoclesZP, Normal.exact_divides_iff,
      Normal.DividesCriterion, mixedCore, mixedZ, mixedP, zz]
    omega
  intro htrace
  obtain ⟨F, s, hs, hcoeff⟩ :=
    exists_root_image_with_variable_coeff_of_mem_trace (k := k) S hS
      (by omega) hanti (by exact ⟨ha, Or.inl ⟨by omega, hc⟩⟩) .z hzS htrace
  have hs' : s = C ∨ s = Z ∨ s = P := by
    simpa [S, C, Z, P, mixedSoclesZP] using hs
  rcases hs' with rfl | rfl | rfl
  · have hrlt : r < a := by omega
    have hr1lt : 1 + r < a := by omega
    have htransfer := coeff_transfer_of_common_quotient (k := k) S F
      (⟨m, hmS⟩ : MonomialIndex S)
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)
      (⟨q, hqS⟩ : MonomialIndex S)
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)
      (⟨m, hmS⟩ : MonomialIndex S) (⟨w, hwS⟩ : MonomialIndex S)
      (rootIndex S C hC) (rootIndex S Z hZ)
      (by apply Normal.ext <;>
        simp [m, q, C, mixedCore, rootIndex, Nat.mod_eq_of_lt hrlt,
          Nat.div_eq_of_lt hrlt])
      (by apply Normal.ext <;>
        simp [q, Z, mixedZ, Normal.zGenerator, rootIndex] <;> omega)
      (by apply Normal.ext <;>
        simp [m, w, Normal.zGenerator, Nat.mod_eq_of_lt hrlt,
          Nat.div_eq_of_lt hrlt])
      (by apply Normal.ext <;>
        simp [m, w, Normal.zGenerator, Nat.mod_eq_of_lt hrlt,
          Nat.div_eq_of_lt hrlt])
    have hnot : ¬(Normal.xGenerator : Normal a 1 c) ∣ Z := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.xGenerator, show a ≠ 1 by omega, Z, mixedZ]
    have hzero : X (k := k) S Normal.xGenerator hxS •
        U (k := k) S (rootIndex S Z hZ) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S Z hZ
        (⟨Normal.xGenerator, hxS⟩ : MonomialIndex S)).2 hnot
    have hvanish := coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.xGenerator, hxS⟩ : MonomialIndex S)
      (⟨m, hmS⟩ : MonomialIndex S) (rootIndex S P hP)
      (rootIndex S Z hZ) hzero
      (by apply Normal.ext <;>
        simp [m, P, mixedP, Normal.xGenerator, show a ≠ 1 by omega,
          rootIndex, Nat.mod_eq_of_lt hr1lt,
          Nat.div_eq_of_lt hr1lt] <;> omega)
    exact hcoeff (htransfer.trans hvanish)
  · have hnot : ¬(Normal.yGenerator : Normal a 1 c) ∣ Z := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.yGenerator, Z, mixedZ]
    have hzero : X (k := k) S Normal.yGenerator hyS •
        U (k := k) S (rootIndex S Z hZ) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S Z hZ
        (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)).2 hnot
    exact hcoeff (coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S) ⟨yz, hyzS⟩
      (rootIndex S Z hZ) hzero
      (by apply Normal.ext <;> simp [yz, Normal.yGenerator, Normal.zGenerator]))
  · have hnot : ¬(Normal.zGenerator : Normal a 1 c) ∣ P := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.zGenerator, P, mixedP]
    have hzero : X (k := k) S Normal.zGenerator hzS •
        U (k := k) S (rootIndex S P hP) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S P hP
        (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)).2 hnot
    exact hcoeff (coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S) ⟨zz, hzzS⟩
      (rootIndex S P hP) hzero
      (by apply Normal.ext <;> simp [zz, Normal.zGenerator]))

/-! ## M5 / PQ -/

/--
@isnad1 id=other.5h5v.s6.e772b264e55e from=translated src=- shape=cf8046ee vocab=b253c9b1
-/
theorem mixedPQ_card_eq_three {a b c u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) :
    let hr : a - 2 < a - 1 := by omega
    (mixedSoclesPQ (a := a) (b := b) (c := c) (a - 2) u v hr).card = 3 := by
  dsimp
  let hr : a - 2 < a - 1 := by omega
  let C : Normal a b c := mixedCore (a - 2) u v (by omega)
  let P : Normal a b c := mixedP (a - 2) u hr
  let Q : Normal a b c := mixedQ (a - 2) v hr
  have hCP : C ≠ P := by
    intro h
    have hx := congrArg Normal.x h
    simp [C, P, mixedCore, mixedP] at hx
  have hCQ : C ≠ Q := by
    intro h
    have hx := congrArg Normal.x h
    simp [C, Q, mixedCore, mixedQ] at hx
  have hPQ : P ≠ Q := by
    intro h
    have hy := congrArg Normal.y h
    simp [P, Q, mixedP, mixedQ] at hy
    omega
  change ({C, P, Q} : Finset (Normal a b c)).card = 3
  simp [hCP, hCQ, hPQ]

/--
@isnad1 id=other.5h5v.s6.3e667d1e8bc8 from=translated src=- shape=6d53f629 vocab=27af7484
-/
theorem mixedPQ_isRootAntichain {a b c u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) :
    let hr : a - 2 < a - 1 := by omega
    IsRootAntichain
      (mixedSoclesPQ (a := a) (b := b) (c := c) (a - 2) u v hr) := by
  dsimp
  simp only [IsRootAntichain]
  intro p hp q hq hpq
  simp only [mixedSoclesPQ, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  all_goals
    simp_all [Normal.exact_divides_iff, Normal.DividesCriterion,
      mixedCore, mixedP, mixedQ, Normal.ext_iff]
  all_goals omega

/--
@isnad1 id=other.5h5v.s6.19f96c32684c from=translated src=- shape=6d53f629 vocab=bc1f628f
-/
theorem mixedPQ_isLiveTie {a b c u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) :
    let hr : a - 2 < a - 1 := by omega
    IsLiveTie
      (mixedSoclesPQ (a := a) (b := b) (c := c) (a - 2) u v hr) := by
  dsimp
  simp [IsLiveTie, standardSet, mixedSoclesPQ, liveTiePoint,
    Normal.exact_divides_iff, Normal.DividesCriterion,
    mixedCore, mixedP, mixedQ, Normal.xGenerator,
    show a ≠ 1 by omega, Normal.yGenerator, Normal.zGenerator]
  omega

/--
@isnad1 id=other.6h6v.s9.72a4333fe9f5 from=translated src=- shape=9aa8b238 vocab=cb7ec09b
-/
theorem mixedPQ_y_not_mem_trace_of_u_gt_one
    {a b c u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hu1 : 1 < u) :
    let hr : a - 2 < a - 1 := by omega
    let S := mixedSoclesPQ (a := a) (b := b) (c := c) (a - 2) u v hr
    let hyS : (Normal.yGenerator : Normal a b c) ∈ standardFinset S :=
      (mem_standardFinset_iff_standardSet S _).2
        (mixedPQ_isLiveTie ha hb hc hu hv).2.1
    X (k := k) S Normal.yGenerator hyS ∉ TraceSubmodule k S := by
  dsimp only
  let hr : a - 2 < a - 1 := by omega
  let S := mixedSoclesPQ (a := a) (b := b) (c := c) (a - 2) u v hr
  let C : Normal a b c := mixedCore (a - 2) u v (by omega)
  let P : Normal a b c := mixedP (a - 2) u hr
  let Q : Normal a b c := mixedQ (a - 2) v hr
  have hC : C ∈ S := by simp [S, C, mixedSoclesPQ]
  have hP : P ∈ S := by simp [S, P, mixedSoclesPQ]
  have hQ : Q ∈ S := by simp [S, Q, mixedSoclesPQ]
  have hcard3 : S.card = 3 := mixedPQ_card_eq_three ha hb hc hu hv
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hanti : IsRootAntichain S := mixedPQ_isRootAntichain ha hb hc hu hv
  have hlive : IsLiveTie S := mixedPQ_isLiveTie ha hb hc hu hv
  have hxS : (Normal.xGenerator : Normal a b c) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.1
  have hyS : (Normal.yGenerator : Normal a b c) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.2.1
  have hzS : (Normal.zGenerator : Normal a b c) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.2.2.1
  let m : Normal a b c := ⟨0, b - 1, v, a_pos_of_neZero⟩
  let q : Normal a b c := ⟨a - 2, u + 1 - b, 0, by omega⟩
  let w : Normal a b c := ⟨0, b, v, a_pos_of_neZero⟩
  let h : Normal a b c := ⟨a - 1, 0, v - c, by omega⟩
  let yz : Normal a b c := ⟨0, 1, 1, a_pos_of_neZero⟩
  let yy : Normal a b c := ⟨0, 2, 0, a_pos_of_neZero⟩
  have hmS : m ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr]
    simp [m, mixedPQStandardNat]
    omega
  have hqS : q ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr]
    simp [q, mixedPQStandardNat]
  have hwS : w ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr]
    simp [w, mixedPQStandardNat]
    omega
  have hhS : h ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr]
    simp [h, mixedPQStandardNat]
    omega
  have hyzS : yz ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr]
    simp [yz, mixedPQStandardNat]
    omega
  have hyyS : yy ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr]
    simp [yy, mixedPQStandardNat]
    omega
  intro htrace
  obtain ⟨F, s, hs, hcoeff⟩ :=
    exists_root_image_with_variable_coeff_of_mem_trace (k := k) S hS
      (by omega) hanti (by exact ⟨ha, Or.inl ⟨hb, hc⟩⟩) .y hyS htrace
  have hs' : s = C ∨ s = P ∨ s = Q := by
    simpa [S, C, P, Q, mixedSoclesPQ] using hs
  rcases hs' with rfl | rfl | rfl
  · have hrlt : a - 2 < a := by omega
    have hr1lt : 1 + (a - 2) < a := by omega
    have halast : a - 1 < a := by omega
    have hwrap : (Normal.xGenerator : Normal a b c) * h = w := by
      rw [mul_comm]
      simpa [h, w, Normal.wrappedXPredecessor] using
        (Normal.wrappedXPredecessor_mul w (by rfl) (by simp [w]) (by simp [w]; omega))
    have htransfer := coeff_transfer_of_common_quotient (k := k) S F
      (⟨m, hmS⟩ : MonomialIndex S)
      (⟨Normal.xGenerator, hxS⟩ : MonomialIndex S)
      (⟨q, hqS⟩ : MonomialIndex S)
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)
      (⟨h, hhS⟩ : MonomialIndex S) (⟨w, hwS⟩ : MonomialIndex S)
      (rootIndex S C hC) (rootIndex S P hP)
      (by apply Normal.ext <;>
        simp [m, q, C, mixedCore, rootIndex, Nat.mod_eq_of_lt hrlt,
          Nat.div_eq_of_lt hrlt] <;> omega)
      (by apply Normal.ext <;>
        simp [q, P, mixedP, Normal.xGenerator, show a ≠ 1 by omega,
          rootIndex, Nat.mod_eq_of_lt hr1lt,
          Nat.div_eq_of_lt hr1lt] <;> omega)
      (by apply Normal.ext <;> simp [m, w, Normal.yGenerator] <;> omega)
      hwrap
    have hnot : ¬(Normal.zGenerator : Normal a b c) ∣ P := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.zGenerator, P, mixedP]
    have hzero : X (k := k) S Normal.zGenerator hzS •
        U (k := k) S (rootIndex S P hP) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S P hP
        (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)).2 hnot
    have hvanish := coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)
      (⟨h, hhS⟩ : MonomialIndex S) (rootIndex S Q hQ)
      (rootIndex S P hP) hzero
      (by apply Normal.ext <;>
        simp [h, Q, mixedQ, Normal.zGenerator, rootIndex,
          Nat.mod_eq_of_lt halast, Nat.div_eq_of_lt halast] <;> omega)
    exact hcoeff (htransfer.trans hvanish)
  · have hnot : ¬(Normal.zGenerator : Normal a b c) ∣ P := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.zGenerator, P, mixedP]
    have hzero : X (k := k) S Normal.zGenerator hzS •
        U (k := k) S (rootIndex S P hP) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S P hP
        (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)).2 hnot
    exact hcoeff (coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S) ⟨yz, hyzS⟩
      (rootIndex S P hP) hzero
      (by apply Normal.ext <;> simp [yz, Normal.yGenerator, Normal.zGenerator]))
  · have hnot : ¬(Normal.yGenerator : Normal a b c) ∣ Q := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.yGenerator, Q, mixedQ]
    have hzero : X (k := k) S Normal.yGenerator hyS •
        U (k := k) S (rootIndex S Q hQ) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S Q hQ
        (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)).2 hnot
    exact hcoeff (coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S) ⟨yy, hyyS⟩
      (rootIndex S Q hQ) hzero
      (by apply Normal.ext <;> simp [yy, Normal.yGenerator]))

/--
@isnad1 id=other.6h6v.s9.ed97bf666a02 from=translated src=- shape=3b469f91 vocab=cb7ec09b
-/
theorem mixedPQ_z_not_mem_trace_of_v_gt_one
    {a b c u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hv1 : 1 < v) :
    let hr : a - 2 < a - 1 := by omega
    let S := mixedSoclesPQ (a := a) (b := b) (c := c) (a - 2) u v hr
    let hzS : (Normal.zGenerator : Normal a b c) ∈ standardFinset S :=
      (mem_standardFinset_iff_standardSet S _).2
        (mixedPQ_isLiveTie ha hb hc hu hv).2.2.1
    X (k := k) S Normal.zGenerator hzS ∉ TraceSubmodule k S := by
  dsimp only
  let hr : a - 2 < a - 1 := by omega
  let S := mixedSoclesPQ (a := a) (b := b) (c := c) (a - 2) u v hr
  let C : Normal a b c := mixedCore (a - 2) u v (by omega)
  let P : Normal a b c := mixedP (a - 2) u hr
  let Q : Normal a b c := mixedQ (a - 2) v hr
  have hC : C ∈ S := by simp [S, C, mixedSoclesPQ]
  have hP : P ∈ S := by simp [S, P, mixedSoclesPQ]
  have hQ : Q ∈ S := by simp [S, Q, mixedSoclesPQ]
  have hcard3 : S.card = 3 := mixedPQ_card_eq_three ha hb hc hu hv
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hanti : IsRootAntichain S := mixedPQ_isRootAntichain ha hb hc hu hv
  have hlive : IsLiveTie S := mixedPQ_isLiveTie ha hb hc hu hv
  have hxS : (Normal.xGenerator : Normal a b c) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.1
  have hyS : (Normal.yGenerator : Normal a b c) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.2.1
  have hzS : (Normal.zGenerator : Normal a b c) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.2.2.1
  let m : Normal a b c := ⟨0, u, c - 1, a_pos_of_neZero⟩
  let q : Normal a b c := ⟨a - 2, 0, v + 1 - c, by omega⟩
  let w : Normal a b c := ⟨0, u, c, a_pos_of_neZero⟩
  let h : Normal a b c := ⟨a - 1, u - b, 0, by omega⟩
  let yz : Normal a b c := ⟨0, 1, 1, a_pos_of_neZero⟩
  let zz : Normal a b c := ⟨0, 0, 2, a_pos_of_neZero⟩
  have hmS : m ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr]
    simp [m, mixedPQStandardNat]
    omega
  have hqS : q ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr]
    simp [q, mixedPQStandardNat]
  have hwS : w ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr]
    simp [w, mixedPQStandardNat]
    omega
  have hhS : h ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr]
    simp [h, mixedPQStandardNat]
    omega
  have hyzS : yz ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr]
    simp [yz, mixedPQStandardNat]
    omega
  have hzzS : zz ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,
      mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr]
    simp [zz, mixedPQStandardNat]
    omega
  intro htrace
  obtain ⟨F, s, hs, hcoeff⟩ :=
    exists_root_image_with_variable_coeff_of_mem_trace (k := k) S hS
      (by omega) hanti (by exact ⟨ha, Or.inl ⟨hb, hc⟩⟩) .z hzS htrace
  have hs' : s = C ∨ s = P ∨ s = Q := by
    simpa [S, C, P, Q, mixedSoclesPQ] using hs
  rcases hs' with rfl | rfl | rfl
  · have hrlt : a - 2 < a := by omega
    have hr1lt : 1 + (a - 2) < a := by omega
    have halast : a - 1 < a := by omega
    have hwrap : (Normal.xGenerator : Normal a b c) * h = w := by
      rw [mul_comm]
      simpa [h, w, Normal.wrappedXPredecessor] using
        (Normal.wrappedXPredecessor_mul w (by rfl) (by simp [w]; omega) (by simp [w]))
    have htransfer := coeff_transfer_of_common_quotient (k := k) S F
      (⟨m, hmS⟩ : MonomialIndex S)
      (⟨Normal.xGenerator, hxS⟩ : MonomialIndex S)
      (⟨q, hqS⟩ : MonomialIndex S)
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)
      (⟨h, hhS⟩ : MonomialIndex S) (⟨w, hwS⟩ : MonomialIndex S)
      (rootIndex S C hC) (rootIndex S Q hQ)
      (by apply Normal.ext <;>
        simp [m, q, C, mixedCore, rootIndex, Nat.mod_eq_of_lt hrlt,
          Nat.div_eq_of_lt hrlt] <;> omega)
      (by apply Normal.ext <;>
        simp [q, Q, mixedQ, Normal.xGenerator, show a ≠ 1 by omega,
          rootIndex, Nat.mod_eq_of_lt hr1lt,
          Nat.div_eq_of_lt hr1lt] <;> omega)
      (by apply Normal.ext <;> simp [m, w, Normal.zGenerator] <;> omega)
      hwrap
    have hnot : ¬(Normal.yGenerator : Normal a b c) ∣ Q := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.yGenerator, Q, mixedQ]
    have hzero : X (k := k) S Normal.yGenerator hyS •
        U (k := k) S (rootIndex S Q hQ) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S Q hQ
        (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)).2 hnot
    have hvanish := coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)
      (⟨h, hhS⟩ : MonomialIndex S) (rootIndex S P hP)
      (rootIndex S Q hQ) hzero
      (by apply Normal.ext <;>
        simp [h, P, mixedP, Normal.yGenerator, rootIndex,
          Nat.mod_eq_of_lt halast, Nat.div_eq_of_lt halast] <;> omega)
    exact hcoeff (htransfer.trans hvanish)
  · have hnot : ¬(Normal.zGenerator : Normal a b c) ∣ P := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.zGenerator, P, mixedP]
    have hzero : X (k := k) S Normal.zGenerator hzS •
        U (k := k) S (rootIndex S P hP) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S P hP
        (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)).2 hnot
    exact hcoeff (coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S) ⟨zz, hzzS⟩
      (rootIndex S P hP) hzero
      (by apply Normal.ext <;> simp [zz, Normal.zGenerator]))
  · have hnot : ¬(Normal.yGenerator : Normal a b c) ∣ Q := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.yGenerator, Q, mixedQ]
    have hzero : X (k := k) S Normal.yGenerator hyS •
        U (k := k) S (rootIndex S Q hQ) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S Q hQ
        (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)).2 hnot
    exact hcoeff (coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S) ⟨yz, hyzS⟩
      (rootIndex S Q hQ) hzero
      (by apply Normal.ext <;> simp [yz, Normal.yGenerator, Normal.zGenerator]))

/--
@isnad1 id=other.6h7v.s7.0330c9fae763 from=translated src=- shape=ae93d04b vocab=7128dec6
-/
theorem mixedPQ_not_variablesInTrace
    {a b c u v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (huv : 1 < u ∨ 1 < v)
    (hlive :
      let hr : a - 2 < a - 1 := by omega
      IsLiveTie
        (mixedSoclesPQ (a := a) (b := b) (c := c) (a - 2) u v hr)) :
    let hr : a - 2 < a - 1 := by omega
    let S := mixedSoclesPQ (a := a) (b := b) (c := c) (a - 2) u v hr
    ¬VariablesInTrace k S hlive := by
  dsimp only at hlive ⊢
  intro htrace
  rcases huv with hu1 | hv1
  · exact mixedPQ_y_not_mem_trace_of_u_gt_one (k := k) ha hb hc hu hv hu1 htrace.2.1
  · exact mixedPQ_z_not_mem_trace_of_v_gt_one (k := k) ha hb hc hu hv hv1 htrace.2.2
end

end P23.Artin
