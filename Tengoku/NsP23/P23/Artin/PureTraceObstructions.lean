import Tengoku.NsP23.P23.Artin.MixedTraceObstructions
import Tengoku.NsP23.P23.OneTie.NonDominantRows

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact pure survivor-family trace obstructions

Direct coefficient contradictions for the Run-04 P4Z and P5Z families,
followed by the Run-10 exact-family summary API.  No reduction from an
arbitrary dominant configuration is asserted here.
-/

namespace P23.Artin

noncomputable section

open P23.OneTie

variable {k : Type*} [Field k]

private theorem a_pos_of_neZero {a : ℕ} [NeZero a] : 0 < a :=
  Nat.pos_of_ne_zero (NeZero.ne a)

/-! ## P4Z -/

/--
@isnad1 id=eq.3h3v.s6.25c9898a0507 from=translated src=- shape=ee7544ed vocab=9b823c05
-/
theorem p4Z_card_eq_three {a b V : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V) :
    (p4ZSocles (a := a) (b := b) ha V).card = 3 := by
  let C : Normal a b 0 := ⟨0, b, 0, a_pos_of_neZero⟩
  let P : Normal a b 0 := ⟨0, b - 1, V, a_pos_of_neZero⟩
  let Z : Normal a b 0 := ⟨0, 0, V + 1, a_pos_of_neZero⟩
  have hCP : C ≠ P := by
    intro h
    have hz := congrArg Normal.z h
    simp [C, P] at hz
    omega
  have hCZ : C ≠ Z := by
    intro h
    have hy := congrArg Normal.y h
    simp [C, Z] at hy
    omega
  have hPZ : P ≠ Z := by
    intro h
    have hy := congrArg Normal.y h
    simp [P, Z] at hy
    omega
  change ({C, P, Z} : Finset (Normal a b 0)).card = 3
  simp [hCP, hCZ, hPZ]

/--
@isnad1 id=isrootan.3h3v.s5.3121bb910e22 from=translated src=- shape=bbb4277c vocab=470079a4
-/
theorem p4Z_isRootAntichain {a b V : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V) :
    IsRootAntichain (p4ZSocles (a := a) (b := b) ha V) := by
  simp only [IsRootAntichain]
  intro p hp q hq hpq
  simp only [p4ZSocles, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  all_goals
    simp_all [Normal.exact_divides_iff, Normal.DividesCriterion, Normal.ext_iff]
  all_goals omega

/--
@isnad1 id=isliveti.3h3v.s5.bf9345b96dfd from=translated src=- shape=bbb4277c vocab=70f4aa47
-/
theorem p4Z_isLiveTie {a b V : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V) :
    IsLiveTie (p4ZSocles (a := a) (b := b) ha V) := by
  simp [IsLiveTie, standardSet, p4ZSocles, liveTiePoint,
    Normal.exact_divides_iff, Normal.DividesCriterion,
    Normal.xGenerator, show a ≠ 1 by omega,
    Normal.yGenerator, Normal.zGenerator]
  omega

/--
@isnad1 id=other.3h4v.s9.093a6cd8d30d from=translated src=- shape=3c03cd1f vocab=38bb7e54
-/
theorem p4Z_z_not_mem_trace {a b V : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V) :
    let S := p4ZSocles (a := a) (b := b) ha V
    let hzS : (Normal.zGenerator : Normal a b 0) ∈ standardFinset S :=
      (mem_standardFinset_iff_standardSet S _).2 (p4Z_isLiveTie ha hb hV).2.2.1
    X (k := k) S Normal.zGenerator hzS ∉ TraceSubmodule k S := by
  dsimp only
  let S := p4ZSocles (a := a) (b := b) ha V
  let C : Normal a b 0 := ⟨0, b, 0, a_pos_of_neZero⟩
  let P : Normal a b 0 := ⟨0, b - 1, V, a_pos_of_neZero⟩
  let Z : Normal a b 0 := ⟨0, 0, V + 1, a_pos_of_neZero⟩
  have hC : C ∈ S := by simp [S, C, p4ZSocles]
  have hP : P ∈ S := by simp [S, P, p4ZSocles]
  have hZ : Z ∈ S := by simp [S, Z, p4ZSocles]
  have hcard3 : S.card = 3 := p4Z_card_eq_three ha hb hV
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hanti : IsRootAntichain S := p4Z_isRootAntichain ha hb hV
  have hlive : IsLiveTie S := p4Z_isLiveTie ha hb hV
  have hyS : (Normal.yGenerator : Normal a b 0) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.2.1
  have hzS : (Normal.zGenerator : Normal a b 0) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.2.2.1
  let m : Normal a b 0 := ⟨0, b - 1, 0, a_pos_of_neZero⟩
  let q : Normal a b 0 := ⟨0, 0, V, a_pos_of_neZero⟩
  let w : Normal a b 0 := ⟨0, b - 1, 1, a_pos_of_neZero⟩
  let yz : Normal a b 0 := ⟨0, 1, 1, a_pos_of_neZero⟩
  let zz : Normal a b 0 := ⟨0, 0, 2, a_pos_of_neZero⟩
  have hmS : m ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet, mem_standardSet_p4Z_iff ha hb hV]
    simp [m, p4ZStandardNat]
  have hqS : q ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet, mem_standardSet_p4Z_iff ha hb hV]
    simp [q, p4ZStandardNat]
  have hwS : w ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet, mem_standardSet_p4Z_iff ha hb hV]
    simp [w, p4ZStandardNat]
    omega
  have hyzS : yz ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet, mem_standardSet_p4Z_iff ha hb hV]
    simp [yz, p4ZStandardNat]
    omega
  have hzzS : zz ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet, mem_standardSet_p4Z_iff ha hb hV]
    simp [zz, p4ZStandardNat]
    omega
  intro htrace
  obtain ⟨F, s, hs, hcoeff⟩ :=
    exists_root_image_with_variable_coeff_of_mem_trace (k := k) S hS
      (by omega) hanti (by exact ⟨ha, Or.inr ⟨hb, rfl⟩⟩) .z hzS htrace
  have hs' : s = C ∨ s = P ∨ s = Z := by
    simpa [S, C, P, Z, p4ZSocles] using hs
  rcases hs' with rfl | rfl | rfl
  · have hnot : ¬(Normal.zGenerator : Normal a b 0) ∣ C := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.zGenerator, C]
    have hzero : X (k := k) S Normal.zGenerator hzS •
        U (k := k) S (rootIndex S C hC) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S C hC
        (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)).2 hnot
    exact hcoeff (coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S) ⟨zz, hzzS⟩
      (rootIndex S C hC) hzero
      (by apply Normal.ext <;> simp [zz, Normal.zGenerator]))
  · have htransfer := coeff_transfer_of_common_quotient (k := k) S F
      (⟨m, hmS⟩ : MonomialIndex S)
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)
      (⟨q, hqS⟩ : MonomialIndex S)
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)
      (⟨m, hmS⟩ : MonomialIndex S) (⟨w, hwS⟩ : MonomialIndex S)
      (rootIndex S P hP) (rootIndex S Z hZ)
      (by apply Normal.ext <;> simp [m, q, P, rootIndex] <;> omega)
      (by apply Normal.ext <;> simp [q, Z, Normal.zGenerator, rootIndex] <;> omega)
      (by apply Normal.ext <;> simp [m, w, Normal.zGenerator])
      (by apply Normal.ext <;> simp [m, w, Normal.zGenerator])
    have hnot : ¬(Normal.yGenerator : Normal a b 0) ∣ Z := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.yGenerator, Z]
    have hzero : X (k := k) S Normal.yGenerator hyS •
        U (k := k) S (rootIndex S Z hZ) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S Z hZ
        (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)).2 hnot
    have hvanish := coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)
      (⟨m, hmS⟩ : MonomialIndex S) (rootIndex S C hC)
      (rootIndex S Z hZ) hzero
      (by apply Normal.ext <;>
        simp [m, C, Normal.yGenerator, rootIndex] <;> omega)
    exact hcoeff (htransfer.trans hvanish)
  · have hnot : ¬(Normal.yGenerator : Normal a b 0) ∣ Z := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.yGenerator, Z]
    have hzero : X (k := k) S Normal.yGenerator hyS •
        U (k := k) S (rootIndex S Z hZ) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S Z hZ
        (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)).2 hnot
    exact hcoeff (coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.yGenerator, hyS⟩ : MonomialIndex S)
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S) ⟨yz, hyzS⟩
      (rootIndex S Z hZ) hzero
      (by apply Normal.ext <;> simp [yz, Normal.yGenerator, Normal.zGenerator]))

/--
@isnad1 id=not.4h4v.s6.66de37f40700 from=translated src=- shape=62ccc462 vocab=5fd1c0af
-/
theorem p4Z_not_variablesInTrace {a b V : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V)
    (hlive : IsLiveTie (p4ZSocles (a := a) (b := b) ha V)) :
    ¬VariablesInTrace k (p4ZSocles (a := a) (b := b) ha V) hlive := by
  intro htrace
  exact p4Z_z_not_mem_trace (k := k) ha hb hV htrace.2.2

/-! ## P5Z -/

/--
@isnad1 id=eq.3h3v.s6.f567b929dc88 from=translated src=- shape=ee7544ed vocab=f8528f85
-/
theorem p5Z_card_eq_three {a b v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
    (p5ZSocles (a := a) (b := b) ha v).card = 3 := by
  have ha10 : a - 1 ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hv0 : v ≠ 0 := by omega
  simp [p5ZSocles, Normal.ext_iff, ha10, hb0, hv0]

/--
@isnad1 id=isrootan.3h3v.s5.add246f6f861 from=translated src=- shape=bbb4277c vocab=bc2d352e
-/
theorem p5Z_isRootAntichain {a b v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
    IsRootAntichain (p5ZSocles (a := a) (b := b) ha v) := by
  simp only [IsRootAntichain]
  intro p hp q hq hpq
  simp only [p5ZSocles, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  all_goals
    simp_all [Normal.exact_divides_iff, Normal.DividesCriterion, Normal.ext_iff]
  all_goals omega

/--
@isnad1 id=isliveti.3h3v.s5.353642b81751 from=translated src=- shape=bbb4277c vocab=25933d7d
-/
theorem p5Z_isLiveTie {a b v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
    IsLiveTie (p5ZSocles (a := a) (b := b) ha v) := by
  simp [IsLiveTie, standardSet, p5ZSocles, liveTiePoint,
    Normal.exact_divides_iff, Normal.DividesCriterion,
    Normal.xGenerator, show a ≠ 1 by omega,
    Normal.yGenerator, Normal.zGenerator]
  omega

/--
@isnad1 id=other.3h4v.s9.21a64b03c0b3 from=translated src=- shape=3c03cd1f vocab=19697e34
-/
theorem p5Z_z_not_mem_trace {a b v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
    let S := p5ZSocles (a := a) (b := b) ha v
    let hzS : (Normal.zGenerator : Normal a b 0) ∈ standardFinset S :=
      (mem_standardFinset_iff_standardSet S _).2 (p5Z_isLiveTie ha hb hv).2.2.1
    X (k := k) S Normal.zGenerator hzS ∉ TraceSubmodule k S := by
  dsimp only
  let S := p5ZSocles (a := a) (b := b) ha v
  let R : Normal a b 0 := ⟨a - 1, 0, v, by omega⟩
  let C : Normal a b 0 := ⟨0, b, 0, a_pos_of_neZero⟩
  let Z : Normal a b 0 := ⟨0, 0, v + 1, a_pos_of_neZero⟩
  have hR : R ∈ S := by simp [S, R, p5ZSocles]
  have hC : C ∈ S := by simp [S, C, p5ZSocles]
  have hZ : Z ∈ S := by simp [S, Z, p5ZSocles]
  have hcard3 : S.card = 3 := p5Z_card_eq_three ha hb hv
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hanti : IsRootAntichain S := p5Z_isRootAntichain ha hb hv
  have hlive : IsLiveTie S := p5Z_isLiveTie ha hb hv
  have hxS : (Normal.xGenerator : Normal a b 0) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.1
  have hzS : (Normal.zGenerator : Normal a b 0) ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 hlive.2.2.1
  let m : Normal a b 0 := ⟨a - 1, 0, 0, by omega⟩
  let q : Normal a b 0 := ⟨0, 0, v, a_pos_of_neZero⟩
  let w : Normal a b 0 := ⟨a - 1, 0, 1, by omega⟩
  let xz : Normal a b 0 := ⟨1, 0, 1, by omega⟩
  let zz : Normal a b 0 := ⟨0, 0, 2, a_pos_of_neZero⟩
  have hmS : m ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet, mem_standardSet_p5Z_iff ha hb hv]
    simp [m, p5ZStandardNat]
  have hqS : q ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet, mem_standardSet_p5Z_iff ha hb hv]
    simp [q, p5ZStandardNat]
  have hwS : w ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet, mem_standardSet_p5Z_iff ha hb hv]
    simp [w, p5ZStandardNat]
    omega
  have hxzS : xz ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet, mem_standardSet_p5Z_iff ha hb hv]
    simp [xz, p5ZStandardNat]
    omega
  have hzzS : zz ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet, mem_standardSet_p5Z_iff ha hb hv]
    simp [zz, p5ZStandardNat]
    omega
  intro htrace
  obtain ⟨F, s, hs, hcoeff⟩ :=
    exists_root_image_with_variable_coeff_of_mem_trace (k := k) S hS
      (by omega) hanti (by exact ⟨ha, Or.inr ⟨hb, rfl⟩⟩) .z hzS htrace
  have hs' : s = R ∨ s = C ∨ s = Z := by
    simpa [S, R, C, Z, p5ZSocles] using hs
  rcases hs' with rfl | rfl | rfl
  · have htransfer := coeff_transfer_of_common_quotient (k := k) S F
      (⟨m, hmS⟩ : MonomialIndex S)
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)
      (⟨q, hqS⟩ : MonomialIndex S)
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)
      (⟨m, hmS⟩ : MonomialIndex S) (⟨w, hwS⟩ : MonomialIndex S)
      (rootIndex S R hR) (rootIndex S Z hZ)
      (by apply Normal.ext <;>
        simp [m, q, R, rootIndex, Nat.mod_eq_of_lt (show a - 1 < a by omega),
          Nat.div_eq_of_lt (show a - 1 < a by omega)] <;> omega)
      (by apply Normal.ext <;> simp [q, Z, Normal.zGenerator, rootIndex] <;> omega)
      (by apply Normal.ext <;> simp [m, w, Normal.zGenerator] <;> omega)
      (by apply Normal.ext <;> simp [m, w, Normal.zGenerator] <;> omega)
    have hnot : ¬(Normal.xGenerator : Normal a b 0) ∣ Z := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.xGenerator, show a ≠ 1 by omega, Z]
      omega
    have hzero : X (k := k) S Normal.xGenerator hxS •
        U (k := k) S (rootIndex S Z hZ) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S Z hZ
        (⟨Normal.xGenerator, hxS⟩ : MonomialIndex S)).2 hnot
    have hwrap : (Normal.xGenerator : Normal a b 0) * m = C := by
      rw [mul_comm]
      simpa [m, C, Normal.wrappedXPredecessor] using
        (Normal.wrappedXPredecessor_mul C (by rfl)
          (by simp [C]) (by simp [C]))
    have hvanish := coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.xGenerator, hxS⟩ : MonomialIndex S)
      (⟨m, hmS⟩ : MonomialIndex S) (rootIndex S C hC)
      (rootIndex S Z hZ) hzero
      (by simpa [rootIndex] using hwrap)
    exact hcoeff (htransfer.trans hvanish)
  · have hnot : ¬(Normal.zGenerator : Normal a b 0) ∣ C := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.zGenerator, C]
    have hzero : X (k := k) S Normal.zGenerator hzS •
        U (k := k) S (rootIndex S C hC) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S C hC
        (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)).2 hnot
    exact hcoeff (coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S)
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S) ⟨zz, hzzS⟩
      (rootIndex S C hC) hzero
      (by apply Normal.ext <;> simp [zz, Normal.zGenerator]))
  · have hnot : ¬(Normal.xGenerator : Normal a b 0) ∣ Z := by
      simp [Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.xGenerator, show a ≠ 1 by omega, Z]
      omega
    have hzero : X (k := k) S Normal.xGenerator hxS •
        U (k := k) S (rootIndex S Z hZ) = 0 :=
      (X_smul_rootDual_eq_zero_iff (k := k) S Z hZ
        (⟨Normal.xGenerator, hxS⟩ : MonomialIndex S)).2 hnot
    exact hcoeff (coeff_eq_zero_of_annihilator (k := k) S F
      (⟨Normal.xGenerator, hxS⟩ : MonomialIndex S)
      (⟨Normal.zGenerator, hzS⟩ : MonomialIndex S) ⟨xz, hxzS⟩
      (rootIndex S Z hZ) hzero
      (by apply Normal.ext <;>
        simp [xz, Normal.xGenerator, show a ≠ 1 by omega, Normal.zGenerator,
          Nat.mod_eq_of_lt (show 1 < a by omega),
          Nat.div_eq_of_lt (show 1 < a by omega)]))

/--
@isnad1 id=not.4h4v.s6.4a243e87a073 from=translated src=- shape=62ccc462 vocab=9d4963aa
-/
theorem p5Z_not_variablesInTrace {a b v : ℕ} [NeZero a]
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v)
    (hlive : IsLiveTie (p5ZSocles (a := a) (b := b) ha v)) :
    ¬VariablesInTrace k (p5ZSocles (a := a) (b := b) ha v) hlive := by
  intro htrace
  exact p5Z_z_not_mem_trace (k := k) ha hb hv htrace.2.2

/-- Run-10 exact-family obstruction bundle.  This deliberately contains no
classification or arbitrary-dominant reduction.-/
structure CanonicalTraceObstructions : Prop where
  mixedYZ : ∀ {a u v : ℕ} [NeZero a] (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v),
    let hr : 0 < a - 1 := by omega
    let S := mixedSoclesYZ (a := a) (b := 1) (c := 1) 0 u v hr
    let hyS : (Normal.yGenerator : Normal a 1 1) ∈ standardFinset S :=
      (mem_standardFinset_iff_standardSet S _).2 (mixedYZ_isLiveTie ha hu hv).2.1
    X (k := k) S Normal.yGenerator hyS ∉ TraceSubmodule k S
  mixedYQ : ∀ {a b r u v : ℕ} [NeZero a] (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hu : b ≤ u) (hv : 1 ≤ v) (hr : r < a - 1),
    let S := mixedSoclesYQ (a := a) (b := b) (c := 1) r u v hr
    let hyS : (Normal.yGenerator : Normal a b 1) ∈ standardFinset S :=
      (mem_standardFinset_iff_standardSet S _).2 (mixedYQ_isLiveTie ha hb hu hv hr).2.1
    X (k := k) S Normal.yGenerator hyS ∉ TraceSubmodule k S
  mixedZP : ∀ {a c r u v : ℕ} [NeZero a] (ha : 2 ≤ a) (hc : 1 ≤ c)
    (hu : 1 ≤ u) (hv : c ≤ v) (hr : r < a - 1),
    let S := mixedSoclesZP (a := a) (b := 1) (c := c) r u v hr
    let hzS : (Normal.zGenerator : Normal a 1 c) ∈ standardFinset S :=
      (mem_standardFinset_iff_standardSet S _).2 (mixedZP_isLiveTie ha hc hu hv hr).2.2.1
    X (k := k) S Normal.zGenerator hzS ∉ TraceSubmodule k S
  mixedPQ : ∀ {a b c u v : ℕ} [NeZero a] (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hu : b ≤ u) (hv : c ≤ v) (huv : 1 < u ∨ 1 < v),
    let hr : a - 2 < a - 1 := by omega
    let S := mixedSoclesPQ (a := a) (b := b) (c := c) (a - 2) u v hr
    let hlive := mixedPQ_isLiveTie ha hb hc hu hv
    ¬ VariablesInTrace k S hlive
  pureP4Z : ∀ {a b V : ℕ} [NeZero a] (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V),
    let S := p4ZSocles (a := a) (b := b) ha V
    let hzS : (Normal.zGenerator : Normal a b 0) ∈ standardFinset S :=
      (mem_standardFinset_iff_standardSet S _).2 (p4Z_isLiveTie ha hb hV).2.2.1
    X (k := k) S Normal.zGenerator hzS ∉ TraceSubmodule k S
  pureP5Z : ∀ {a b v : ℕ} [NeZero a] (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v),
    let S := p5ZSocles (a := a) (b := b) ha v
    let hzS : (Normal.zGenerator : Normal a b 0) ∈ standardFinset S :=
      (mem_standardFinset_iff_standardSet S _).2 (p5Z_isLiveTie ha hb hv).2.2.1
    X (k := k) S Normal.zGenerator hzS ∉ TraceSubmodule k S

/--
@isnad1 id=canonica.0h1v.s3.812da333cb6b from=translated src=- shape=c6850a32 vocab=8f592d9c
-/
theorem canonicalTraceObstructions : CanonicalTraceObstructions (k := k) where
  mixedYZ := mixedYZ_y_not_mem_trace
  mixedYQ := mixedYQ_y_not_mem_trace
  mixedZP := mixedZP_z_not_mem_trace
  mixedPQ := by
    intro a b c u v _ ha hb hc hu hv huv
    dsimp only
    exact mixedPQ_not_variablesInTrace (k := k) ha hb hc hu hv huv
      (mixedPQ_isLiveTie ha hb hc hu hv)
  pureP4Z := p4Z_z_not_mem_trace
  pureP5Z := p5Z_z_not_mem_trace

end

end P23.Artin
