import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_BruhatTitsTree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two

set_option autoImplicit false

open scoped MatrixGroups Matrix
open CerednikDrinfeld.BruhatTits LT.LatticeTree

noncomputable section

namespace R1BTTree

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
variable {ϖ : R}

/--
@isnad1 id=ne.1h3v.s7.6188f1b49888 from=translated src=- shape=9029a494 vocab=0bd2dba4
-/
theorem alg_ne_zero {x : R} (hx : x ≠ 0) : algebraMap R K x ≠ 0 :=
  fun h => hx (IsFractionRing.injective R K (by rw [h, map_zero]))

/--
@isnad1 id=iff.0h5v.s10.80ad812744d2 from=translated src=- shape=f417b285 vocab=5fbb6723
-/
theorem sc_le_iff (c : Kˣ) (L L' : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL c) L ≤ L' ↔ ∀ w ∈ L, (c : K) • w ∈ L' := by
  constructor
  · intro h w hw
    exact h (mem_latticeMap_scalarGL.mpr ⟨w, hw, rfl⟩)
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
    exact h w hw

/--
@isnad1 id=mem.1h5v.s9.857a74e63c8d from=translated src=- shape=e5f7fae5 vocab=865e955a
-/
theorem algebraMap_smul_mem (L : Submodule R (Fin 2 → K)) (r : R) {w : Fin 2 → K} (hw : w ∈ L) :
    algebraMap R K r • w ∈ L := by
  rw [algebraMap_smul]
  exact L.smul_mem r hw

/--
@isnad1 id=eq.1h5v.s8.05ff1ce0bbc9 from=translated src=- shape=5805db54 vocab=6d2df339
-/
theorem sc_unit_eq (u : Rˣ) (c : Kˣ) (hc : (c : K) = algebraMap R K u)
    (L : Submodule R (Fin 2 → K)) : latticeMap (scalarGL c) L = L := by
  apply le_antisymm
  · rw [sc_le_iff]
    intro w hw
    rw [hc]
    exact algebraMap_smul_mem L _ hw
  · intro w hw
    refine mem_latticeMap_scalarGL.mpr ⟨((c⁻¹ : Kˣ) : K) • w, ?_, by rw [smul_smul, Units.mul_inv, one_smul]⟩
    have : ((c⁻¹ : Kˣ) : K) = algebraMap R K ↑u⁻¹ := by
      rw [map_units_inv, ← hc, Units.val_inv_eq_inv_val]
    rw [this]
    exact algebraMap_smul_mem L _ hw

def piU (hϖ : Irreducible ϖ) : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero

/--
@isnad1 id=eq.1h3v.s7.e9abcb032123 from=translated src=- shape=a571b5a0 vocab=3919560d
-/
theorem piU_coe (hϖ : Irreducible ϖ) : ((piU (K := K) hϖ : Kˣ) : K) = algebraMap R K ϖ := rfl

/--
@isnad1 id=eq.1h4v.s7.ca28cb638c89 from=translated src=- shape=1e90e2cc vocab=65b283a4
-/
theorem piU_pow_coe (hϖ : Irreducible ϖ) (n : ℕ) :
    ((piU (K := K) hϖ ^ n : Kˣ) : K) = algebraMap R K (ϖ ^ n) := by
  rw [Units.val_pow_eq_pow_val, piU_coe, map_pow]

/--
@isnad1 id=mem.2h6v.s9.85d395af61bb from=translated src=- shape=e9cae625 vocab=1b387dde
-/
theorem pow_smul_mem (hϖ : Irreducible ϖ) (L : Submodule R (Fin 2 → K)) (n : ℕ) {w : Fin 2 → K}
    (hw : w ∈ L) : ((piU (K := K) hϖ ^ n : Kˣ) : K) • w ∈ L := by
  rw [piU_pow_coe]
  exact algebraMap_smul_mem L _ hw

/--
@isnad1 id=le.1h5v.s9.055c24b4bd8c from=translated src=- shape=e42a2855 vocab=8f60502f
-/
theorem sc_pow_le (hϖ : Irreducible ϖ) (L : Submodule R (Fin 2 → K)) (n : ℕ) :
    latticeMap (scalarGL (piU (K := K) hϖ ^ n)) L ≤ L :=
  (sc_le_iff _ _ _).2 fun w hw => pow_smul_mem hϖ L n hw

/--
@isnad1 id=le.1h4v.s8.2f12b93e3a1f from=translated src=- shape=6d6d0637 vocab=95468cd9
-/
theorem sc_one_le (hϖ : Irreducible ϖ) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (piU (K := K) hϖ)) L ≤ L :=
  (sc_le_iff _ _ _).2 fun w hw => by
    rw [piU_coe]
    exact algebraMap_smul_mem L ϖ hw

/--
@isnad1 id=eq.0h5v.s8.39741536fb91 from=translated src=- shape=82e1370c vocab=7639034f
-/
theorem sc_sc (c d : Kˣ) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL c) (latticeMap (scalarGL d) L) = latticeMap (scalarGL (c * d)) L := by
  rw [scalarGL_mul, latticeMap_mul]

/--
@isnad1 id=eq.1h5v.s8.3d1a0c776d7b from=translated src=- shape=37ef0b8b vocab=18717acc
-/
theorem sc_one_sc_pow (hϖ : Irreducible ϖ) (L : Submodule R (Fin 2 → K)) (n : ℕ) :
    latticeMap (scalarGL (piU (K := K) hϖ)) (latticeMap (scalarGL (piU (K := K) hϖ ^ n)) L) =
      latticeMap (scalarGL (piU (K := K) hϖ ^ (n + 1))) L := by
  rw [sc_sc, ← pow_succ']

/--
@isnad1 id=eq.1h5v.s8.d5fb04879862 from=translated src=- shape=23eb1e97 vocab=18717acc
-/
theorem sc_pow_sc_one (hϖ : Irreducible ϖ) (L : Submodule R (Fin 2 → K)) (n : ℕ) :
    latticeMap (scalarGL (piU (K := K) hϖ ^ n)) (latticeMap (scalarGL (piU (K := K) hϖ)) L) =
      latticeMap (scalarGL (piU (K := K) hϖ ^ (n + 1))) L := by
  rw [sc_sc, ← pow_succ]

/--
@isnad1 id=eq.0h5v.s9.32f8fc0566b4 from=translated src=- shape=a428ebbe vocab=35f0e0c2
-/
theorem latticeMap_sup (g : GL (Fin 2) K) (L L' : Submodule R (Fin 2 → K)) :
    latticeMap g (L ⊔ L') = latticeMap g L ⊔ latticeMap g L' :=
  Submodule.map_sup _ _ _

/--
@isnad1 id=eq.2h5v.s8.63167c1d4c1f from=translated src=- shape=7c01a7ac vocab=f07a964a
-/
theorem sc_irreducible_eq (hϖ : Irreducible ϖ) {ϖ' : R} (hϖ' : Irreducible ϖ')
    (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ'.ne_zero)) L =
      latticeMap (scalarGL (piU (K := K) hϖ)) L := by
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible R hϖ hϖ'
  have hunit : (Units.mk0 (algebraMap R K u) (alg_ne_zero u.ne_zero) : K) = algebraMap R K u := rfl
  have hfac : (unitOfNeZero (K := K) hϖ'.ne_zero : Kˣ) =
      piU (K := K) hϖ * Units.mk0 (algebraMap R K u) (alg_ne_zero u.ne_zero) := by
    ext
    rw [Units.val_mul, unitOfNeZero_coe, piU_coe, ← hu, map_mul]
    rfl
  rw [hfac, ← sc_sc, sc_unit_eq u _ hunit]

/--
@isnad1 id=ex.2h5v.s9.f255959288fe from=translated src=- shape=16dab3df vocab=7bbfac3e
-/
theorem exists_pow_smul_mem (hϖ : Irreducible ϖ) {L : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) (v : Fin 2 → K) :
    ∃ n : ℕ, ((piU (K := K) hϖ ^ n : Kˣ) : K) • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set (Fin 2 → K)) := by
    rw [hL.2]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rwa [pow_zero, Units.val_one, one_smul]⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
      obtain ⟨m, hm⟩ := hx
      obtain ⟨n, hn⟩ := hy
      refine ⟨m + n, ?_⟩
      rw [smul_add]
      refine L.add_mem ?_ ?_
      · rw [add_comm, pow_add, Units.val_mul, mul_smul]
        exact pow_smul_mem hϖ L n hm
      · rw [pow_add, Units.val_mul, mul_smul]
        exact pow_smul_mem hϖ L m hn
  | smul c x _ hx =>
      obtain ⟨n, hn⟩ := hx
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) c
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      obtain ⟨e, u, hbu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
      refine ⟨e + n, ?_⟩
      have hπ : algebraMap R K ϖ ≠ 0 := alg_ne_zero hϖ.ne_zero
      have hu : algebraMap R K u ≠ 0 := alg_ne_zero u.ne_zero
      have key : ((piU (K := K) hϖ ^ (e + n) : Kˣ) : K) * (algebraMap R K a / algebraMap R K b) =
          algebraMap R K (a * ↑u⁻¹) * ((piU (K := K) hϖ ^ n : Kˣ) : K) := by
        rw [hbu, piU_pow_coe, piU_pow_coe, map_mul, map_mul, map_pow, map_pow, map_pow,
          map_units_inv, pow_add]
        field_simp
      rw [smul_smul, key, mul_smul, algebraMap_smul]
      exact L.smul_mem _ hn

/--
@isnad1 id=ex.3h5v.s9.db9db45e8b13 from=translated src=- shape=729e6e22 vocab=929b7c04
-/
theorem exists_sc_pow_le (hϖ : Irreducible ϖ) {L M : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) (hM : IsFullLattice M) :
    ∃ n : ℕ, latticeMap (scalarGL (piU (K := K) hϖ ^ n)) M ≤ L := by
  obtain ⟨s, hs⟩ := hM.1
  choose f hf using fun v : Fin 2 → K => exists_pow_smul_mem hϖ hL v
  refine ⟨s.sup f, (sc_le_iff _ _ _).2 ?_⟩
  rw [← hs]
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
      have hle : f x ≤ s.sup f := Finset.le_sup (Finset.mem_coe.mp hx)
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [hk, add_comm, pow_add, Units.val_mul, mul_smul]
      exact pow_smul_mem hϖ L k (hf x)
  | zero =>
      rw [smul_zero]
      exact L.zero_mem
  | add x y _ _ hx hy =>
      rw [smul_add]
      exact L.add_mem hx hy
  | smul r x _ hx =>
      rw [smul_comm]
      exact L.smul_mem r hx

/--
@isnad1 id=isfullla.3h5v.s9.a0bba98f9706 from=translated src=- shape=2803b4a0 vocab=494252c2
-/
theorem isFullLattice_of_le_of_le {L L' : Submodule R (Fin 2 → K)} (hL : IsFullLattice L)
    (hL'fg : L'.FG) {c : Kˣ} (hle : latticeMap (scalarGL c) L ≤ L') : IsFullLattice L' := by
  refine ⟨hL'fg, ?_⟩
  rw [eq_top_iff, ← (hL.map (scalarGL c)).2]
  exact Submodule.span_mono hle

/--
@isnad1 id=reachabl.3h4v.s8.de66a859f68d from=translated src=- shape=cecc170d vocab=0bd1e832
-/
theorem reachable_of_adjacentLattice {L L' : Submodule R (Fin 2 → K)} (hL : IsFullLattice L)
    (hL' : IsFullLattice L') (h : AdjacentLattice L L') :
    (tree R K).Reachable (Vertex.mk R K L hL) (Vertex.mk R K L' hL') := by
  by_cases heq : Vertex.mk R K L hL = Vertex.mk R K L' hL'
  · rw [heq]
  · exact SimpleGraph.Adj.reachable
      ((tree_adj_iff _ _).2 ⟨heq, Or.inl ⟨L, L', hL, hL', rfl, rfl, h⟩⟩)

/--
@isnad1 id=eq.2h6v.s10.c95a733c61ab from=translated src=- shape=96f22387 vocab=596283aa
-/
theorem sup_sc_pow_eq_of_sup_sc_eq (hϖ : Irreducible ϖ) {L N : Submodule R (Fin 2 → K)}
    (h : N ⊔ latticeMap (scalarGL (piU (K := K) hϖ)) L = L) :
    ∀ k : ℕ, N ⊔ latticeMap (scalarGL (piU (K := K) hϖ ^ (k + 1))) L = L
  | 0 => by rwa [zero_add, pow_one]
  | (k + 1) => by
      have ih := sup_sc_pow_eq_of_sup_sc_eq hϖ h k
      have hN : latticeMap (scalarGL (piU (K := K) hϖ)) N ≤ N := sc_one_le hϖ N
      calc N ⊔ latticeMap (scalarGL (piU (K := K) hϖ ^ (k + 1 + 1))) L
          = N ⊔ (latticeMap (scalarGL (piU (K := K) hϖ)) N ⊔
              latticeMap (scalarGL (piU (K := K) hϖ ^ (k + 1 + 1))) L) := by
            rw [← sup_assoc, sup_eq_left.2 hN]
        _ = N ⊔ latticeMap (scalarGL (piU (K := K) hϖ))
              (N ⊔ latticeMap (scalarGL (piU (K := K) hϖ ^ (k + 1))) L) := by
            rw [latticeMap_sup, sc_one_sc_pow]
        _ = L := by rw [ih, h]

/--
@isnad1 id=reachabl.5h6v.s10.a45228e52b1d from=translated src=- shape=898067c5 vocab=47f5dbb4
-/
theorem reachable_of_sc_pow_le (hϖ : Irreducible ϖ) :
    ∀ (n : ℕ) (L N : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) (hN : IsFullLattice N),
      latticeMap (scalarGL (piU (K := K) hϖ ^ n)) L ≤ N → N ≤ L →
      (tree R K).Reachable (Vertex.mk R K L hL) (Vertex.mk R K N hN)
  | 0, L, N, hL, hN, h1, h2 => by
      have h1' : L ≤ N := by rwa [pow_zero, scalarGL_one, latticeMap_one] at h1
      obtain rfl : L = N := le_antisymm h1' h2
      rfl
  | (n + 1), L, N, hL, hN, h1, h2 => by
      by_cases hc : N ≤ latticeMap (scalarGL (piU (K := K) hϖ)) L
      ·
        have hN' : IsFullLattice (latticeMap (scalarGL (piU (K := K) hϖ)⁻¹) N) := hN.map _
        have e : Vertex.mk R K N hN = Vertex.mk R K _ hN' :=
          Vertex.mk_eq_mk_iff.2 ⟨(piU (K := K) hϖ)⁻¹, rfl⟩
        rw [e]
        apply reachable_of_sc_pow_le hϖ n L _ hL hN'
        · have := latticeMap_mono (scalarGL (piU (K := K) hϖ)⁻¹) h1
          rwa [sc_sc, pow_succ', inv_mul_cancel_left] at this
        · have := latticeMap_mono (scalarGL (piU (K := K) hϖ)⁻¹) hc
          rwa [sc_sc, inv_mul_cancel, scalarGL_one, latticeMap_one] at this
      ·
        by_cases htop : N ⊔ latticeMap (scalarGL (piU (K := K) hϖ)) L = L
        · have hall := sup_sc_pow_eq_of_sup_sc_eq hϖ htop n
          have hNL : L ≤ N := by
            calc L = N ⊔ latticeMap (scalarGL (piU (K := K) hϖ ^ (n + 1))) L := hall.symm
              _ ≤ N := sup_le le_rfl h1
          obtain rfl : L = N := le_antisymm hNL h2
          rfl
        · have hL'fg : (N ⊔ latticeMap (scalarGL (piU (K := K) hϖ)) L).FG :=
            hN.1.sup (hL.map _).1
          have hL'full : IsFullLattice (N ⊔ latticeMap (scalarGL (piU (K := K) hϖ)) L) :=
            isFullLattice_of_le_of_le hL hL'fg le_sup_right
          have hlt1 : latticeMap (scalarGL (piU (K := K) hϖ)) L <
              N ⊔ latticeMap (scalarGL (piU (K := K) hϖ)) L :=
            lt_of_le_of_ne le_sup_right fun h => hc (h ▸ le_sup_left)
          have hlt2 : N ⊔ latticeMap (scalarGL (piU (K := K) hϖ)) L < L :=
            lt_of_le_of_ne (sup_le h2 (sc_one_le hϖ L)) htop
          have hadj : AdjacentLattice L (N ⊔ latticeMap (scalarGL (piU (K := K) hϖ)) L) :=
            ⟨ϖ, hϖ, hlt1, hlt2⟩
          refine (reachable_of_adjacentLattice hL hL'full hadj).trans ?_
          apply reachable_of_sc_pow_le hϖ n _ N hL'full hN
          · rw [latticeMap_sup, sc_pow_sc_one]
            exact sup_le (sc_pow_le hϖ N n) h1
          · exact le_sup_left

/--
@isnad1 id=connecte.0h2v.s6.df18195ab0b0 from=translated src=- shape=c1290c98 vocab=3a4b5a0c
-/
theorem tree_connected : (tree R K).Connected := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨stdVertex R K, fun y => ?_⟩
  induction y using Quotient.inductionOn with
  | h M =>
    obtain ⟨M, hM⟩ := M
    change (tree R K).Reachable (Vertex.mk R K (stdLattice R K) isFullLattice_stdLattice)
      (Vertex.mk R K M hM)
    obtain ⟨n, hn⟩ := exists_sc_pow_le hϖ (isFullLattice_stdLattice (R := R) (K := K)) hM
    have hN : IsFullLattice (latticeMap (scalarGL (piU (K := K) hϖ ^ n)) M) := hM.map _
    have e : Vertex.mk R K M hM = Vertex.mk R K _ hN :=
      Vertex.mk_eq_mk_iff.2 ⟨piU (K := K) hϖ ^ n, rfl⟩
    rw [e]
    obtain ⟨m, hm⟩ := exists_sc_pow_le hϖ hN (isFullLattice_stdLattice (R := R) (K := K))
    exact reachable_of_sc_pow_le hϖ m _ _ isFullLattice_stdLattice hN hm hn

/--
@isnad1 id=ex.1h3v.s8.722777346b64 from=translated src=- shape=9df1f8b0 vocab=17cf5f84
-/
theorem exists_gl_latticeMap_stdLattice_eq {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    ∃ g : GL (Fin 2) K, latticeMap g (stdLattice R K) = L := by
  haveI : Submodule.IsLattice K L := ⟨hL.1, hL.2⟩
  have hrank : Module.finrank R L = 2 := by
    rw [Submodule.IsLattice.finrank_of_pi K L, Fintype.card_fin]
  let b : Module.Basis (Fin 2) R L := Module.finBasisOfFinrankEq R L hrank
  let bK : Module.Basis (Fin 2) K (Fin 2 → K) := b.extendOfIsLattice K
  let e : Module.Basis (Fin 2) K (Fin 2 → K) := Pi.basisFun K (Fin 2)
  let g : GL (Fin 2) K :=
    ⟨e.toMatrix bK, bK.toMatrix e, e.toMatrix_mul_toMatrix_flip bK, bK.toMatrix_mul_toMatrix_flip e⟩
  refine ⟨g, ?_⟩
  have hcol : ∀ j, mulVecLinR (R := R) g (Pi.single j 1) = ((b j : L) : Fin 2 → K) := by
    intro j
    rw [mulVecLinR_apply, mulVec_single_one]
    funext i
    change e.toMatrix bK i j = _
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr, Module.Basis.extendOfIsLattice_apply]
  rw [latticeMap, stdLattice_eq_span, Submodule.map_span, ← Set.range_comp]
  have hfun : (mulVecLinR (R := R) g) ∘ (fun j => (Pi.single j 1 : Fin 2 → K)) =
      fun j => ((b j : L) : Fin 2 → K) := funext hcol
  rw [hfun]
  have h2 := congrArg (Submodule.map L.subtype) b.span_eq
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h2
  exact h2

/--
@isnad1 id=ex.0h3v.s8.3231a7fdb985 from=translated src=- shape=e23089c6 vocab=07a5227c
-/
theorem exists_gl_smul_stdVertex_eq (x : Vertex R K) : ∃ g : GL (Fin 2) K, g • stdVertex R K = x := by
  induction x using Quotient.inductionOn with
  | h L =>
    obtain ⟨L, hL⟩ := L
    obtain ⟨g, hg⟩ := exists_gl_latticeMap_stdLattice_eq hL
    refine ⟨g, ?_⟩
    change Vertex.mk R K (latticeMap g (stdLattice R K)) _ = Vertex.mk R K L hL
    exact Vertex.mk_eq_mk_iff.2 (hg ▸ Homothetic.refl _)

/--
@isnad1 id=ex.1h4v.s8.7668d32c0039 from=translated src=- shape=744c245c vocab=b1a6df66
-/
theorem exists_unit_mul_zpow (hϖ : Irreducible ϖ) (c : Kˣ) :
    ∃ (m : ℤ) (u : Rˣ), (c : K) = algebraMap R K u * algebraMap R K ϖ ^ m := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) (c : K)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact c.ne_zero hab.symm
  obtain ⟨i, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨j, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨(i : ℤ) - j, u * w⁻¹, ?_⟩
  have hπ : algebraMap R K ϖ ≠ 0 := alg_ne_zero hϖ.ne_zero
  have hwK : algebraMap R K w ≠ 0 := alg_ne_zero w.ne_zero
  rw [← hab, hu, hw, Units.val_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_units_inv,
    zpow_sub₀ hπ, zpow_natCast, zpow_natCast]
  field_simp

/--
@isnad1 id=eq.3h7v.s8.7df419578c8e from=translated src=- shape=0b124573 vocab=91bb177a
-/
theorem zpow_exp_unique_aux (hϖ : Irreducible ϖ) {m m' : ℤ} {u u' : Rˣ} (hle : m ≤ m')
    (h : algebraMap R K u * algebraMap R K ϖ ^ m = algebraMap R K u' * algebraMap R K ϖ ^ m') :
    m = m' := by
  obtain ⟨k, rfl⟩ := Int.le.dest hle
  have hπ : algebraMap R K ϖ ≠ 0 := alg_ne_zero hϖ.ne_zero
  rw [zpow_add₀ hπ, zpow_natCast, mul_comm (algebraMap R K ϖ ^ m), ← mul_assoc] at h
  have h' : (u : R) * ϖ ^ 0 = u' * ϖ ^ k := by
    apply IsFractionRing.injective R K
    rw [pow_zero, mul_one, map_mul, map_pow]
    exact mul_right_cancel₀ (zpow_ne_zero m hπ) h
  have hk : 0 = k := IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ u u' 0 k h'
  subst hk
  simp

/--
@isnad1 id=eq.2h7v.s8.e868c170d204 from=translated src=- shape=20e82777 vocab=b1a6df66
-/
theorem zpow_exp_unique (hϖ : Irreducible ϖ) {m m' : ℤ} {u u' : Rˣ}
    (h : algebraMap R K u * algebraMap R K ϖ ^ m = algebraMap R K u' * algebraMap R K ϖ ^ m') :
    m = m' := by
  rcases le_total m m' with hle | hle
  · exact zpow_exp_unique_aux hϖ hle h
  · exact (zpow_exp_unique_aux hϖ hle h.symm).symm

def zv (hϖ : Irreducible ϖ) (c : Kˣ) : ℤ := (exists_unit_mul_zpow (K := K) hϖ c).choose

/--
@isnad1 id=ex.1h4v.s8.c203e547c060 from=translated src=- shape=5aa76e8d vocab=c60673e7
-/
theorem zv_spec (hϖ : Irreducible ϖ) (c : Kˣ) :
    ∃ u : Rˣ, (c : K) = algebraMap R K u * algebraMap R K ϖ ^ zv hϖ c :=
  (exists_unit_mul_zpow (K := K) hϖ c).choose_spec

/--
@isnad1 id=eq.2h6v.s8.285caa395da4 from=translated src=- shape=85941930 vocab=c60673e7
-/
theorem zv_eq (hϖ : Irreducible ϖ) {c : Kˣ} {m : ℤ} (u : Rˣ)
    (h : (c : K) = algebraMap R K u * algebraMap R K ϖ ^ m) : zv hϖ c = m := by
  obtain ⟨u', hu'⟩ := zv_spec hϖ c
  exact zpow_exp_unique hϖ (hu'.symm.trans h)

/--
@isnad1 id=eq.1h5v.s7.cb79cbe255e6 from=translated src=- shape=6aa1fa2a vocab=43890b3c
-/
theorem zv_mul (hϖ : Irreducible ϖ) (c d : Kˣ) : zv hϖ (c * d) = zv hϖ c + zv hϖ d := by
  obtain ⟨u, hu⟩ := zv_spec hϖ c
  obtain ⟨w, hw⟩ := zv_spec hϖ d
  apply zv_eq hϖ (u * w)
  rw [Units.val_mul, hu, hw, Units.val_mul, map_mul, zpow_add₀ (alg_ne_zero hϖ.ne_zero)]
  ring

/--
@isnad1 id=eq.2h5v.s7.b0b3fa6aab56 from=translated src=- shape=2e222d8e vocab=5586163a
-/
theorem zv_of_eq_unit (hϖ : Irreducible ϖ) {c : Kˣ} (u : Rˣ) (h : (c : K) = algebraMap R K u) :
    zv hϖ c = 0 :=
  zv_eq hϖ u (by rw [h, zpow_zero, mul_one])

/--
@isnad1 id=eq.2h6v.s7.593862a2ce23 from=translated src=- shape=2f4d85ec vocab=a6949f36
-/
theorem zv_of_eq_unit_mul_pow (hϖ : Irreducible ϖ) {c : Kˣ} (u : Rˣ) (k : ℕ)
    (h : (c : K) = algebraMap R K (u * ϖ ^ k)) : zv hϖ c = k :=
  zv_eq hϖ u (by rw [h, map_mul, map_pow, zpow_natCast])

/--
@isnad1 id=eq.1h4v.s6.e67b4781802e from=translated src=- shape=4daedc80 vocab=fd04b5b3
-/
theorem zv_inv (hϖ : Irreducible ϖ) (c : Kˣ) : zv hϖ c⁻¹ = -zv hϖ c := by
  have h1 : zv hϖ (c⁻¹ * c) = 0 := by
    rw [inv_mul_cancel]
    exact zv_of_eq_unit hϖ 1 (by rw [Units.val_one, Units.val_one, map_one])
  rw [zv_mul] at h1
  omega

/--
@isnad1 id=ex.1h3v.s9.95fba0fe383f from=translated src=- shape=63b16219 vocab=02e94958
-/
theorem exists_matrix_of_latticeMap_le {h : GL (Fin 2) K}
    (hle : latticeMap h (stdLattice R K) ≤ stdLattice R K) :
    ∃ M : Matrix (Fin 2) (Fin 2) R, M.map (algebraMap R K) = (h : Matrix (Fin 2) (Fin 2) K) := by
  have hcol : ∀ i j, IsLocalization.IsInteger R ((h : Matrix (Fin 2) (Fin 2) K) i j) := by
    intro i j
    have hj : (h : Matrix (Fin 2) (Fin 2) K) *ᵥ (Pi.single j 1) ∈ stdLattice R K :=
      hle (mulVec_mem_latticeMap (single_one_mem_stdLattice R K j))
    have := hj i
    rwa [mulVec_single_one] at this
  choose a ha using hcol
  exact ⟨Matrix.of fun i j => a i j, by ext i j; exact ha i j⟩

/--
@isnad1 id=eq.1h4v.s8.8b75625bb2ad from=translated src=- shape=28be3bd3 vocab=77d3dc85
-/
theorem det_coe_eq {h : GL (Fin 2) K} {M : Matrix (Fin 2) (Fin 2) R}
    (hM : M.map (algebraMap R K) = (h : Matrix (Fin 2) (Fin 2) K)) :
    (h : Matrix (Fin 2) (Fin 2) K).det = algebraMap R K M.det := by
  rw [← hM, RingHom.map_det, RingHom.mapMatrix_apply]

/--
@isnad1 id=eq.2h4v.s8.636cadae5c97 from=translated src=- shape=6fa6f660 vocab=07d8f455
-/
theorem latticeMap_eq_of_isUnit_det {h : GL (Fin 2) K} {M : Matrix (Fin 2) (Fin 2) R}
    (hM : M.map (algebraMap R K) = (h : Matrix (Fin 2) (Fin 2) K)) (hdet : IsUnit M.det) :
    latticeMap h (stdLattice R K) = stdLattice R K := by
  obtain ⟨Mu, hMu⟩ := (Matrix.isUnit_iff_isUnit_det M).mpr hdet
  refine (latticeMap_stdLattice_eq_iff_mem_range h).mpr ⟨Mu, ?_⟩
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, ← hM, hMu, Matrix.map_apply]

/--
@isnad1 id=eq.3h4v.s10.97ef1551b264 from=translated src=- shape=1bc7a085 vocab=05fa454d
-/
theorem zv_det_eq_one (hϖ : Irreducible ϖ) (h : GL (Fin 2) K)
    (h1 : latticeMap (scalarGL (piU (K := K) hϖ)) (stdLattice R K) < latticeMap h (stdLattice R K))
    (h2 : latticeMap h (stdLattice R K) < stdLattice R K) :
    zv hϖ (Matrix.GeneralLinearGroup.det h) = 1 := by
  set h' : GL (Fin 2) K := h⁻¹ * scalarGL (piU (K := K) hϖ) with hh'
  have hhh' : h * h' = scalarGL (piU (K := K) hϖ) := by rw [hh', mul_inv_cancel_left]
  have h1' : latticeMap h' (stdLattice R K) ≤ stdLattice R K := by
    have := latticeMap_mono h⁻¹ h1.le
    rwa [latticeMap_inv_latticeMap, ← latticeMap_mul] at this
  obtain ⟨M, hM⟩ := exists_matrix_of_latticeMap_le h2.le
  obtain ⟨M', hM'⟩ := exists_matrix_of_latticeMap_le h1'
  have hdet : M.det * M'.det = ϖ ^ 2 := by
    apply IsFractionRing.injective R K
    rw [map_mul, ← det_coe_eq hM, ← det_coe_eq hM', ← Matrix.det_mul,
      ← Matrix.GeneralLinearGroup.coe_mul, hhh', scalarGL_coe, Matrix.det_smul, Matrix.det_one,
      mul_one, Fintype.card_fin, map_pow, piU_coe]
  have hM0 : M.det ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hdet
    exact pow_ne_zero 2 hϖ.ne_zero hdet.symm
  have hM'0 : M'.det ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hdet
    exact pow_ne_zero 2 hϖ.ne_zero hdet.symm
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hM0 hϖ
  obtain ⟨b, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hM'0 hϖ
  have hab : a + b = 2 := by
    apply IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (u * u') 1 (a + b) 2
    rw [Units.val_one, one_mul, ← hdet, hu, hu', Units.val_mul]
    ring
  have ha : a ≠ 0 := by
    rintro rfl
    apply h2.ne
    apply latticeMap_eq_of_isUnit_det hM
    rw [hu, pow_zero, mul_one]
    exact u.isUnit
  have hb : b ≠ 0 := by
    rintro rfl
    apply h1.ne
    have e : latticeMap h' (stdLattice R K) = stdLattice R K :=
      latticeMap_eq_of_isUnit_det hM' (by rw [hu', pow_zero, mul_one]; exact u'.isUnit)
    calc latticeMap (scalarGL (piU (K := K) hϖ)) (stdLattice R K)
        = latticeMap h (latticeMap h' (stdLattice R K)) := by rw [← latticeMap_mul, hhh']
      _ = latticeMap h (stdLattice R K) := by rw [e]
  have ha1 : a = 1 := by omega
  apply zv_of_eq_unit_mul_pow hϖ u 1
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_coe_eq hM, hu, ha1]

def rep (x : Vertex R K) : GL (Fin 2) K := (exists_gl_smul_stdVertex_eq x).choose

/--
@isnad1 id=eq.0h3v.s8.0bab9735365d from=translated src=- shape=8f18e1e1 vocab=a9d04a09
-/
theorem rep_spec (x : Vertex R K) : rep x • stdVertex R K = x :=
  (exists_gl_smul_stdVertex_eq x).choose_spec

def color (hϖ : Irreducible ϖ) (x : Vertex R K) : ZMod 2 :=
  (zv (K := K) hϖ (Matrix.GeneralLinearGroup.det (rep x)) : ZMod 2)

/--
@isnad1 id=eq.0h1v.s6.37df61cac041 from=translated src=- shape=2500d187 vocab=0685f5bc
-/
theorem two_mul_cast_zmod_two (k : ℤ) : ((2 * k : ℤ) : ZMod 2) = 0 := by
  rw [Int.cast_mul]
  have : ((2 : ℤ) : ZMod 2) = 0 := by decide
  rw [this, zero_mul]

/--
@isnad1 id=eq.2h5v.s9.07d32e2a4246 from=translated src=- shape=3cc162c9 vocab=3c9dbc7f
-/
theorem color_eq (hϖ : Irreducible ϖ) {x : Vertex R K} {g : GL (Fin 2) K}
    (hg : g • stdVertex R K = x) :
    color hϖ x = (zv (K := K) hϖ (Matrix.GeneralLinearGroup.det g) : ZMod 2) := by
  have hfix : Vertex.act (g⁻¹ * rep x) (stdVertex R K) = stdVertex R K := by
    rw [← gl_smul_def, mul_smul, rep_spec, ← hg, inv_smul_smul]
  obtain ⟨c, M, hM⟩ := (Vertex.act_stdVertex_eq_iff _).mp hfix

  have hdetM : zv (K := K) hϖ (Matrix.GeneralLinearGroup.det (scalarGL c * (g⁻¹ * rep x))) = 0 := by
    rw [← hM, Matrix.GeneralLinearGroup.map_det]
    exact zv_of_eq_unit hϖ (Matrix.GeneralLinearGroup.det M) rfl
  have hsc : Matrix.GeneralLinearGroup.det (scalarGL c : GL (Fin 2) K) = c * c := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_smul, Matrix.det_one,
      mul_one, Fintype.card_fin, Units.val_mul, pow_two]
  rw [map_mul, map_mul, map_inv, hsc, zv_mul, zv_mul, zv_mul, zv_inv] at hdetM
  have hz : zv (K := K) hϖ (Matrix.GeneralLinearGroup.det (rep x)) =
      zv (K := K) hϖ (Matrix.GeneralLinearGroup.det g) + 2 * (-zv hϖ c) := by omega
  unfold color
  rw [hz, Int.cast_add, two_mul_cast_zmod_two, add_zero]

/--
@isnad1 id=ne.2h5v.s6.d2b56c4e69ba from=translated src=- shape=6cb2fd36 vocab=658809a9
-/
theorem color_ne_of_vertRel (hϖ : Irreducible ϖ) {x y : Vertex R K} (h : VertRel R K x y) :
    color hϖ x ≠ color hϖ y := by
  obtain ⟨L, L', hL, hL', rfl, rfl, ϖ', hϖ', h1, h2⟩ := h
  rw [sc_irreducible_eq hϖ hϖ'] at h1
  obtain ⟨g, rfl⟩ := exists_gl_latticeMap_stdLattice_eq hL
  obtain ⟨g', rfl⟩ := exists_gl_latticeMap_stdLattice_eq hL'
  have hx : g • stdVertex R K = Vertex.mk R K (latticeMap g (stdLattice R K)) hL := rfl
  have hy : g' • stdVertex R K = Vertex.mk R K (latticeMap g' (stdLattice R K)) hL' := rfl
  rw [color_eq hϖ hx, color_eq hϖ hy]
  have k1 : latticeMap (scalarGL (piU (K := K) hϖ)) (stdLattice R K) <
      latticeMap (g⁻¹ * g') (stdLattice R K) := by
    have := (latticeMap_lt_latticeMap_iff g⁻¹).2 h1
    rwa [← latticeMap_mul, ← latticeMap_mul, ← latticeMap_mul, ← scalarGL_mul_comm,
      inv_mul_cancel_right] at this
  have k2 : latticeMap (g⁻¹ * g') (stdLattice R K) < stdLattice R K := by
    have := (latticeMap_lt_latticeMap_iff g⁻¹).2 h2
    rwa [← latticeMap_mul, latticeMap_inv_latticeMap] at this
  have hone := zv_det_eq_one hϖ (g⁻¹ * g') k1 k2
  rw [map_mul, map_inv, zv_mul, zv_inv] at hone
  have hz : zv (K := K) hϖ (Matrix.GeneralLinearGroup.det g') =
      zv (K := K) hϖ (Matrix.GeneralLinearGroup.det g) + 1 := by omega
  rw [hz, Int.cast_add, Int.cast_one]
  have key : ∀ t : ZMod 2, t ≠ t + 1 := by decide
  exact key _

/--
@isnad1 id=ne.2h5v.s6.85d5c138fccf from=translated src=- shape=ec79d715 vocab=38c32f80
-/
theorem color_ne_of_adj (hϖ : Irreducible ϖ) {x y : Vertex R K} (h : (tree R K).Adj x y) :
    color hϖ x ≠ color hϖ y := by
  rw [tree_adj_iff] at h
  obtain ⟨-, h | h⟩ := h
  · exact color_ne_of_vertRel hϖ h
  · exact (color_ne_of_vertRel hϖ h).symm

/--
@isnad1 id=colorabl.0h2v.s6.4bf2043d74e6 from=translated src=- shape=2802decd vocab=e0baba3d
-/
theorem tree_colorable_two : (tree R K).Colorable 2 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have C : (tree R K).Coloring (ZMod 2) :=
    SimpleGraph.Coloring.mk (color hϖ) fun hadj => color_ne_of_adj hϖ hadj
  have := C.colorable
  rwa [ZMod.card] at this

end R1BTTree

end

open R1BTTree in
/--
@isnad1 id=and.0h2v.s6.ded60d552629 from=translated src=- shape=be1858a4 vocab=fb075cab
-/
theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] :
    (tree R K).Connected ∧ (tree R K).Colorable 2 :=
  ⟨tree_connected, tree_colorable_two⟩
