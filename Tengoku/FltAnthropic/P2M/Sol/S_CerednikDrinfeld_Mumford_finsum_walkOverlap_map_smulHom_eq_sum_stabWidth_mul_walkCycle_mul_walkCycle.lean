import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_WalkOverlap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_Mumford_finsum_walkOverlap_map_smulHom_eq_sum_stabWidth_mul_walkCycle_mul_walkCycle.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 3 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_Mumford_finsum_walkOverlap_map_smulHom_eq_sum_stabWidth_mul_walkCycle_mul_walkCycle.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_Mumford_finsum_walkOverlap_map_smulHom_eq_sum_stabWidth_mul_walkCycle_mul_walkCycle

set_option autoImplicit false

open _root_.MulAction open _root_.CerednikDrinfeld open _root_.CerednikDrinfeld.Mumford

namespace CerednikDrinfeld
namespace Mumford
export _root_.CerednikDrinfeld.Mumford (stabilizer_dart_le smulHom dartIndex walkCycle GraphAction smul_dart_symm QuotEdge card_stabilizer_smul stabWidth stabWidth_mk walkOverlap walkOverlap_eq_sum)
namespace TreeSumW
open _root_.CerednikDrinfeld.Mumford open _root_.CerednikDrinfeld

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
  (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w)

def orbitColour : QuotEdge G 𝒯 → ZMod 2 :=
  Quotient.lift (fun d : 𝒯.Dart => τ d.fst) (by rintro _ d ⟨g, rfl⟩; exact hτ g d.fst)

/--
@isnad1 id=eq.1h5v.s7.13cd35e1fd15 from=translated src=- shape=2ff1d12b vocab=9424c8ec
-/
theorem orbitColour_eq_out (o : QuotEdge G 𝒯) : orbitColour 𝒯 τ hτ o = τ o.out.fst := by
  conv_lhs => rw [← Quotient.out_eq o]
  rfl

omit [GraphAction G 𝒯] in
/--
@isnad1 id=eq.1h4v.s7.25b929296451 from=translated src=- shape=beb4bc8b vocab=6d64020f
-/
theorem colour_symm_fst (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v) (d : 𝒯.Dart) : τ d.symm.fst = τ d.fst + 1 := by
  have key : ∀ x y : ZMod 2, x ≠ y → y = x + 1 := by decide
  exact key _ _ (hadj _ _ d.adj)

omit [GraphAction G 𝒯] in
/--
@isnad1 id=iff.0h5v.s7.fa697725c626 from=translated src=- shape=7cd2530f vocab=c3ea4f43
-/
theorem mk_symm_eq_mk_symm_iff [GraphAction G 𝒯] (x y : 𝒯.Dart) :
    Quotient.mk (orbitRel G 𝒯.Dart) x.symm = Quotient.mk (orbitRel G 𝒯.Dart) y.symm ↔
      Quotient.mk (orbitRel G 𝒯.Dart) x = Quotient.mk (orbitRel G 𝒯.Dart) y := by
  simp only [Quotient.eq, orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    have := congrArg SimpleGraph.Dart.symm hg
    rwa [← smul_dart_symm, SimpleGraph.Dart.symm_symm, SimpleGraph.Dart.symm_symm] at this
  · rintro ⟨g, hg⟩
    exact ⟨g, by rw [← smul_dart_symm, hg]⟩

/--
@isnad1 id=iff.0h5v.s7.9be24100d458 from=translated src=- shape=50abb4ca vocab=c3ea4f43
-/
theorem mk_symm_eq_mk_iff (x y : 𝒯.Dart) :
    Quotient.mk (orbitRel G 𝒯.Dart) x.symm = Quotient.mk (orbitRel G 𝒯.Dart) y ↔
      Quotient.mk (orbitRel G 𝒯.Dart) x = Quotient.mk (orbitRel G 𝒯.Dart) y.symm := by
  conv_lhs => rw [← SimpleGraph.Dart.symm_symm y]
  exact mk_symm_eq_mk_symm_iff 𝒯 x y.symm

variable [DecidableEq (QuotEdge G 𝒯)] {E : Type} [Fintype E] (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})

/--
@isnad1 id=eq.1h8v.s10.486f5e3af023 from=translated src=- shape=528ec5ed vocab=b34768e3
-/
theorem sum_ite_eq_orbit (o : QuotEdge G 𝒯) (f : ℤ) :
    (∑ e : E, if o = (eE e).1 then f else 0) = if orbitColour 𝒯 τ hτ o = 0 then f else 0 := by
  classical
  by_cases h : orbitColour 𝒯 τ hτ o = 0
  · rw [ite_eq_left h]
    have ho : τ o.out.fst = 0 := by rwa [orbitColour_eq_out] at h
    rw [Finset.sum_eq_single (eE.symm ⟨o, ho⟩)]
    · simp
    · intro e _ hne
      rw [ite_eq_right]
      intro heq
      apply hne
      apply eE.injective
      rw [Equiv.apply_symm_apply]
      exact Subtype.ext heq.symm
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun e _ => ite_eq_right fun heq => h ?_
    rw [heq, orbitColour_eq_out]; exact (eE e).2

include hτ in
/--
@isnad1 id=eq.2h8v.s10.30d14434556d from=translated src=- shape=d1b618d2 vocab=e047158f
-/
theorem sum_dartIndex_mul_dartIndex (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v) (d d' : 𝒯.Dart) :
    (∑ e : E, dartIndex 𝒯 (eE e).1 d * dartIndex 𝒯 (eE e).1 d') =
      (if Quotient.mk (orbitRel G 𝒯.Dart) d = Quotient.mk (orbitRel G 𝒯.Dart) d' then 1 else 0) -
        (if Quotient.mk (orbitRel G 𝒯.Dart) d.symm = Quotient.mk (orbitRel G 𝒯.Dart) d' then 1 else 0) := by
  classical
  set a := Quotient.mk (orbitRel G 𝒯.Dart) d with ha
  set a' := Quotient.mk (orbitRel G 𝒯.Dart) d.symm with ha'
  set b := Quotient.mk (orbitRel G 𝒯.Dart) d' with hb
  set b' := Quotient.mk (orbitRel G 𝒯.Dart) d'.symm with hb'
  have ca' : orbitColour 𝒯 τ hτ a' = orbitColour 𝒯 τ hτ a + 1 := colour_symm_fst 𝒯 τ hadj d
  have cb' : orbitColour 𝒯 τ hτ b' = orbitColour 𝒯 τ hτ b + 1 := colour_symm_fst 𝒯 τ hadj d'
  have expand : ∀ e : E, dartIndex 𝒯 (eE e).1 d * dartIndex 𝒯 (eE e).1 d' =
      (if a = (eE e).1 then (if b = (eE e).1 then 1 else 0) - (if b' = (eE e).1 then 1 else 0) else 0) -
      (if a' = (eE e).1 then (if b = (eE e).1 then 1 else 0) - (if b' = (eE e).1 then 1 else 0) else 0) := by
    intro e
    simp only [dartIndex, ← ha, ← ha', ← hb, ← hb']
    split_ifs <;> simp
  simp_rw [expand]
  rw [Finset.sum_sub_distrib]
  have loc : ∀ (o : QuotEdge G 𝒯),
      (∑ e : E, if o = (eE e).1 then ((if b = (eE e).1 then 1 else 0) - (if b' = (eE e).1 then 1 else 0) : ℤ) else 0) =
        if orbitColour 𝒯 τ hτ o = 0 then ((if b = o then 1 else 0) - (if b' = o then 1 else 0)) else 0 := by
    intro o
    have : ∀ e : E, (if o = (eE e).1 then ((if b = (eE e).1 then 1 else 0) - (if b' = (eE e).1 then 1 else 0) : ℤ) else 0)
        = if o = (eE e).1 then ((if b = o then 1 else 0) - (if b' = o then 1 else 0)) else 0 := by
      intro e
      by_cases h : o = (eE e).1
      · rw [ite_eq_left h, ite_eq_left h, h]
      · rw [ite_eq_right h, ite_eq_right h]
    simp_rw [this]
    exact sum_ite_eq_orbit 𝒯 τ hτ eE o _
  rw [loc a, loc a']
  have r1 : (b' = a) ↔ (a' = b) := by
    rw [hb', ha, ha', hb, mk_symm_eq_mk_iff, eq_comm]
  have r2 : (b' = a') ↔ (a = b) := by
    rw [hb', ha', mk_symm_eq_mk_symm_iff, eq_comm]
  have r3 : (b = a) ↔ (a = b) := eq_comm
  have r4 : (b = a') ↔ (a' = b) := eq_comm
  have hcol : ∀ x : ZMod 2, (x + 1 = 0 ↔ ¬ x = 0) := by decide
  have hne1 : ∀ x : ZMod 2, x ≠ x + 1 := by decide
  have not_both : ¬ (a = b ∧ a' = b) := by
    rintro ⟨h1, h2⟩
    have := congrArg (orbitColour 𝒯 τ hτ) (h1.trans h2.symm)
    rw [ca'] at this
    exact hne1 _ this
  simp only [r1, r2, r3, r4, ca', hcol]
  by_cases h1 : a = b
  · have h2 : ¬ a' = b := fun h2 => not_both ⟨h1, h2⟩
    by_cases hc : orbitColour 𝒯 τ hτ a = 0
    · rw [h1] at hc; simp [h1, h2, hc]
    · rw [h1] at hc; simp [h1, h2, hc]
  · by_cases h2 : a' = b <;> by_cases hc : orbitColour 𝒯 τ hτ a = 0 <;> simp [h1, h2, hc]

section Weights

variable (G)

noncomputable def wt (d : 𝒯.Dart) : ℤ := (Nat.card (stabilizer G d) : ℤ)

/--
@isnad1 id=eq.0h4v.s6.47fa23bc0613 from=translated src=- shape=21f9a82c vocab=02e6b876
-/
theorem stabilizer_symm (d : 𝒯.Dart) : stabilizer G d.symm = stabilizer G d := by
  ext γ
  simp only [mem_stabilizer_iff]
  constructor
  · intro h
    have := congrArg SimpleGraph.Dart.symm h
    rwa [smul_dart_symm, SimpleGraph.Dart.symm_symm] at this
  · intro h
    rw [← smul_dart_symm, h]

/--
@isnad1 id=eq.0h4v.s5.faf327141fbc from=translated src=- shape=38d1aace vocab=d8a1c03f
-/
theorem wt_symm (d : 𝒯.Dart) : wt G 𝒯 d.symm = wt G 𝒯 d := by
  rw [wt, wt, stabilizer_symm G 𝒯]

/--
@isnad1 id=eq.0h5v.s6.bcc778e67ca8 from=translated src=- shape=1ecdcf4c vocab=89591de8
-/
theorem wt_smul (g : G) (d : 𝒯.Dart) : wt G 𝒯 (g • d) = wt G 𝒯 d := by
  rw [wt, wt, card_stabilizer_smul]

/--
@isnad1 id=eq.1h5v.s6.7a025d1e034e from=translated src=- shape=41c441c5 vocab=25cac2cb
-/
theorem wt_eq_of_mk_eq {d d' : 𝒯.Dart}
    (h : Quotient.mk (orbitRel G 𝒯.Dart) d = Quotient.mk (orbitRel G 𝒯.Dart) d') : wt G 𝒯 d = wt G 𝒯 d' := by
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact h))
  exact wt_smul G 𝒯 g d'

/--
@isnad1 id=eq.1h4v.s6.bc0e8c2cd681 from=translated src=- shape=0364f654 vocab=bd986d77
-/
theorem stabWidth_mk_eq_wt (hfin : ∀ d : 𝒯.Dart, Finite (stabilizer G d)) (d : 𝒯.Dart) :
    ((stabWidth G 𝒯 (Quotient.mk (orbitRel G 𝒯.Dart) d) : ℕ) : ℤ) = wt G 𝒯 d := by
  have h := stabWidth_mk 𝒯 (G := G) d
  have hpos : 0 < Nat.card (stabilizer G d) := by
    haveI := hfin d
    exact Nat.card_pos
  rw [show (Quotient.mk'' d : QuotEdge G 𝒯) = Quotient.mk (orbitRel G 𝒯.Dart) d from rfl] at h
  rw [h, Nat.toPNat'_coe, ite_eq_left hpos, wt]

/--
@isnad1 id=eq.1h8v.s11.ece9a34a4cc5 from=translated src=- shape=1576e121 vocab=239255ed
-/
theorem stabWidth_mul_dartIndex (hfin : ∀ d : 𝒯.Dart, Finite (stabilizer G d)) (e : E) (d : 𝒯.Dart) :
    ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * dartIndex 𝒯 (eE e).1 d = wt G 𝒯 d * dartIndex 𝒯 (eE e).1 d := by
  by_cases h1 : Quotient.mk (orbitRel G 𝒯.Dart) d = (eE e).1
  · rw [← h1, stabWidth_mk_eq_wt G 𝒯 hfin]
  · by_cases h2 : Quotient.mk (orbitRel G 𝒯.Dart) d.symm = (eE e).1
    · rw [← h2, stabWidth_mk_eq_wt G 𝒯 hfin, wt_symm]
    · have : dartIndex 𝒯 (eE e).1 d = 0 := by
        rw [dartIndex, ite_eq_right h1, ite_eq_right h2, sub_zero]
      rw [this, mul_zero, mul_zero]

end Weights

section FiniteStab

variable [DecidableEq W] (hfin : ∀ d : 𝒯.Dart, Finite (stabilizer G d))

include hfin in
/--
@isnad1 id=finite.1h5v.s7.cf1325d5bc8c from=translated src=- shape=647f952f vocab=5eac1f20
-/
theorem finite_setOf_smul_eq (d d' : 𝒯.Dart) : ({γ : G | γ • d' = d} : Set G).Finite := by
  by_cases h : ∃ γ₀ : G, γ₀ • d' = d
  · obtain ⟨γ₀, hγ₀⟩ := h
    haveI := hfin d'
    have hsub : {γ : G | γ • d' = d} ⊆ (fun s : stabilizer G d' => γ₀ * (s : G)) '' Set.univ := by
      intro γ hγ
      simp only [Set.mem_ofPred_eq] at hγ
      refine ⟨⟨γ₀⁻¹ * γ, ?_⟩, Set.mem_univ _, ?_⟩
      · rw [mem_stabilizer_iff, mul_smul, hγ, ← hγ₀, inv_smul_smul]
      · simp
    exact (Set.finite_univ.image _).subset hsub
  · have : ({γ : G | γ • d' = d} : Set G) = ∅ := by
      ext γ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hγ => h ⟨γ, hγ⟩
    rw [this]; exact Set.finite_empty

include hfin in
/--
@isnad1 id=finite.1h5v.s7.897a4ab70a67 from=translated src=- shape=b4f0f142 vocab=bbf31a0b
-/
theorem finite_support_indicator (d d' : 𝒯.Dart) :
    (Function.support fun γ : G => (if γ • d' = d then (1 : ℤ) else 0)).Finite := by
  apply (finite_setOf_smul_eq 𝒯 hfin d d').subset
  intro γ hγ
  rw [Function.mem_support] at hγ
  by_contra h
  exact hγ (ite_eq_right h)

include hfin in

/--
@isnad1 id=eq.1h5v.s8.4a7b891fd396 from=translated src=- shape=060da147 vocab=f807320c
-/
theorem finsum_indicator_smul_eq (d d' : 𝒯.Dart) :
    ∑ᶠ γ : G, (if γ • d' = d then (1 : ℤ) else 0) =
      if Quotient.mk (orbitRel G 𝒯.Dart) d = Quotient.mk (orbitRel G 𝒯.Dart) d' then wt G 𝒯 d else 0 := by
  classical
  by_cases h : Quotient.mk (orbitRel G 𝒯.Dart) d = Quotient.mk (orbitRel G 𝒯.Dart) d'
  · rw [ite_eq_left h]
    obtain ⟨γ₀, hγ₀⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact h))

    haveI := hfin d'
    have hS := finite_setOf_smul_eq 𝒯 hfin d d'
    rw [finsum_eq_sum_of_support_subset _ (s := hS.toFinset) (by
      intro γ hγ
      rw [Function.mem_support] at hγ
      rw [Set.Finite.coe_toFinset]
      by_contra hn
      exact hγ (ite_eq_right hn))]
    rw [Finset.sum_congr rfl (fun γ hγ => ite_eq_left (show γ • d' = d from (Set.Finite.mem_toFinset hS).mp hγ)),
      Finset.sum_const, nsmul_eq_mul, mul_one]

    rw [wt_eq_of_mk_eq G 𝒯 h, wt]
    congr 1
    rw [← Nat.card_eq_card_finite_toFinset hS]
    refine Nat.card_congr ?_
    refine
      { toFun := fun γ => ⟨γ₀⁻¹ * (γ : G), ?_⟩
        invFun := fun s => ⟨γ₀ * (s : G), ?_⟩
        left_inv := fun γ => Subtype.ext (by simp)
        right_inv := fun s => Subtype.ext (by simp) }
    · have hγ : (γ : G) • d' = d := γ.2
      rw [mem_stabilizer_iff, mul_smul, hγ, ← hγ₀, inv_smul_smul]
    · show (γ₀ * (s : G)) • d' = d
      rw [mul_smul, (mem_stabilizer_iff).mp s.2, hγ₀]
  · rw [ite_eq_right h]
    have : (fun γ : G => (if γ • d' = d then (1 : ℤ) else 0)) = fun _ => 0 := by
      funext γ
      rw [ite_eq_right]
      intro hγd
      exact h (Quotient.sound (orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨γ, hγd⟩)))
    rw [this, finsum_zero]

end FiniteStab

section Lists

variable [DecidableEq W]
variable (hfin : ∀ d : 𝒯.Dart, Finite (stabilizer G d))

def atom (d : 𝒯.Dart) (L : List 𝒯.Dart) (γ : G) : ℤ :=
  ((L.map fun x => γ • x).count d : ℤ) - ((L.map fun x => γ • x).count d.symm : ℤ)

/--
@isnad1 id=eq.0h5v.s6.60417c7445c4 from=translated src=- shape=ca685c3f vocab=b8c1edcf
-/
theorem atom_nil (d : 𝒯.Dart) (γ : G) : atom 𝒯 d [] γ = 0 := by simp [atom]

/--
@isnad1 id=eq.0h7v.s8.e17f14a5aa16 from=translated src=- shape=f22b0118 vocab=38e881c5
-/
theorem atom_cons (d d' : 𝒯.Dart) (L : List 𝒯.Dart) (γ : G) :
    atom 𝒯 d (d' :: L) γ =
      ((if γ • d' = d then (1 : ℤ) else 0) - (if γ • d' = d.symm then (1 : ℤ) else 0)) + atom 𝒯 d L γ := by
  simp only [atom, List.map_cons, List.count_cons, beq_iff_eq, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  ring

include hfin in
/--
@isnad1 id=finite.1h5v.s8.1a92e7642793 from=translated src=- shape=4f9805af vocab=aa9d9929
-/
theorem finite_support_pair (d d' : 𝒯.Dart) :
    (Function.support fun γ : G => (if γ • d' = d then (1 : ℤ) else 0) - (if γ • d' = d.symm then (1 : ℤ) else 0)).Finite := by
  refine ((finite_support_indicator 𝒯 hfin d d').union (finite_support_indicator 𝒯 hfin d.symm d')).subset ?_
  intro γ hγ
  rw [Function.mem_support] at hγ
  by_contra hnot
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hnot
  exact hγ (by rw [hnot.1, hnot.2, sub_zero])

include hfin in
/--
@isnad1 id=finite.1h5v.s6.3fd903d9c9e4 from=translated src=- shape=69fe98b1 vocab=39817aef
-/
theorem finite_support_atom (d : 𝒯.Dart) (L : List 𝒯.Dart) : (Function.support (atom 𝒯 d L : G → ℤ)).Finite := by
  induction L with
  | nil =>
    have : (atom 𝒯 d [] : G → ℤ) = fun _ => 0 := funext fun γ => atom_nil 𝒯 d γ
    rw [this]
    exact Set.finite_empty.subset fun γ hγ => (hγ rfl).elim
  | cons d' L ih =>
    refine ((finite_support_pair 𝒯 hfin d d').union ih).subset ?_
    intro γ hγ
    rw [Function.mem_support, atom_cons] at hγ
    by_contra hnot
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hnot
    exact hγ (by rw [hnot.1, hnot.2, add_zero])

include hfin hτ in

/--
@isnad1 id=eq.3h8v.s11.3f545ee5e287 from=translated src=- shape=0e70e321 vocab=d460ae84
-/
theorem finsum_atom (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v) (d : 𝒯.Dart) (L : List 𝒯.Dart) :
    ∑ᶠ γ : G, atom 𝒯 d L γ =
      ∑ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * (dartIndex 𝒯 (eE e).1 d * (L.map (dartIndex 𝒯 (eE e).1)).sum) := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil, mul_zero, Finset.sum_const_zero]
    rw [show (fun γ : G => atom 𝒯 d [] γ) = fun _ => 0 from funext fun γ => atom_nil 𝒯 d γ, finsum_zero]
  | cons d' L ih =>
    rw [show (fun γ : G => atom 𝒯 d (d' :: L) γ) =
        fun γ => ((if γ • d' = d then (1 : ℤ) else 0) - (if γ • d' = d.symm then (1 : ℤ) else 0)) + atom 𝒯 d L γ from
      funext fun γ => atom_cons 𝒯 d d' L γ]
    rw [finsum_add_distrib (finite_support_pair 𝒯 hfin d d') (finite_support_atom 𝒯 hfin d L),
      finsum_sub_distrib (finite_support_indicator 𝒯 hfin d d') (finite_support_indicator 𝒯 hfin d.symm d'),
      finsum_indicator_smul_eq 𝒯 hfin, finsum_indicator_smul_eq 𝒯 hfin, wt_symm G 𝒯, ih]

    have head : ((if Quotient.mk (orbitRel G 𝒯.Dart) d = Quotient.mk (orbitRel G 𝒯.Dart) d' then wt G 𝒯 d else 0) -
        (if Quotient.mk (orbitRel G 𝒯.Dart) d.symm = Quotient.mk (orbitRel G 𝒯.Dart) d' then wt G 𝒯 d else 0)) =
        ∑ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * (dartIndex 𝒯 (eE e).1 d * dartIndex 𝒯 (eE e).1 d') := by
      have : ∀ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * (dartIndex 𝒯 (eE e).1 d * dartIndex 𝒯 (eE e).1 d') =
          wt G 𝒯 d * (dartIndex 𝒯 (eE e).1 d * dartIndex 𝒯 (eE e).1 d') := fun e => by
        rw [← mul_assoc, stabWidth_mul_dartIndex G 𝒯 τ eE hfin e d, mul_assoc]
      rw [Finset.sum_congr rfl (fun e _ => this e), ← Finset.mul_sum,
        sum_dartIndex_mul_dartIndex 𝒯 τ hτ eE hadj d d', mul_sub]
      split_ifs <;> simp
    rw [head, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [List.map_cons, List.sum_cons]
    ring

include hfin in
/--
@isnad1 id=finite.1h5v.s6.966707a1c192 from=translated src=- shape=9101350f vocab=56a41001
-/
theorem finite_support_listSum (LP L : List 𝒯.Dart) :
    (Function.support fun γ : G => (LP.map fun d => atom 𝒯 d L γ).sum).Finite := by
  induction LP with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact Set.finite_empty.subset fun γ hγ => (hγ rfl).elim
  | cons d LP ih =>
    refine ((finite_support_atom 𝒯 hfin d L).union ih).subset ?_
    intro γ hγ
    rw [Function.mem_support, List.map_cons, List.sum_cons] at hγ
    by_contra hnot
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hnot
    exact hγ (by rw [hnot.1, hnot.2, add_zero])

include hfin hτ in
/--
@isnad1 id=eq.3h8v.s11.a82389b957df from=translated src=- shape=785279a1 vocab=d460ae84
-/
theorem finsum_listSum (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v) (LP L : List 𝒯.Dart) :
    ∑ᶠ γ : G, (LP.map fun d => atom 𝒯 d L γ).sum =
      ∑ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) *
        ((LP.map (dartIndex 𝒯 (eE e).1)).sum * (L.map (dartIndex 𝒯 (eE e).1)).sum) := by
  induction LP with
  | nil =>
    simp only [List.map_nil, List.sum_nil, zero_mul, mul_zero, Finset.sum_const_zero]
    exact finsum_zero
  | cons d LP ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [finsum_add_distrib (finite_support_atom 𝒯 hfin d L) (finite_support_listSum 𝒯 hfin LP L),
      finsum_atom 𝒯 τ hτ eE hfin hadj d L, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring

end Lists

/--
@isnad1 id=eq.3h12v.s11.439a39ff0114 from=translated src=- shape=38467929 vocab=f35dc29a
-/
theorem main {G : Type} [Group G] {W : Type} [DecidableEq W] [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hfin : ∀ w : W, Finite (stabilizer G w))
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)] {E : Type} [Fintype E]
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    ∑ᶠ γ : G, walkOverlap P (Q.map (smulHom γ)) =
      ∑ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) *
        (walkCycle 𝒯 (fun e => (eE e).1) P e * walkCycle 𝒯 (fun e => (eE e).1) Q e) := by
  have hfinD : ∀ d : 𝒯.Dart, Finite (stabilizer G d) := fun d => by
    haveI := hfin d.fst
    exact Finite.of_injective (Subgroup.inclusion (stabilizer_dart_le 𝒯 d)) (Subgroup.inclusion_injective _)
  have hexp : ∀ γ : G, walkOverlap P (Q.map (smulHom γ)) = (P.darts.map fun d => atom 𝒯 d Q.darts γ).sum := by
    intro γ
    rw [walkOverlap_eq_sum, SimpleGraph.Walk.darts_map]
    rfl
  simp_rw [hexp]
  exact finsum_listSum 𝒯 τ hτ eE hfinD hadj P.darts Q.darts

end CerednikDrinfeld.Mumford.TreeSumW

open _root_.CerednikDrinfeld.Mumford open _root_.P2MW.S_CerednikDrinfeld_Mumford_finsum_walkOverlap_map_smulHom_eq_sum_stabWidth_mul_walkCycle_mul_walkCycle.CerednikDrinfeld.Mumford open _root_.MulAction

/--
@isnad1 id=eq.3h12v.s11.439a39ff0114 from=translated src=- shape=38467929 vocab=f35dc29a
-/
theorem solution
    {G : Type} [Group G] {W : Type} [DecidableEq W] [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hfin : ∀ w : W, Finite (stabilizer G w))
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)] {E : Type} [Fintype E]
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    ∑ᶠ γ : G, walkOverlap P (Q.map (smulHom γ)) =
      ∑ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) *
        (walkCycle 𝒯 (fun e => (eE e).1) P e * walkCycle 𝒯 (fun e => (eE e).1) Q e) :=
  CerednikDrinfeld.Mumford.TreeSumW.main 𝒯 hfin τ hτ hadj eE P Q
