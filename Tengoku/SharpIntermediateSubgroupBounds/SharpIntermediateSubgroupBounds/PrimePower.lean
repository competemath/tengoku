import Tengoku.Seed.GroupTheory.IndexNormal
import Tengoku.Seed.GroupTheory.Sylow
import Tengoku.Seed.GroupTheory.Coset.Card
import Tengoku.Seed.Algebra.Group.Subgroup.Pointwise
import Tengoku.Seed.Order.Atoms
import Tengoku.Seed.GroupTheory.GroupAction.Quotient
import Tengoku.SharpIntermediateSubgroupBounds.SharpIntermediateSubgroupBounds.QBinomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The exact prime-power layers

This file contains the finite-group part of the exact prime-power-index theorem.  We formulate
the induction inside one ambient finite group; this avoids repeatedly transporting subgroups
through subtype groups.
-/

namespace SharpIntermediateSubgroupBounds

open scoped BigOperators Pointwise

noncomputable section

variable {G : Type*} [Group G] [Fintype G]

noncomputable local instance subgroupCarrierFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

noncomputable local instance subgroupIntervalFintype (H : Subgroup G) : Fintype (Set.Ici H) :=
  Fintype.ofFinite (Set.Ici H)

/-- A subgroup of prime index is maximal.  This small lemma is useful below because the
prime-index subgroup is chosen by its cardinality, rather than by a maximality argument.-/
theorem isCoatom_of_prime_index (H : Subgroup G) (hprime : H.index.Prime) : IsCoatom H := by
  refine ⟨?_, ?_⟩
  · intro htop
    exact hprime.ne_one (by simp [htop])
  · intro K hHK
    have hdvd : K.index ∣ H.index := H.index_dvd_of_le hHK.le
    rcases hprime.eq_one_or_self_of_dvd K.index hdvd with hK | hK
    · exact Subgroup.index_eq_one.mp hK
    · have htower := H.relIndex_mul_index hHK.le
      have hrel : H.relIndex K = 1 := by
        apply Nat.mul_right_cancel
          (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := H)))
        simpa [hK] using htower
      exact ((not_le_of_gt hHK) (Subgroup.relIndex_eq_one.mp hrel)).elim

/-- In a finite `p`-group, a subgroup of index `p` is normal.-/
theorem normal_of_index_eq_prime_of_isPGroup {p : ℕ} (hp : p.Prime)
    (hG : IsPGroup p G) (H : Subgroup G) (hindex : H.index = p) : H.Normal := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hcard⟩ := hG.exists_card_eq
  have hc : c ≠ 0 := by
    intro hc
    have hle := Nat.le_of_dvd Nat.card_pos H.index_dvd_card
    rw [hindex, hcard, hc, pow_zero] at hle
    have := hp.one_lt
    omega
  apply H.normal_of_index_eq_minFac_card
  rw [hindex, hcard, hp.pow_minFac hc]

/-- The fiber of the intersection map across a fixed coatom.-/
abbrev CoatomFiber (M V : Subgroup G) :=
  {Q : Subgroup G // Q ⊓ M = V ∧ ¬ Q ≤ M}

noncomputable local instance coatomFiberFintype (M V : Subgroup G) :
    Fintype (CoatomFiber M V) := Fintype.ofFinite _

/-- All subgroups with a fixed intersection with a normal coatom inject into the corresponding
coset space.  Notice that this statement does not require a `p`-group hypothesis.-/
theorem coatomFiber_card_le_relIndex (M V : Subgroup G) [M.Normal]
    (hM : IsCoatom M) (hVM : V ≤ M) :
    Fintype.card (CoatomFiber M V) ≤ V.relIndex M := by
  classical
  obtain ⟨x, -, hxM⟩ := SetLike.exists_of_lt hM.lt_top
  have sup_eq_top (S : Subgroup G) (hS : ¬ S ≤ M) : S ⊔ M = ⊤ := by
    apply (hM.ne_iff_eq_top le_sup_right).mp
    intro hSM
    exact hS (le_sup_left.trans_eq hSM)
  have exists_rep (Q : CoatomFiber M V) : ∃ m : M, x * (m : G) ∈ Q.1 := by
    have hxQM : x ∈ Q.1 ⊔ M := by
      rw [sup_eq_top Q.1 Q.2.2]
      exact Subgroup.mem_top x
    obtain ⟨q, hq, m, hm, hqmx⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := Q.1) (t := M) (x := x)).mp hxQM
    refine ⟨⟨m⁻¹, M.inv_mem hm⟩, ?_⟩
    rw [← hqmx]
    simpa [mul_assoc] using hq
  let rep : CoatomFiber M V → M := fun Q ↦ Classical.choose (exists_rep Q)
  have rep_mem (Q : CoatomFiber M V) : x * (rep Q : G) ∈ Q.1 :=
    Classical.choose_spec (exists_rep Q)
  have hVQ (Q : CoatomFiber M V) : V ≤ Q.1 := by
    intro v hv
    have hvInf : v ∈ Q.1 ⊓ M := by
      rw [Q.2.1]
      exact hv
    exact hvInf.1
  have generated (Q : CoatomFiber M V) :
      V ⊔ Subgroup.closure {x * (rep Q : G)} = Q.1 := by
    apply le_antisymm
    · refine sup_le (hVQ Q) ((Subgroup.closure_le Q.1).2 ?_)
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact rep_mem Q
    · let R : Subgroup G := V ⊔ Subgroup.closure {x * (rep Q : G)}
      have hRQ : R ≤ Q.1 := by
        refine sup_le (hVQ Q) ((Subgroup.closure_le Q.1).2 ?_)
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact rep_mem Q
      have hqR : x * (rep Q : G) ∈ R :=
        Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _))
      have hqM : x * (rep Q : G) ∉ M := by
        intro h
        apply hxM
        have hmInv : (rep Q : G)⁻¹ ∈ M := M.inv_mem (rep Q).2
        simpa [mul_assoc] using M.mul_mem h hmInv
      have hRnot : ¬ R ≤ M := fun h ↦ hqM (h hqR)
      have hRM : R ⊔ M = ⊤ := sup_eq_top R hRnot
      intro y hy
      have hyRM : y ∈ R ⊔ M := by
        rw [hRM]
        exact Subgroup.mem_top y
      obtain ⟨r, hr, m, hm, hrmy⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := R) (t := M) (x := y)).mp hyRM
      have hmQ : m ∈ Q.1 := by
        have hm_eq : m = r⁻¹ * y := by
          rw [← hrmy]
          simp
        rw [hm_eq]
        exact Q.1.mul_mem (Q.1.inv_mem (hRQ hr)) hy
      have hmV : m ∈ V := by
        rw [← Q.2.1]
        exact ⟨hmQ, hm⟩
      have hmR : m ∈ R := Subgroup.mem_sup_left hmV
      rw [← hrmy]
      exact R.mul_mem hr hmR
  let f : CoatomFiber M V → M ⧸ V.subgroupOf M := fun Q ↦ QuotientGroup.mk (rep Q)
  have fiber_le (A B : CoatomFiber M V) (hf : f A = f B) : B.1 ≤ A.1 := by
    rw [← generated B]
    refine sup_le (hVQ A) ((Subgroup.closure_le A.1).2 ?_)
    rw [Set.singleton_subset_iff]
    have hvM : (rep A)⁻¹ * rep B ∈ V.subgroupOf M := QuotientGroup.eq.mp hf
    have hv : (rep A : G)⁻¹ * (rep B : G) ∈ V := Subgroup.mem_subgroupOf.mp hvM
    have hvA : (rep A : G)⁻¹ * (rep B : G) ∈ A.1 := hVQ A hv
    have hprod := A.1.mul_mem (rep_mem A) hvA
    simpa [mul_assoc] using hprod
  have hf_injective : Function.Injective f := by
    intro A B hf
    apply Subtype.ext
    exact le_antisymm (fiber_le B A hf.symm) (fiber_le A B hf)
  calc
    Fintype.card (CoatomFiber M V) ≤ Fintype.card (M ⧸ V.subgroupOf M) :=
      Fintype.card_le_of_injective f hf_injective
    _ = V.relIndex M := by
      rw [Fintype.card_eq_nat_card]
      rfl

/-- Subgroups between `T` and `P` having index `p^k` in `P`.-/
def primePowerLayer (p k : ℕ) (T P : Subgroup G) : Finset (Subgroup G) :=
  by
    classical
    exact Finset.univ.filter fun Q ↦ T ≤ Q ∧ Q ≤ P ∧ Q.relIndex P = p ^ k

@[simp]
theorem mem_primePowerLayer {p k : ℕ} {T P Q : Subgroup G} :
    Q ∈ primePowerLayer p k T P ↔ T ≤ Q ∧ Q ≤ P ∧ Q.relIndex P = p ^ k := by
  simp [primePowerLayer]

/-- Passing from an ambient subgroup `P` to the group `P` itself preserves every relative-index
layer.-/
theorem primePowerLayer_card_subgroup {p k : ℕ} {T P : Subgroup G} (hTP : T ≤ P) :
    (primePowerLayer p k T P).card =
      (primePowerLayer p k (T.subgroupOf P) (⊤ : Subgroup P)).card := by
  classical
  let toSubgroup (Q : ↑(primePowerLayer p k T P)) :
      ↑(primePowerLayer p k (T.subgroupOf P) (⊤ : Subgroup P)) := by
    refine ⟨Q.1.subgroupOf P, ?_⟩
    have hQ := (mem_primePowerLayer.mp Q.2)
    apply mem_primePowerLayer.mpr
    refine ⟨Subgroup.comap_mono hQ.1, le_top, ?_⟩
    simpa using
      (Subgroup.relIndex_subgroupOf (H := Q.1) (K := P) (L := P) le_rfl).trans hQ.2.2
  let fromSubgroup (R : ↑(primePowerLayer p k (T.subgroupOf P) (⊤ : Subgroup P))) :
      ↑(primePowerLayer p k T P) := by
    refine ⟨R.1.map P.subtype, ?_⟩
    have hR := mem_primePowerLayer.mp R.2
    apply mem_primePowerLayer.mpr
    refine ⟨?_, Subgroup.map_subtype_le R.1, ?_⟩
    · calc
        T = Subgroup.map P.subtype (T.subgroupOf P) :=
          (Subgroup.map_subgroupOf_eq_of_le hTP).symm
        _ ≤ Subgroup.map P.subtype R.1 := Subgroup.map_mono hR.1
    · have hi := Subgroup.relIndex_map_map_of_injective R.1 (⊤ : Subgroup P)
          P.subtype_injective
      have htop : Subgroup.map P.subtype (⊤ : Subgroup P) = P := by
        rw [← P.subtype.range_eq_map, Subgroup.range_subtype]
      rw [htop] at hi
      exact hi.trans hR.2.2
  have hleft (Q : ↑(primePowerLayer p k T P)) : fromSubgroup (toSubgroup Q) = Q := by
    apply Subtype.ext
    exact Subgroup.map_subgroupOf_eq_of_le (mem_primePowerLayer.mp Q.2).2.1
  have hright (R : ↑(primePowerLayer p k (T.subgroupOf P) (⊤ : Subgroup P))) :
      toSubgroup (fromSubgroup R) = R := by
    apply Subtype.ext
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective R.1
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr
    { toFun := toSubgroup
      invFun := fromSubgroup
      left_inv := hleft
      right_inv := hright }

/-- The Gaussian layer bound for an arbitrary subgroup of a finite `p`-group.-/
theorem pGroup_primePowerLayer_card_le {p a : ℕ} (hp : p.Prime) (hG : IsPGroup p G)
    (T : Subgroup G) (hindex : T.index = p ^ a) (k : ℕ) :
    (primePowerLayer p k T ⊤).card ≤ qBinom p a k := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  induction a generalizing G T k with
  | zero =>
      have hT : T = ⊤ := Subgroup.index_eq_one.mp (by simpa using hindex)
      subst T
      cases k with
      | zero =>
          have hlayer : primePowerLayer p 0 (⊤ : Subgroup G) ⊤ = {⊤} := by
            ext Q
            constructor
            · intro hQ
              have hQl := mem_primePowerLayer.mp hQ
              exact Finset.mem_singleton.mpr
                (top_unique (Subgroup.relIndex_eq_one.mp (by simpa using hQl.2.2)))
            · intro hQ
              have hQtop := Finset.mem_singleton.mp hQ
              subst Q
              exact mem_primePowerLayer.mpr ⟨le_rfl, le_rfl, by simp⟩
          simp [hlayer]
      | succ k =>
          have hpow : p ^ (k + 1) ≠ 1 := by
            exact (Nat.one_lt_pow (by omega) hp.one_lt).ne'
          simp [primePowerLayer, hpow, hpow.symm]
  | succ a ih =>
      cases k with
      | zero =>
          have hlayer : primePowerLayer p 0 T ⊤ = {⊤} := by
            ext Q
            constructor
            · intro hQ
              have hQl := mem_primePowerLayer.mp hQ
              exact Finset.mem_singleton.mpr
                (top_unique (Subgroup.relIndex_eq_one.mp (by simpa using hQl.2.2)))
            · intro hQ
              have hQtop := Finset.mem_singleton.mp hQ
              subst Q
              exact mem_primePowerLayer.mpr ⟨le_top, le_rfl, by simp⟩
          simp [hlayer]
      | succ k =>
          obtain ⟨b, hTcard⟩ := (hG.to_subgroup T).exists_card_eq
          have hcardG : Nat.card G = p ^ (b + (a + 1)) := by
            rw [← T.card_mul_index, hTcard, hindex, ← pow_add]
          have hdvd : p ^ (b + a) ∣ Nat.card G := by
            rw [hcardG, show b + (a + 1) = (b + a) + 1 by omega, pow_succ]
            exact dvd_mul_right _ _
          obtain ⟨M, hMcard, hTM⟩ :=
            Sylow.exists_subgroup_card_pow_prime_le (G := G) p hdvd T hTcard (by omega)
          have hMindex : M.index = p := by
            apply Nat.mul_left_cancel (pow_pos hp.pos _)
            calc
              p ^ (b + a) * M.index = Nat.card G := by
                rw [← hMcard]
                exact M.card_mul_index
              _ = p ^ (b + a) * p := by
                rw [hcardG, show b + (a + 1) = (b + a) + 1 by omega, pow_succ]
          letI : M.Normal := normal_of_index_eq_prime_of_isPGroup hp hG M hMindex
          have hMcoatom : IsCoatom M := isCoatom_of_prime_index M (hMindex.symm ▸ hp)
          have hTrelM : T.relIndex M = p ^ a := by
            have htower := T.relIndex_mul_index hTM
            apply Nat.mul_right_cancel hp.pos
            simpa [hMindex, hindex, pow_succ] using htower
          let layer := primePowerLayer p (k + 1) T ⊤
          let inside := layer.filter fun Q ↦ Q ≤ M
          let outside := layer.filter fun Q ↦ ¬Q ≤ M
          have hsplit : inside.card + outside.card = layer.card := by
            exact Finset.card_filter_add_card_filter_not (s := layer) (fun Q ↦ Q ≤ M)
          let lowerLayer := primePowerLayer p k T M
          have hins_maps : (inside : Set (Subgroup G)) ⊆ (lowerLayer : Set (Subgroup G)) := by
            intro Q hQ
            have hQi := Finset.mem_filter.mp hQ
            have hQl := mem_primePowerLayer.mp hQi.1
            apply mem_primePowerLayer.mpr
            refine ⟨hQl.1, hQi.2, ?_⟩
            have htower := Q.relIndex_mul_index hQi.2
            apply Nat.mul_right_cancel hp.pos
            calc
              Q.relIndex M * p = Q.index := by
                rw [← hMindex]
                exact htower
              _ = p ^ (k + 1) := by
                rw [← Subgroup.relIndex_top_right]
                exact hQl.2.2
              _ = p ^ k * p := by rw [pow_succ]
          have hlower : lowerLayer.card ≤ qBinom p a k := by
            rw [primePowerLayer_card_subgroup hTM]
            exact ih (G := M) (hG.to_subgroup M) (T.subgroupOf M) (by
              simpa using
                (Subgroup.relIndex_subgroupOf (H := T) (K := M) (L := M) le_rfl).trans hTrelM) k
          have hinside : inside.card ≤ qBinom p a k :=
            (Finset.card_le_card hins_maps).trans hlower
          let upperLayer := primePowerLayer p (k + 1) T M
          have hout_maps : (outside : Set (Subgroup G)).MapsTo (fun Q ↦ Q ⊓ M) upperLayer := by
            intro Q hQ
            have hQo := Finset.mem_filter.mp hQ
            have hQl := mem_primePowerLayer.mp hQo.1
            have hsup : M ⊔ Q = ⊤ := by
              apply hMcoatom.2
              refine lt_of_le_of_ne le_sup_left ?_
              intro heq
              exact hQo.2 (le_sup_right.trans_eq heq.symm)
            have hVrelQ : (Q ⊓ M).relIndex Q = p := by
              calc
                (Q ⊓ M).relIndex Q = M.relIndex Q := by
                  simpa [inf_comm] using M.inf_relIndex_right Q
                _ = M.relIndex (M ⊔ Q) := (Q.relIndex_sup_left M).symm
                _ = p := by rw [hsup, Subgroup.relIndex_top_right, hMindex]
            have hVrelM : (Q ⊓ M).relIndex M = p ^ (k + 1) := by
              have htowerM := (Q ⊓ M).relIndex_mul_index inf_le_right
              have htowerQ := (Q ⊓ M).relIndex_mul_index inf_le_left
              have hQindex : Q.index = p ^ (k + 1) := by
                rw [← Subgroup.relIndex_top_right]
                exact hQl.2.2
              apply Nat.mul_right_cancel hp.pos
              calc
                (Q ⊓ M).relIndex M * p = (Q ⊓ M).index := by
                  simpa [hMindex] using htowerM
                _ = (Q ⊓ M).relIndex Q * Q.index := htowerQ.symm
                _ = p * p ^ (k + 1) := by rw [hVrelQ, hQindex]
                _ = p ^ (k + 1) * p := by ac_rfl
            apply mem_primePowerLayer.mpr
            exact ⟨le_inf hQl.1 hTM, inf_le_right, hVrelM⟩
          have houtside : outside.card ≤ p ^ (k + 1) * qBinom p a (k + 1) := by
            rw [Finset.card_eq_sum_card_fiberwise hout_maps]
            calc
              ∑ V ∈ upperLayer, (outside.filter fun Q ↦ Q ⊓ M = V).card ≤
                  ∑ _V ∈ upperLayer, p ^ (k + 1) := by
                    apply Finset.sum_le_sum
                    intro V hV
                    let actualFiber := outside.filter fun Q ↦ Q ⊓ M = V
                    let embed (Q : ↑actualFiber) : CoatomFiber M V := by
                      have hQf := Finset.mem_filter.mp Q.2
                      have hQo := Finset.mem_filter.mp hQf.1
                      exact ⟨Q.1, hQf.2, hQo.2⟩
                    have hembed : Function.Injective embed := by
                      intro Q R hQR
                      apply Subtype.ext
                      exact congrArg (fun X : CoatomFiber M V ↦ X.1) hQR
                    have hactual : actualFiber.card ≤ Fintype.card (CoatomFiber M V) := by
                      rw [← Fintype.card_coe]
                      exact Fintype.card_le_of_injective embed hembed
                    have hVmem := mem_primePowerLayer.mp hV
                    exact hactual.trans
                      ((coatomFiber_card_le_relIndex M V hMcoatom hVmem.2.1).trans_eq
                        hVmem.2.2)
              _ = upperLayer.card * p ^ (k + 1) :=
                    Finset.sum_const_nat fun _ _ ↦ rfl
              _ ≤ qBinom p a (k + 1) * p ^ (k + 1) := by
                    gcongr
                    rw [primePowerLayer_card_subgroup hTM]
                    exact ih (G := M) (hG.to_subgroup M) (T.subgroupOf M) (by
                      simpa using
                        (Subgroup.relIndex_subgroupOf (H := T) (K := M) (L := M)
                          le_rfl).trans hTrelM) (k + 1)
              _ = p ^ (k + 1) * qBinom p a (k + 1) := by ac_rfl
          rw [← hsplit]
          calc
            inside.card + outside.card ≤
                qBinom p a k + p ^ (k + 1) * qBinom p a (k + 1) :=
              Nat.add_le_add hinside houtside
            _ = qBinom p (a + 1) (k + 1) := (qBinom_succ_succ p a k).symm

/-- If `[G:H]` is a power of `p`, a Sylow `p`-subgroup of `G` can be chosen so that its
action on `G/H` is transitive.  Its stabilizer has exactly the same prime-power index.-/
theorem exists_sylow_pretransitive_of_index_primePower {p a : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hindex : H.index = p ^ a) :
    ∃ P : Sylow p G,
      MulAction.IsPretransitive P (G ⧸ H) ∧ H.relIndex (P : Subgroup G) = p ^ a := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let S : Sylow p H := Sylow.nonempty.some
  obtain ⟨P, hPcomap⟩ := S.exists_comap_subtype_eq
  obtain ⟨b, hScard⟩ := S.2.exists_card_eq
  let e : H.subgroupOf (P : Subgroup G) ≃ S :=
    { toFun := fun x ↦ by
        let y : H := ⟨(x.1 : G), x.2⟩
        refine ⟨y, ?_⟩
        rw [← hPcomap]
        exact x.1.2
      invFun := fun y ↦ by
        have hyP : (y.1 : G) ∈ (P : Subgroup G) := by
          have : y.1 ∈ P.comap H.subtype := by simpa [hPcomap] using y.2
          exact this
        exact ⟨⟨(y.1 : G), hyP⟩, y.1.2⟩
      left_inv := by intro x; ext; rfl
      right_inv := by intro y; ext; rfl }
  have hinterCard : Nat.card (H.subgroupOf (P : Subgroup G)) = p ^ b := by
    rw [Nat.card_congr e, hScard]
  have hPcard_tower :
      Nat.card (H.subgroupOf (P : Subgroup G)) * H.relIndex (P : Subgroup G) = Nat.card P := by
    exact (H.subgroupOf (P : Subgroup G)).card_mul_index
  have hrel_le : H.relIndex (P : Subgroup G) ≤ H.index := by
    simpa using H.relIndex_le_of_le_right (K := (P : Subgroup G)) (L := ⊤) le_top
      Subgroup.index_ne_zero_of_finite
  have hPcard_le : Nat.card P ≤ p ^ (b + a) := by
    rw [← hPcard_tower, hinterCard, pow_add]
    exact Nat.mul_le_mul_left _ (hrel_le.trans_eq hindex)
  have hpow_dvd_cardG : p ^ (b + a) ∣ Nat.card G := by
    refine ⟨S.index, ?_⟩
    calc
      Nat.card G = Nat.card H * H.index := H.card_mul_index.symm
      _ = (Nat.card S * S.index) * p ^ a := by rw [hindex, S.card_mul_index]
      _ = p ^ (b + a) * S.index := by rw [hScard, pow_add]; ac_rfl
  have hpow_dvd_cardP : p ^ (b + a) ∣ Nat.card P :=
    P.pow_dvd_card_of_pow_dvd_card hpow_dvd_cardG
  have hPcard : Nat.card P = p ^ (b + a) := by
    apply le_antisymm hPcard_le
    exact Nat.le_of_dvd Nat.card_pos hpow_dvd_cardP
  have hrel : H.relIndex (P : Subgroup G) = p ^ a := by
    apply Nat.mul_left_cancel (pow_pos hp.pos _)
    calc
      p ^ b * H.relIndex (P : Subgroup G) = Nat.card P := by
        rw [← hinterCard]
        exact hPcard_tower
      _ = p ^ b * p ^ a := by rw [hPcard, pow_add]
  have hstab :
      MulAction.stabilizer P ((1 : G) : G ⧸ H) = H.subgroupOf (P : Subgroup G) := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    have hsmul : g • ((1 : G) : G ⧸ H) = (((g : G) * 1 : G) : G ⧸ H) := rfl
    rw [hsmul, mul_one, QuotientGroup.eq]
    simp only [mul_one, Subgroup.inv_mem_iff, Subgroup.mem_subgroupOf]
  have horbit : MulAction.orbit P ((1 : G) : G ⧸ H) = Set.univ :=
    (Set.eq_univ_iff_ncard (MulAction.orbit P ((1 : G) : G ⧸ H))).2 <| by
        calc
          (MulAction.orbit P ((1 : G) : G ⧸ H)).ncard =
              (MulAction.stabilizer P ((1 : G) : G ⧸ H)).index :=
            (MulAction.index_stabilizer P ((1 : G) : G ⧸ H)).symm
          _ = H.relIndex (P : Subgroup G) := by rw [hstab]; rfl
          _ = p ^ a := hrel
          _ = Nat.card (G ⧸ H) := by rw [← H.index_eq_card, hindex]
  have hpre : MulAction.IsPretransitive P (G ⧸ H) := ⟨by
    intro y z
    have hy : y ∈ MulAction.orbit P ((1 : G) : G ⧸ H) := by rw [horbit]; trivial
    have hz : z ∈ MulAction.orbit P ((1 : G) : G ⧸ H) := by rw [horbit]; trivial
    obtain ⟨r, hr⟩ := hy
    obtain ⟨s, hs⟩ := hz
    refine ⟨s * r⁻¹, ?_⟩
    rw [← hr, ← hs]
    simp [smul_smul]⟩
  exact ⟨P, hpre, hrel⟩

/-- Transitivity on `G/H` descends to every quotient `G/K` with `H ≤ K`.-/
theorem pretransitive_quotient_of_le {P H K : Subgroup G}
    (hpre : MulAction.IsPretransitive P (G ⧸ H)) (hHK : H ≤ K) :
    MulAction.IsPretransitive P (G ⧸ K) := by
  letI : MulAction.IsPretransitive P (G ⧸ H) := hpre
  refine ⟨?_⟩
  rintro ⟨g⟩ ⟨g'⟩
  obtain ⟨p, hp'⟩ := MulAction.exists_smul_eq P ((g : G) : G ⧸ H) ((g' : G) : G ⧸ H)
  refine ⟨p, ?_⟩
  apply QuotientGroup.eq.mpr
  exact hHK (QuotientGroup.eq.mp hp')

/-- Under a transitive `P`-action on `G/H`, intersection with `P` preserves all later indices.-/
theorem relIndex_eq_index_of_pretransitive {P H K : Subgroup G}
    (hpre : MulAction.IsPretransitive P (G ⧸ H)) (hHK : H ≤ K) :
    K.relIndex P = K.index := by
  letI : MulAction.IsPretransitive P (G ⧸ K) := pretransitive_quotient_of_le hpre hHK
  have hstab :
      MulAction.stabilizer P ((1 : G) : G ⧸ K) = K.subgroupOf P := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    have hsmul : g • ((1 : G) : G ⧸ K) = (((g : G) * 1 : G) : G ⧸ K) := rfl
    rw [hsmul, mul_one, QuotientGroup.eq]
    simp only [mul_one, Subgroup.inv_mem_iff, Subgroup.mem_subgroupOf]
  calc
    K.relIndex P = (K.subgroupOf P).index := rfl
    _ = (MulAction.stabilizer P ((1 : G) : G ⧸ K)).index := by rw [hstab]
    _ = Nat.card (G ⧸ K) := MulAction.index_stabilizer_of_transitive P _
    _ = K.index := rfl

/-- A subgroup containing `H` is determined by its intersection with a subgroup acting
transitively on `G/H`.-/
theorem subgroupOf_injective_of_pretransitive {P H : Subgroup G}
    (hpre : MulAction.IsPretransitive P (G ⧸ H)) :
    Set.InjOn (fun K : Subgroup G ↦ K.subgroupOf P) (Set.Ici H) := by
  letI : MulAction.IsPretransitive P (G ⧸ H) := hpre
  intro K hHK L hHL heq
  change K.subgroupOf P = L.subgroupOf P at heq
  apply le_antisymm
  · intro g hgK
    obtain ⟨p, hp⟩ :=
      MulAction.exists_smul_eq P (((1 : G) : G ⧸ H)) ((g : G) : G ⧸ H)
    have hsmul : p • ((1 : G) : G ⧸ H) = (((p : G) * 1 : G) : G ⧸ H) := rfl
    rw [hsmul, mul_one] at hp
    have hpgH : (p : G)⁻¹ * g ∈ H := QuotientGroup.eq.mp hp
    have hpgK : (p : G)⁻¹ * g ∈ K := hHK hpgH
    have hpK : (p : G) ∈ K := by
      have := K.mul_mem hgK (K.inv_mem hpgK)
      simpa [mul_assoc] using this
    have hpL : (p : G) ∈ L := by
      have hpSub : p ∈ K.subgroupOf P := hpK
      rw [heq] at hpSub
      exact hpSub
    have hpgL : (p : G)⁻¹ * g ∈ L := hHL hpgH
    have := L.mul_mem hpL hpgL
    simpa [mul_assoc] using this
  · intro g hgL
    obtain ⟨p, hp⟩ :=
      MulAction.exists_smul_eq P (((1 : G) : G ⧸ H)) ((g : G) : G ⧸ H)
    have hsmul : p • ((1 : G) : G ⧸ H) = (((p : G) * 1 : G) : G ⧸ H) := rfl
    rw [hsmul, mul_one] at hp
    have hpgH : (p : G)⁻¹ * g ∈ H := QuotientGroup.eq.mp hp
    have hpgL : (p : G)⁻¹ * g ∈ L := hHL hpgH
    have hpL : (p : G) ∈ L := by
      have := L.mul_mem hgL (L.inv_mem hpgL)
      simpa [mul_assoc] using this
    have hpK : (p : G) ∈ K := by
      have hpSub : p ∈ L.subgroupOf P := hpL
      rw [← heq] at hpSub
      exact hpSub
    have hpgK : (p : G)⁻¹ * g ∈ K := hHK hpgH
    have := K.mul_mem hpK hpgK
    simpa [mul_assoc] using this

/-- The Gaussian layer bound for an arbitrary finite group inclusion of prime-power index.-/
theorem primePowerLayer_card_le {p a k : ℕ} (hp : p.Prime) (H : Subgroup G)
    (hindex : H.index = p ^ a) :
    (primePowerLayer p k H ⊤).card ≤ qBinom p a k := by
  classical
  obtain ⟨P, hpre, hrel⟩ := exists_sylow_pretransitive_of_index_primePower hp H hindex
  let target := primePowerLayer p k (H.subgroupOf (P : Subgroup G)) (⊤ : Subgroup P)
  let source := primePowerLayer p k H ⊤
  have hmaps : (source : Set (Subgroup G)).MapsTo (fun K ↦ K.subgroupOf (P : Subgroup G)) target := by
    intro K hK
    have hKl := mem_primePowerLayer.mp hK
    apply mem_primePowerLayer.mpr
    refine ⟨Subgroup.comap_mono hKl.1, le_top, ?_⟩
    have hKi : K.index = p ^ k := by simpa using hKl.2.2
    have hKP : K.relIndex (P : Subgroup G) = p ^ k :=
      (relIndex_eq_index_of_pretransitive hpre hKl.1).trans hKi
    simpa using
      (Subgroup.relIndex_subgroupOf (H := K) (K := (P : Subgroup G))
        (L := (P : Subgroup G)) le_rfl).trans hKP
  have hinj : (source : Set (Subgroup G)).InjOn (fun K ↦ K.subgroupOf (P : Subgroup G)) :=
    (subgroupOf_injective_of_pretransitive hpre).mono fun _ h ↦
      (mem_primePowerLayer.mp h).1
  calc
    source.card ≤ target.card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ qBinom p a k := pGroup_primePowerLayer_card_le hp P.2
      (H.subgroupOf (P : Subgroup G)) hrel k

/-- The finite set of all intermediate subgroups above `H`.-/
def intermediateSubgroups (H : Subgroup G) : Finset (Subgroup G) :=
  by
    classical
    exact Finset.univ.filter fun K ↦ H ≤ K

@[simp] theorem mem_intermediateSubgroups {H K : Subgroup G} :
    K ∈ intermediateSubgroups H ↔ H ≤ K := by
  simp [intermediateSubgroups]

/-- The finset and order-interval presentations of the intermediate subgroups are equinumerous.-/
theorem intermediateSubgroups_card_eq_Ici (H : Subgroup G) :
    (intermediateSubgroups H).card = Fintype.card (Set.Ici H) := by
  classical
  let e : ↑(intermediateSubgroups H) ≃ Set.Ici H :=
    { toFun := fun K ↦ ⟨K.1, mem_intermediateSubgroups.mp K.2⟩
      invFun := fun K ↦ ⟨K.1, mem_intermediateSubgroups.mpr K.2⟩
      left_inv := by intro K; rfl
      right_inv := by intro K; rfl }
  rw [← Fintype.card_coe]
  exact Fintype.card_congr e

/-- Exact prime-power interval upper bound.-/
theorem intermediateSubgroups_card_le_totalQBinom {p a : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hindex : H.index = p ^ a) :
    (intermediateSubgroups H).card ≤ totalQBinom p a := by
  classical
  let layers : Finset (Subgroup G) :=
    (Finset.range (a + 1)).biUnion fun k ↦ primePowerLayer p k H ⊤
  have hcover : intermediateSubgroups H ⊆ layers := by
    intro K hK
    have hHK := mem_intermediateSubgroups.mp hK
    have hdvd : K.index ∣ p ^ a := by
      rw [← hindex]
      exact H.index_dvd_of_le hHK
    obtain ⟨k, hk, hkindex⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    apply Finset.mem_biUnion.mpr
    exact ⟨k, Finset.mem_range.mpr (by omega), mem_primePowerLayer.mpr
      ⟨hHK, le_top, by simpa using hkindex⟩⟩
  calc
    (intermediateSubgroups H).card ≤ layers.card := Finset.card_le_card hcover
    _ ≤ ∑ k ∈ Finset.range (a + 1), (primePowerLayer p k H ⊤).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (a + 1), qBinom p a k := by
      exact Finset.sum_le_sum fun k _ ↦ primePowerLayer_card_le hp H hindex
    _ = totalQBinom p a := by
      rw [totalQBinom, Fin.sum_univ_eq_sum_range]

/-- Order-interval form of the exact prime-power upper bound.-/
theorem intermediate_interval_card_le_totalQBinom {p a : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hindex : H.index = p ^ a) :
    Fintype.card (Set.Ici H) ≤ totalQBinom p a := by
  rw [← intermediateSubgroups_card_eq_Ici]
  exact intermediateSubgroups_card_le_totalQBinom hp H hindex

/-- The canonical order isomorphism from subgroups of an elementary abelian
group to linear subspaces of its additive vector space.-/
def elementarySubgroupSubmoduleIso (p a : ℕ) :
    Subgroup (Multiplicative (Fin a → ZMod p)) ≃o
      Submodule (ZMod p) (Fin a → ZMod p) :=
  AddSubgroup.toSubgroup.symm.trans (AddSubgroup.toZModSubmodule p)

/-- The preceding order isomorphism is the identity on underlying vectors.-/
def elementaryCarrierEquiv (p a : ℕ)
    (Q : Subgroup (Multiplicative (Fin a → ZMod p))) :
    Q ≃ elementarySubgroupSubmoduleIso p a Q where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A subgroup of an elementary abelian group has cardinality `p` to its
linear dimension.-/
theorem card_elementarySubgroup {p a : ℕ} [Fact p.Prime]
    (Q : Subgroup (Multiplicative (Fin a → ZMod p))) :
    Nat.card Q =
      p ^ Module.finrank (ZMod p) (elementarySubgroupSubmoduleIso p a Q) := by
  letI : Fintype (elementarySubgroupSubmoduleIso p a Q) := Fintype.ofFinite _
  rw [Nat.card_congr (elementaryCarrierEquiv p a Q)]
  rw [Nat.card_eq_fintype_card]
  simpa using (Module.card_eq_pow_finrank (K := ZMod p)
    (V := elementarySubgroupSubmoduleIso p a Q))

/-- Index `p^k` is equivalent to codimension `k`, forward direction.-/
theorem elementarySubgroup_finrank_eq_sub_of_index {p a k : ℕ} [Fact p.Prime]
    (hk : k ≤ a) (Q : Subgroup (Multiplicative (Fin a → ZMod p)))
    (hindex : Q.index = p ^ k) :
    Module.finrank (ZMod p) (elementarySubgroupSubmoduleIso p a Q) = a - k := by
  have hcardQ := card_elementarySubgroup Q
  have hcardAmbient : Nat.card (Multiplicative (Fin a → ZMod p)) = p ^ a := by
    rw [Nat.card_eq_fintype_card]
    simpa using (Module.card_eq_pow_finrank (K := ZMod p)
      (V := Fin a → ZMod p))
  have htower := Q.card_mul_index
  have hpowequal :
      p ^ (Module.finrank (ZMod p) (elementarySubgroupSubmoduleIso p a Q) + k) =
        p ^ a := by
    rw [pow_add, ← hcardQ, ← hindex, htower, hcardAmbient]
  have hadd := Nat.pow_right_injective ((Fact.out : p.Prime).two_le) hpowequal
  omega

/-- Index `p^k` is equivalent to codimension `k`, reverse direction.-/
theorem elementarySubgroup_index_eq_pow_of_finrank {p a k : ℕ} [Fact p.Prime]
    (hk : k ≤ a) (Q : Subgroup (Multiplicative (Fin a → ZMod p)))
    (hrank : Module.finrank (ZMod p) (elementarySubgroupSubmoduleIso p a Q) = a - k) :
    Q.index = p ^ k := by
  have hcardQ := card_elementarySubgroup Q
  have hcardAmbient : Nat.card (Multiplicative (Fin a → ZMod p)) = p ^ a := by
    rw [Nat.card_eq_fintype_card]
    simpa using (Module.card_eq_pow_finrank (K := ZMod p)
      (V := Fin a → ZMod p))
  apply Nat.mul_left_cancel (pow_pos (Fact.out : p.Prime).pos _)
  calc
    p ^ (a - k) * Q.index = Nat.card Q * Q.index := by rw [hcardQ, hrank]
    _ = Nat.card (Multiplicative (Fin a → ZMod p)) := Q.card_mul_index
    _ = p ^ a := hcardAmbient
    _ = p ^ (a - k) * p ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]

/-- Every prime-power layer of an elementary abelian group attains the
Gaussian layer bound.-/
theorem elementaryAbelian_primePowerLayer_card_eq_qBinom (p a k : ℕ)
    [Fact p.Prime] (hk : k ≤ a) :
    (primePowerLayer p k
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ⊤).card =
        qBinom p a k := by
  classical
  let E := elementarySubgroupSubmoduleIso p a
  let Target := {W : Submodule (ZMod p) (Fin a → ZMod p) //
    Module.finrank (ZMod p) W = a - k}
  let toTarget (Q : ↑(primePowerLayer p k
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ⊤)) : Target := by
    refine ⟨E Q.1, ?_⟩
    have hQl := mem_primePowerLayer.mp Q.2
    apply elementarySubgroup_finrank_eq_sub_of_index hk Q.1
    rw [← Subgroup.relIndex_top_right]
    exact hQl.2.2
  let fromTarget (W : Target) : ↑(primePowerLayer p k
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ⊤) := by
    refine ⟨E.symm W.1, mem_primePowerLayer.mpr ⟨bot_le, le_top, ?_⟩⟩
    rw [Subgroup.relIndex_top_right]
    apply elementarySubgroup_index_eq_pow_of_finrank hk
    change Module.finrank (ZMod p) (E (E.symm W.1)) = a - k
    rw [E.apply_symm_apply]
    exact W.2
  let e : ↑(primePowerLayer p k
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ⊤) ≃ Target :=
    { toFun := toTarget
      invFun := fromTarget
      left_inv := by intro Q; apply Subtype.ext; exact E.symm_apply_apply Q.1
      right_inv := by intro W; apply Subtype.ext; exact E.apply_symm_apply W.1 }
  rw [← Fintype.card_coe]
  calc
    Fintype.card ↑(primePowerLayer p k
        (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ⊤) =
      Fintype.card Target := Fintype.card_congr e
    _ = Nat.card Target := Fintype.card_eq_nat_card
    _ = qBinom p a (a - k) :=
      card_subspaces_fin_zmod p a (a - k) (Nat.sub_le _ _)
    _ = qBinom p a k := (qBinom_symm (q := p) (n := a) (k := k)
      (Fact.out : p.Prime).two_le hk).symm

/-- Elementary abelian groups attain the bound.-/
theorem elementaryAbelian_interval_card_eq_totalQBinom (p a : ℕ) [Fact p.Prime] :
    Fintype.card
        (Set.Ici (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))) = totalQBinom p a := by
  classical
  let forgetBottom :
      Set.Ici (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ≃
        Subgroup (Multiplicative (Fin a → ZMod p)) :=
    { toFun := Subtype.val
      invFun := fun K ↦
        ⟨K, (show (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ≤ K from bot_le)⟩
      left_inv := by intro K; rfl
      right_inv := by intro K; rfl }
  calc
    Fintype.card (Set.Ici (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))) =
        Fintype.card (Subgroup (Multiplicative (Fin a → ZMod p))) :=
      Fintype.card_congr forgetBottom
    _ = Fintype.card (AddSubgroup (Fin a → ZMod p)) :=
      Fintype.card_congr AddSubgroup.toSubgroup.toEquiv.symm
    _ = Fintype.card (Submodule (ZMod p) (Fin a → ZMod p)) :=
      Fintype.card_congr (AddSubgroup.toZModSubmodule p).toEquiv
    _ = totalQBinom p a := by
      rw [Fintype.card_eq_nat_card]
      exact card_all_subspaces_fin_zmod p a

/-- More generally, a normal inclusion whose quotient is elementary abelian attains equality.-/
theorem normal_elementaryAbelian_quotient_interval_card_eq {p a : ℕ}
    (H : Subgroup G) [H.Normal]
    (e : (G ⧸ H) ≃* Multiplicative (Fin a → ZMod p)) [Fact p.Prime] :
    Fintype.card (Set.Ici H) = totalQBinom p a := by
  classical
  calc
    Fintype.card (Set.Ici H) = Fintype.card (Subgroup (G ⧸ H)) :=
      Fintype.card_congr (QuotientGroup.comapMk'OrderIso H).toEquiv.symm
    _ = Fintype.card (Subgroup (Multiplicative (Fin a → ZMod p))) :=
      Fintype.card_congr e.mapSubgroup.toEquiv
    _ = Fintype.card (AddSubgroup (Fin a → ZMod p)) :=
      Fintype.card_congr AddSubgroup.toSubgroup.toEquiv.symm
    _ = Fintype.card (Submodule (ZMod p) (Fin a → ZMod p)) :=
      Fintype.card_congr (AddSubgroup.toZModSubmodule p).toEquiv
    _ = totalQBinom p a := by
      rw [Fintype.card_eq_nat_card]
      exact card_all_subspaces_fin_zmod p a

universe u v

/-- The quotient `(H₀ × E)/(H₀ × 1)` is canonically isomorphic to
`E`.  This makes the literal product family used for sharpness available
without suppressing the fixed first factor.-/
noncomputable def productTopBotQuotientEquiv (H₀ : Type u) (E : Type v)
    [Group H₀] [Group E] :
    ((H₀ × E) ⧸ ((⊤ : Subgroup H₀).prod (⊥ : Subgroup E))) ≃* E :=
  (QuotientGroup.prodMulEquiv (⊤ : Subgroup H₀) (⊥ : Subgroup E)).trans
    { toFun := fun q ↦ QuotientGroup.quotientBot q.2
      invFun := fun e ↦ (1, QuotientGroup.quotientBot.symm e)
      left_inv := by
        intro q
        apply Prod.ext
        · exact QuotientGroup.subsingleton_quotient_top.elim _ _
        · exact QuotientGroup.quotientBot.symm_apply_apply q.2
      right_inv := QuotientGroup.quotientBot.apply_symm_apply
      map_mul' := by
        intro x y
        exact QuotientGroup.quotientBot.map_mul x.2 y.2 }

/-- The literal inclusions `H₀ × 1 ≤ H₀ × E` attain the exact
prime-power interval bound when `E` is elementary abelian.-/
theorem product_elementaryAbelian_interval_card_eq
    (H₀ : Type u) [Group H₀] [Fintype H₀]
    (p a : ℕ) [Fact p.Prime] :
    Fintype.card
        (Set.Ici ((⊤ : Subgroup H₀).prod
          (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))))) =
      totalQBinom p a := by
  exact normal_elementaryAbelian_quotient_interval_card_eq
    ((⊤ : Subgroup H₀).prod
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))))
    (productTopBotQuotientEquiv H₀
      (Multiplicative (Fin a → ZMod p)))

/-- The index of the literal product inclusion is the order of its
elementary-abelian second factor.-/
theorem product_elementaryAbelian_index_eq
    (H₀ : Type u) [Group H₀] [Fintype H₀]
    (p a : ℕ) [Fact p.Prime] :
    ((⊤ : Subgroup H₀).prod
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))).index = p ^ a := by
  rw [Subgroup.index_prod]
  simp only [Subgroup.index_top, one_mul, Subgroup.index_bot]
  rw [Nat.card_eq_fintype_card]
  simpa using (Module.card_eq_pow_finrank (K := ZMod p)
    (V := Fin a → ZMod p))

/-- Index and exact interval count for the full fixed-factor product
sharpness family, packaged in one statement.-/
theorem product_elementaryAbelian_family
    (H₀ : Type u) [Group H₀] [Fintype H₀]
    (p a : ℕ) [Fact p.Prime] :
    ((⊤ : Subgroup H₀).prod
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))).index = p ^ a ∧
      Fintype.card
          (Set.Ici ((⊤ : Subgroup H₀).prod
            (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))))) =
        totalQBinom p a :=
  ⟨product_elementaryAbelian_index_eq H₀ p a,
    product_elementaryAbelian_interval_card_eq H₀ p a⟩

/-- The even-rank product family appearing in the asymptotic sharpness
statement of the manuscript.-/
theorem product_elementaryAbelian_even_interval_card_eq
    (H₀ : Type u) [Group H₀] [Fintype H₀]
    (p a : ℕ) [Fact p.Prime] :
    Fintype.card
        (Set.Ici ((⊤ : Subgroup H₀).prod
          (⊥ : Subgroup (Multiplicative (Fin (2 * a) → ZMod p))))) =
      totalQBinom p (2 * a) :=
  product_elementaryAbelian_interval_card_eq H₀ p (2 * a)

/-- Index and interval count for the even-rank family
`H₀ × 1 ≤ H₀ × C_p^{2a}`.-/
theorem product_elementaryAbelian_even_family
    (H₀ : Type u) [Group H₀] [Fintype H₀]
    (p a : ℕ) [Fact p.Prime] :
    ((⊤ : Subgroup H₀).prod
      (⊥ : Subgroup (Multiplicative (Fin (2 * a) → ZMod p)))).index =
        p ^ (2 * a) ∧
      Fintype.card
          (Set.Ici ((⊤ : Subgroup H₀).prod
            (⊥ : Subgroup (Multiplicative (Fin (2 * a) → ZMod p))))) =
        totalQBinom p (2 * a) :=
  product_elementaryAbelian_family H₀ p (2 * a)

/-- The fixed-layer Gaussian estimate packaged with its elementary-abelian
equality witness.-/
theorem primePower_layer_bound_optimal (p a k : ℕ) [Fact p.Prime]
    (hk : k ≤ a) :
    (∀ {G : Type*} [Group G] [Fintype G] (H : Subgroup G),
      H.index = p ^ a →
        (primePowerLayer p k H ⊤).card ≤ qBinom p a k) ∧
      (primePowerLayer p k
        (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ⊤).card =
        qBinom p a k := by
  constructor
  · intro G _ _ H hindex
    exact primePowerLayer_card_le Fact.out H hindex
  · exact elementaryAbelian_primePowerLayer_card_eq_qBinom p a k hk

/-- The exact prime-power theorem packaged as an optimality statement: the bound holds for
every finite inclusion of index `p ^ a`, and the elementary abelian inclusion attains it.-/
theorem primePower_interval_bound_optimal (p a : ℕ) [Fact p.Prime] :
    (∀ {G : Type*} [Group G] [Fintype G] (H : Subgroup G), H.index = p ^ a →
      Fintype.card (Set.Ici H) ≤ totalQBinom p a) ∧
    Fintype.card
        (Set.Ici (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))) = totalQBinom p a := by
  constructor
  · intro G _ _ H hindex
    exact intermediate_interval_card_le_totalQBinom Fact.out H hindex
  · exact elementaryAbelian_interval_card_eq_totalQBinom p a

end

end SharpIntermediateSubgroupBounds
