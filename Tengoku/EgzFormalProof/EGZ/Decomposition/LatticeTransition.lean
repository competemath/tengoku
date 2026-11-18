import Tengoku.EgzFormalProof.EGZ.Decomposition.MinimalLattice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transition maps in support-generated lattice coordinates

An affine map taking the source generators into the target generated lattice
factors uniquely through their integer coordinate charts.  Uniqueness then
supplies the identity and composition laws for recharted flag transitions.
-/

namespace EGZ.IntegerLatticeChart

variable {m n k : ℕ} {S : Finset (IntCoord m)} {T : Finset (IntCoord n)}

/-- An affine map into a chart's generated lattice has a unique affine lift
to the chart coordinates.
@isnad1 id=existsun.1h5v.s9.36c19c8a7f4c from=translated src=- shape=1c7f4148 vocab=e8ff6ea6
-/
theorem existsUnique_lift (C : IntegerLatticeChart T)
    (g : IntCoord k →ᵃ[ℤ] IntCoord n)
    (hg : ∀ q, g q ∈ affineSpan ℤ (T : Set (IntCoord n))) :
    ∃! B : IntCoord k →ᵃ[ℤ] IntCoord C.rank, C.map.comp B = g := by
  obtain ⟨b, hb⟩ := C.range_eq.symm.subset (hg 0)
  have hlin : ∀ q, g.linear q ∈ LinearMap.range C.map.linear := by
    intro q
    rw [C.linear_range_eq, ← direction_affineSpan]
    have h := (affineSpan ℤ (T : Set (IntCoord n))).vsub_mem_direction (hg q) (hg 0)
    simpa only [← g.linearMap_vsub, vsub_eq_sub, sub_zero] using h
  let E := LinearEquiv.ofInjective C.map.linear (C.map.linear_injective_iff.mpr C.injective)
  let L : IntCoord k →ₗ[ℤ] IntCoord C.rank :=
    E.symm.toLinearMap.comp (g.linear.codRestrict (LinearMap.range C.map.linear) hlin)
  have hL (q : IntCoord k) : C.map.linear (L q) = g.linear q := by
    exact LinearEquiv.ofInjective_symm_apply C.map.linear
      (h := C.map.linear_injective_iff.mpr C.injective) ⟨g.linear q, hlin q⟩
  let B : IntCoord k →ᵃ[ℤ] IntCoord C.rank :=
    (AffineEquiv.vaddConst ℤ b).toAffineMap.comp L.toAffineMap
  have hB : C.map.comp B = g := by
    apply AffineMap.ext
    intro q
    change C.map (L q +ᵥ b) = g q
    rw [C.map.map_vadd, hL, hb]
    simpa only [vadd_eq_add, add_zero] using (g.map_vadd 0 q).symm
  refine ⟨B, hB, ?_⟩
  intro B' hB'
  apply AffineMap.ext
  intro q
  apply C.injective
  exact (AffineMap.congr_fun hB' q).trans (AffineMap.congr_fun hB q).symm

/-- The canonical lift is characterized by composition with the chart map.-/
noncomputable def lift (C : IntegerLatticeChart T)
    (g : IntCoord k →ᵃ[ℤ] IntCoord n)
    (hg : ∀ q, g q ∈ affineSpan ℤ (T : Set (IntCoord n))) :
    IntCoord k →ᵃ[ℤ] IntCoord C.rank :=
  Classical.choose (C.existsUnique_lift g hg)

/--
@isnad1 id=eq.1h5v.s9.47667c572867 from=translated src=- shape=742a54ca vocab=917702c1
-/
@[simp]
theorem map_comp_lift (C : IntegerLatticeChart T)
    (g : IntCoord k →ᵃ[ℤ] IntCoord n)
    (hg : ∀ q, g q ∈ affineSpan ℤ (T : Set (IntCoord n))) :
    C.map.comp (C.lift g hg) = g :=
  (Classical.choose_spec (C.existsUnique_lift g hg)).1

/--
@isnad1 id=eq.2h6v.s9.e8e6799a4370 from=translated src=- shape=5de1efb9 vocab=917702c1
-/
theorem lift_unique (C : IntegerLatticeChart T)
    (g : IntCoord k →ᵃ[ℤ] IntCoord n)
    (hg : ∀ q, g q ∈ affineSpan ℤ (T : Set (IntCoord n)))
    (B : IntCoord k →ᵃ[ℤ] IntCoord C.rank) (hB : C.map.comp B = g) :
    B = C.lift g hg :=
  (Classical.choose_spec (C.existsUnique_lift g hg)).2 B hB

/-- It suffices to check membership in the target generated lattice on the
source generators.
@isnad1 id=mem.1h7v.s10.1fc57738e085 from=translated src=- shape=799c5a4d vocab=74427dc4
-/
theorem map_chart_mem_affineSpan (C : IntegerLatticeChart S)
    (A : IntCoord m →ᵃ[ℤ] IntCoord n)
    (hA : ∀ z ∈ S, A z ∈ affineSpan ℤ (T : Set (IntCoord n)))
    (q : IntCoord C.rank) :
    A (C.map q) ∈ affineSpan ℤ (T : Set (IntCoord n)) := by
  have hspan : affineSpan ℤ (S : Set (IntCoord m)) ≤
      (affineSpan ℤ (T : Set (IntCoord n))).comap A := affineSpan_le.mpr hA
  apply hspan
  exact C.range_eq.subset ⟨q, rfl⟩

/-- Express an ambient affine transition in the support-generated coordinates.-/
noncomputable def transition (C : IntegerLatticeChart S) (D : IntegerLatticeChart T)
    (A : IntCoord m →ᵃ[ℤ] IntCoord n)
    (hA : ∀ z ∈ S, A z ∈ affineSpan ℤ (T : Set (IntCoord n))) :
    IntCoord C.rank →ᵃ[ℤ] IntCoord D.rank :=
  D.lift (A.comp C.map) (C.map_chart_mem_affineSpan A hA)

/--
@isnad1 id=eq.1h7v.s9.e2784d0bfeec from=translated src=- shape=a2c46529 vocab=8a97c4f0
-/
@[simp]
theorem map_comp_transition (C : IntegerLatticeChart S) (D : IntegerLatticeChart T)
    (A : IntCoord m →ᵃ[ℤ] IntCoord n)
    (hA : ∀ z ∈ S, A z ∈ affineSpan ℤ (T : Set (IntCoord n))) :
    D.map.comp (C.transition D A hA) = A.comp C.map :=
  D.map_comp_lift _ _

/--
@isnad1 id=eq.1h8v.s10.dadc86c7f245 from=translated src=- shape=9ae766a8 vocab=4cd3ed91
-/
@[simp]
theorem map_transition (C : IntegerLatticeChart S) (D : IntegerLatticeChart T)
    (A : IntCoord m →ᵃ[ℤ] IntCoord n)
    (hA : ∀ z ∈ S, A z ∈ affineSpan ℤ (T : Set (IntCoord n)))
    (q : IntCoord C.rank) :
    D.map (C.transition D A hA q) = A (C.map q) :=
  AffineMap.congr_fun (C.map_comp_transition D A hA) q

/--
@isnad1 id=eq.2h8v.s10.aa00b707cdba from=translated src=- shape=a758b330 vocab=8a97c4f0
-/
theorem transition_unique (C : IntegerLatticeChart S) (D : IntegerLatticeChart T)
    (A : IntCoord m →ᵃ[ℤ] IntCoord n)
    (hA : ∀ z ∈ S, A z ∈ affineSpan ℤ (T : Set (IntCoord n)))
    (B : IntCoord C.rank →ᵃ[ℤ] IntCoord D.rank)
    (hB : D.map.comp B = A.comp C.map) : B = C.transition D A hA :=
  D.lift_unique _ _ B hB

/-- Recharting the identity transition gives the identity map.
@isnad1 id=eq.1h3v.s9.ce9038c27775 from=translated src=- shape=35f6261a vocab=91a3d4ee
-/
@[simp]
theorem transition_id (C : IntegerLatticeChart S)
    (h : ∀ z ∈ S, (AffineMap.id ℤ (IntCoord m)) z ∈
      affineSpan ℤ (S : Set (IntCoord m))) :
    C.transition C (AffineMap.id ℤ (IntCoord m)) h =
      AffineMap.id ℤ (IntCoord C.rank) := by
  symm
  apply C.transition_unique C
  simp

/-- Uniqueness gives the cocycle law for consecutive recharted transitions.
@isnad1 id=eq.3h11v.s10.a6671e94ccbb from=translated src=- shape=e08737d0 vocab=f116b564
-/
theorem transition_comp {r : ℕ} {U : Finset (IntCoord r)}
    (C : IntegerLatticeChart S) (D : IntegerLatticeChart T) (E : IntegerLatticeChart U)
    (A : IntCoord m →ᵃ[ℤ] IntCoord n) (B : IntCoord n →ᵃ[ℤ] IntCoord r)
    (hA : ∀ z ∈ S, A z ∈ affineSpan ℤ (T : Set (IntCoord n)))
    (hB : ∀ z ∈ T, B z ∈ affineSpan ℤ (U : Set (IntCoord r)))
    (hBA : ∀ z ∈ S, (B.comp A) z ∈ affineSpan ℤ (U : Set (IntCoord r))) :
    C.transition E (B.comp A) hBA =
      (D.transition E B hB).comp (C.transition D A hA) := by
  symm
  apply C.transition_unique E
  rw [← AffineMap.comp_assoc, D.map_comp_transition E B hB,
    AffineMap.comp_assoc, C.map_comp_transition D A hA, AffineMap.comp_assoc]

end EGZ.IntegerLatticeChart
