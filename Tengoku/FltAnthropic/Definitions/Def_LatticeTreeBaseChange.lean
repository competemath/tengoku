import Tengoku.FltAnthropic.Definitions.Def_LatticeTreeOrbital

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

attribute [local simp] IntegralAut.symm_toBase IntegralAut.symm_toField galVec_galVec_symm galVec_symm_galVec
  latticeGal_latticeGal_symm latticeGal_symm_latticeGal latticeMap_one mem_fixedVertexSet mem_stdLattice
  mem_twistedFixedVertexSet

section BaseChangeVocabulary

structure IntegralHom (R' K' R K : Type*) [CommRing R'] [Field K'] [Algebra R' K']
    [CommRing R] [Field K] [Algebra R K] where

  toField : K' →+* K

  toBase : R' →+* R

  commutes : ∀ r : R', toField (algebraMap R' K' r) = algebraMap R K (toBase r)

section BaseChange

variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ι : IntegralHom R' K' R K)

def vecMap (v : Fin 2 → K') : Fin 2 → K := fun i => ι.toField (v i)

/--
@isnad1 id=eq.0h7v.s7.49923cf19f56 from=translated src=- shape=e2c8f4c2 vocab=93e1aacb
-/
@[simp] theorem vecMap_apply (v : Fin 2 → K') (i : Fin 2) : vecMap ι v i = ι.toField (v i) := rfl

/--
@isnad1 id=eq.0h7v.s8.938e60bd1826 from=translated src=- shape=745b1ada vocab=73512f7d
-/
theorem vecMap_add (v w : Fin 2 → K') : vecMap ι (v + w) = vecMap ι v + vecMap ι w := by
  ext i; simp

/--
@isnad1 id=eq.0h5v.s7.fe3905cb03cf from=translated src=- shape=33ec09e6 vocab=ea9aa73a
-/
theorem vecMap_zero : vecMap ι (0 : Fin 2 → K') = 0 := by
  ext i; simp

/--
@isnad1 id=eq.0h7v.s8.abbbbeb993b7 from=translated src=- shape=2348ee60 vocab=06fccbca
-/
theorem vecMap_smul_field (c : K') (v : Fin 2 → K') : vecMap ι (c • v) = ι.toField c • vecMap ι v := by
  ext i; simp

/--
@isnad1 id=eq.0h7v.s8.8cfa338be478 from=translated src=- shape=db4b3fc6 vocab=38d6d8f6
-/
theorem vecMap_smul (r : R') (v : Fin 2 → K') : vecMap ι (r • v) = ι.toBase r • vecMap ι v := by
  ext i
  show ι.toField ((r • v) i) = (ι.toBase r • vecMap ι v) i
  rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul, ι.commutes,
    vecMap_apply]

/--
@isnad1 id=eq.0h7v.s8.bd86011fbc73 from=translated src=- shape=61d3851a vocab=5842aecc
-/
theorem vecMap_mulVec (M : Matrix (Fin 2) (Fin 2) K') (v : Fin 2 → K') :
    vecMap ι (M *ᵥ v) = M.map ι.toField *ᵥ vecMap ι v := by
  ext i
  exact RingHom.map_mulVec ι.toField M v i

/--
@isnad1 id=eq.0h6v.s7.f21011cd3954 from=translated src=- shape=d1d0448a vocab=90ab8002
-/
theorem vecMap_single_one (j : Fin 2) : vecMap ι (Pi.single j 1) = Pi.single j 1 := by
  ext i
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [Pi.single_eq_of_ne h]

abbrev IntegralHom.mapGL : Matrix.GeneralLinearGroup (Fin 2) K' →* Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.map ι.toField

/--
@isnad1 id=eq.0h6v.s9.719a64a4d7b4 from=translated src=- shape=375ecb99 vocab=8defbb00
-/
theorem IntegralHom.mapGL_coe (g : Matrix.GeneralLinearGroup (Fin 2) K') :
    ((ι.mapGL g : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (g : Matrix (Fin 2) (Fin 2) K').map ι.toField := by
  ext i j
  exact Matrix.GeneralLinearGroup.map_apply ι.toField i j g

/--
@isnad1 id=eq.0h6v.s9.032725f3576c from=translated src=- shape=8ed03118 vocab=f5a8db85
-/
theorem IntegralHom.mapGL_scalarGL (c : K'ˣ) :
    ι.mapGL (scalarGL c) = scalarGL (Units.map (ι.toField : K' →* K) c) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, scalarGL_coe, scalarGL_coe, Matrix.smul_apply,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, Units.coe_map, MonoidHom.coe_coe]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply, apply_ite ι.toField, map_one, map_zero]

def latticeBaseChange (L' : Submodule R' (Fin 2 → K')) : Submodule R (Fin 2 → K) :=
  Submodule.span R (vecMap ι '' (L' : Set (Fin 2 → K')))

/--
@isnad1 id=mem.1h7v.s9.1b46762b3c54 from=translated src=- shape=bb6b3a0c vocab=2d929209
-/
theorem vecMap_mem_latticeBaseChange {L' : Submodule R' (Fin 2 → K')} {v : Fin 2 → K'}
    (hv : v ∈ L') : vecMap ι v ∈ latticeBaseChange ι L' :=
  Submodule.subset_span ⟨v, hv, rfl⟩

/--
@isnad1 id=eq.0h6v.s8.ef36412028e6 from=translated src=- shape=ba6ed2a9 vocab=611f9858
-/
theorem latticeBaseChange_span (s : Set (Fin 2 → K')) :
    latticeBaseChange ι (Submodule.span R' s) = Submodule.span R (vecMap ι '' s) := by
  apply le_antisymm
  · rw [latticeBaseChange, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    induction hw using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [vecMap_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [vecMap_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [vecMap_smul]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/--
@isnad1 id=eq.0h7v.s9.0422285b1e2f from=translated src=- shape=256e9993 vocab=03e2963d
-/
theorem latticeBaseChange_latticeMap (g : Matrix.GeneralLinearGroup (Fin 2) K')
    (L' : Submodule R' (Fin 2 → K')) :
    latticeBaseChange ι (latticeMap g L') = latticeMap (ι.mapGL g) (latticeBaseChange ι L') := by
  have himg : vecMap ι '' (latticeMap g L' : Set (Fin 2 → K'))
      = mulVecLinR (R := R) (ι.mapGL g) '' (vecMap ι '' (L' : Set (Fin 2 → K'))) := by
    ext v
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨vecMap ι w, ⟨w, hw, rfl⟩, ?_⟩
      rw [mulVecLinR_apply, IntegralHom.mapGL_coe, ← vecMap_mulVec]
      rfl
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨(g : Matrix (Fin 2) (Fin 2) K') *ᵥ w, mulVec_mem_latticeMap hw, ?_⟩
      rw [mulVecLinR_apply, IntegralHom.mapGL_coe, ← vecMap_mulVec]
  rw [latticeBaseChange, himg, ← Submodule.map_span]
  rfl

/--
@isnad1 id=eq.0h7v.s9.8d41b36e3233 from=translated src=- shape=3e8ca205 vocab=db9dae06
-/
theorem latticeBaseChange_scalarGL (c : K'ˣ) (L' : Submodule R' (Fin 2 → K')) :
    latticeBaseChange ι (latticeMap (scalarGL c) L')
      = latticeMap (scalarGL (Units.map (ι.toField : K' →* K) c)) (latticeBaseChange ι L') := by
  rw [latticeBaseChange_latticeMap, IntegralHom.mapGL_scalarGL]

/--
@isnad1 id=isfullla.1h6v.s7.bd54e0beaa29 from=translated src=- shape=46fcb995 vocab=de7304a6
-/
theorem IsFullLattice.baseChange {L' : Submodule R' (Fin 2 → K')} (hL' : IsFullLattice L') :
    IsFullLattice (latticeBaseChange ι L') := by
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs⟩ := hL'.1
    rw [← hs, latticeBaseChange_span]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · rw [eq_top_iff]
    intro v _
    have hbasis : ∀ j : Fin 2, (Pi.single j 1 : Fin 2 → K)
        ∈ Submodule.span K ((latticeBaseChange ι L' : Set (Fin 2 → K))) := by
      intro j
      have key : ∀ x ∈ Submodule.span K' ((L' : Set (Fin 2 → K'))),
          vecMap ι x ∈ Submodule.span K ((latticeBaseChange ι L' : Set (Fin 2 → K))) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx => exact Submodule.subset_span (vecMap_mem_latticeBaseChange ι hx)
        | zero => rw [vecMap_zero]; exact Submodule.zero_mem _
        | add x y _ _ hx hy => rw [vecMap_add]; exact Submodule.add_mem _ hx hy
        | smul c x _ hx => rw [vecMap_smul_field]; exact Submodule.smul_mem _ _ hx
      rw [← vecMap_single_one ι j]
      exact key _ (hL'.2 ▸ Submodule.mem_top)
    have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → K) + v 1 • (Pi.single 1 1 : Fin 2 → K) := by
      ext i
      fin_cases i <;> simp
    rw [hv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hbasis 0)) (Submodule.smul_mem _ _ (hbasis 1))

def Vertex.baseChange : Vertex R' K' → Vertex R K :=
  Quotient.map (fun L => ⟨latticeBaseChange ι L.1, L.2.baseChange ι⟩)
    (by
      rintro ⟨L, hL⟩ ⟨L', hL'⟩ ⟨c, hc⟩
      refine ⟨Units.map (ι.toField : K' →* K) c, ?_⟩
      show latticeMap _ (latticeBaseChange ι L) = latticeBaseChange ι L'
      rw [← latticeBaseChange_scalarGL, hc])

/--
@isnad1 id=eq.1h6v.s7.ea83ee065471 from=translated src=- shape=b01a8752 vocab=716c062e
-/
@[simp] theorem Vertex.baseChange_mk (L' : Submodule R' (Fin 2 → K')) (hL' : IsFullLattice L') :
    Vertex.baseChange ι (Vertex.mk R' K' L' hL')
      = Vertex.mk R K (latticeBaseChange ι L') (hL'.baseChange ι) :=
  rfl

/--
@isnad1 id=eq.0h7v.s9.3671719e77da from=translated src=- shape=f62b39f9 vocab=c989d4c7
-/
theorem Vertex.baseChange_act (g : Matrix.GeneralLinearGroup (Fin 2) K') (v : Vertex R' K') :
    Vertex.baseChange ι (Vertex.act g v) = Vertex.act (ι.mapGL g) (Vertex.baseChange ι v) := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeBaseChange_latticeMap ι g L.1))

/--
@isnad1 id=le.0h5v.s8.7d19b6bdc768 from=translated src=- shape=3f8b3425 vocab=afaf63d1
-/
theorem latticeBaseChange_stdLattice_le : latticeBaseChange ι (stdLattice R' K') ≤ stdLattice R K := by
  rw [latticeBaseChange, Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩ i
  obtain ⟨r, hr⟩ := hw i
  exact ⟨ι.toBase r, by rw [vecMap_apply, ← hr, ι.commutes]⟩

/--
@isnad1 id=isfixedv.1h7v.s9.a7197bbf1e9e from=translated src=- shape=b0f4d253 vocab=0a04b95c
-/
theorem IsFixedVertex.baseChange {g : Matrix.GeneralLinearGroup (Fin 2) K'} {v : Vertex R' K'}
    (hv : IsFixedVertex g v) : IsFixedVertex (ι.mapGL g) (Vertex.baseChange ι v) := by
  rw [IsFixedVertex, ← Vertex.baseChange_act, hv]

/--
@isnad1 id=le.0h6v.s9.df9fd892db9d from=translated src=- shape=0139af8a vocab=d05b9602
-/
theorem baseChange_image_fixedVertexSet_subset (g : Matrix.GeneralLinearGroup (Fin 2) K') :
    Vertex.baseChange ι '' fixedVertexSet (R := R') g ⊆ fixedVertexSet (R := R) (ι.mapGL g) := by
  rintro _ ⟨v, hv, rfl⟩
  exact IsFixedVertex.baseChange ι hv

/--
@isnad1 id=isfixedv.1h5v.s9.0619fce2f88b from=translated src=- shape=d1c095ad vocab=04972118
-/
theorem act_mem_fixedVertexSet_conj {g P : Matrix.GeneralLinearGroup (Fin 2) K} {v : Vertex R K}
    (hv : IsFixedVertex g v) : IsFixedVertex (P * g * P⁻¹) (Vertex.act P v) := by
  rw [IsFixedVertex, ← Vertex.act_mul, inv_mul_cancel_right, Vertex.act_mul, hv]

/--
@isnad1 id=le.1h8v.s10.75287ddb4eea from=translated src=- shape=8c97a84e vocab=0b2bc5c4
-/
theorem act_baseChange_fixed_subset_of_conj_eq {N P : Matrix.GeneralLinearGroup (Fin 2) K}
    {γ : Matrix.GeneralLinearGroup (Fin 2) K'} (hP : P⁻¹ * N * P = ι.mapGL γ) :
    Vertex.act P '' (Vertex.baseChange ι '' fixedVertexSet (R := R') γ)
      ⊆ fixedVertexSet (R := R) N := by
  rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  have h := act_mem_fixedVertexSet_conj (P := P) (IsFixedVertex.baseChange ι hv)
  rwa [← hP, show P * (P⁻¹ * N * P) * P⁻¹ = N by group] at h

/--
@isnad1 id=eq.1h7v.s9.f1fe20cfbc0d from=translated src=- shape=73fade18 vocab=fd87d684
-/
theorem latticeGal_latticeBaseChange {σ : IntegralAut R K}
    (hσ : ∀ x : K', σ.toField (ι.toField x) = ι.toField x) (L' : Submodule R' (Fin 2 → K')) :
    latticeGal σ (latticeBaseChange ι L') = latticeBaseChange ι L' := by
  have hfix : galVec σ '' (vecMap ι '' (L' : Set (Fin 2 → K'))) = vecMap ι '' (L' : Set (Fin 2 → K')) := by
    have hpt : ∀ w : Fin 2 → K', galVec σ (vecMap ι w) = vecMap ι w := fun w => by
      ext i; simp [hσ]
    ext v
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, (hpt w).symm⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨vecMap ι w, ⟨w, hw, rfl⟩, hpt w⟩
  rw [latticeBaseChange, latticeGal_span, hfix]

/--
@isnad1 id=eq.1h7v.s8.ccf827bc791e from=translated src=- shape=7e20725a vocab=1a454d6a
-/
theorem Vertex.galAct_baseChange {σ : IntegralAut R K}
    (hσ : ∀ x : K', σ.toField (ι.toField x) = ι.toField x) (v : Vertex R' K') :
    Vertex.galAct σ (Vertex.baseChange ι v) = Vertex.baseChange ι v := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeGal_latticeBaseChange ι hσ L.1))

/--
@isnad1 id=eq.1h8v.s8.cdb3ebf71089 from=translated src=- shape=4a699ce2 vocab=fa54142f
-/
theorem Vertex.twistedAct_baseChange {σ : IntegralAut R K}
    (hσ : ∀ x : K', σ.toField (ι.toField x) = ι.toField x)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R' K') :
    Vertex.twistedAct g σ (Vertex.baseChange ι v) = Vertex.act g (Vertex.baseChange ι v) := by
  rw [Vertex.twistedAct, Vertex.galAct_baseChange ι hσ]

end BaseChange

section Inhabitants

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

variable (R K) in

def IntegralHom.refl : IntegralHom R K R K where
  toField := RingHom.id K
  toBase := RingHom.id R
  commutes _ := rfl

def IntegralAut.toIntegralHom (σ : IntegralAut R K) : IntegralHom R K R K where
  toField := σ.toField
  toBase := σ.toBase
  commutes := σ.commutes

/--
@isnad1 id=eq.0h3v.s5.7436f8f11dcb from=translated src=- shape=f1eb9481 vocab=b4152010
-/
@[simp] theorem vecMap_refl (v : Fin 2 → K) : vecMap (IntegralHom.refl R K) v = v := rfl

/--
@isnad1 id=eq.0h3v.s7.27b6e99f4cab from=translated src=- shape=c521d9b5 vocab=f5720ce5
-/
theorem latticeBaseChange_refl (L : Submodule R (Fin 2 → K)) :
    latticeBaseChange (IntegralHom.refl R K) L = L := by
  have h : vecMap (IntegralHom.refl R K) '' (L : Set (Fin 2 → K)) = L := by
    ext v; simp
  rw [latticeBaseChange, h, Submodule.span_eq]

/--
@isnad1 id=eq.0h3v.s5.45b8f9704c56 from=translated src=- shape=3f905053 vocab=aa3be460
-/
theorem Vertex.baseChange_refl (v : Vertex R K) : Vertex.baseChange (IntegralHom.refl R K) v = v := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeBaseChange_refl L.1))

/--
@isnad1 id=nonempty.0h2v.s4.278464a8eea1 from=translated src=- shape=ba4e7e14 vocab=251a9b0d
-/
theorem nonempty_vertex : Nonempty (Vertex R K) := ⟨stdVertex R K⟩

end Inhabitants

section Monotone

variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ι : IntegralHom R' K' R K)

/--
@isnad1 id=le.1h7v.s9.72d6aac59b1b from=translated src=- shape=37090a2c vocab=b32f591a
-/
theorem latticeBaseChange_mono {L₁ L₂ : Submodule R' (Fin 2 → K')} (h : L₁ ≤ L₂) :
    latticeBaseChange ι L₁ ≤ latticeBaseChange ι L₂ :=
  Submodule.span_mono (Set.image_mono h)

/--
@isnad1 id=le.1h5v.s9.0bb8e218e19b from=translated src=- shape=db380b7b vocab=f59d5d5b
-/
theorem latticeGal_mono (σ : IntegralAut R K) {L₁ L₂ : Submodule R (Fin 2 → K)} (h : L₁ ≤ L₂) :
    latticeGal σ L₁ ≤ latticeGal σ L₂ := by
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w, h hw, rfl⟩

end Monotone

section DepthCurrency

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

def LatticeWithin (c : Kˣ) (n : ℕ) (L M : Submodule R (Fin 2 → K)) : Prop :=
  latticeMap (scalarGL (c ^ n)) L ≤ M ∧ M ≤ L

def Vertex.IsWithin (c : Kˣ) (n : ℕ) (v w : Vertex R K) : Prop :=
  ∃ (L M : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) (hM : IsFullLattice M),
    Vertex.mk R K L hL = v ∧ Vertex.mk R K M hM = w ∧ LatticeWithin c n L M

/--
@isnad1 id=iff.0h5v.s8.1cf270bcaceb from=translated src=- shape=82d5765b vocab=946ddbb5
-/
theorem latticeWithin_zero_iff (c : Kˣ) (L M : Submodule R (Fin 2 → K)) :
    LatticeWithin c 0 L M ↔ M = L := by
  simp only [LatticeWithin, pow_zero, scalarGL_one, latticeMap_one]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

/--
@isnad1 id=iff.0h5v.s6.b6029c493703 from=translated src=- shape=0d09bc6f vocab=74d10ae8
-/
theorem Vertex.isWithin_zero_iff (c : Kˣ) (v w : Vertex R K) : Vertex.IsWithin c 0 v w ↔ v = w := by
  constructor
  · rintro ⟨L, M, hL, hM, rfl, rfl, h⟩
    rw [latticeWithin_zero_iff] at h
    subst h
    rfl
  · rintro rfl
    induction v using Quotient.inductionOn with
    | h L => exact ⟨L.1, L.1, L.2, L.2, rfl, rfl, (latticeWithin_zero_iff c _ _).mpr rfl⟩

/--
@isnad1 id=latticew.1h6v.s8.e2474c5235ce from=translated src=- shape=29975351 vocab=f80d9057
-/
theorem LatticeWithin.symm_rescale {c : Kˣ} {n : ℕ} {L M : Submodule R (Fin 2 → K)}
    (h : LatticeWithin c n L M) :
    LatticeWithin c n (latticeMap (scalarGL (c ^ n))⁻¹ M) L := by
  obtain ⟨hlow, hup⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← latticeMap_mul, mul_inv_cancel, latticeMap_one]
    exact hup
  · have := latticeMap_mono (scalarGL (c ^ n))⁻¹ hlow
    rwa [latticeMap_inv_latticeMap] at this

/--
@isnad1 id=iswithin.1h6v.s6.bbc7e7007bef from=translated src=- shape=a7e32335 vocab=74d10ae8
-/
theorem Vertex.IsWithin.symm {c : Kˣ} {n : ℕ} {v w : Vertex R K} (h : Vertex.IsWithin c n v w) :
    Vertex.IsWithin c n w v := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h
  refine ⟨latticeMap (scalarGL (c ^ n))⁻¹ M, L, hM.map _, hL, ?_, rfl, hLM.symm_rescale⟩
  rw [Vertex.mk_eq_mk_iff]
  exact ⟨c ^ n, by rw [← latticeMap_mul, mul_inv_cancel, latticeMap_one]⟩

/--
@isnad1 id=iff.0h6v.s6.f9d05c4ee8c5 from=translated src=- shape=dc6d6493 vocab=74d10ae8
-/
theorem Vertex.isWithin_comm (c : Kˣ) (n : ℕ) (v w : Vertex R K) :
    Vertex.IsWithin c n v w ↔ Vertex.IsWithin c n w v :=
  ⟨Vertex.IsWithin.symm, Vertex.IsWithin.symm⟩

/--
@isnad1 id=le.1h5v.s9.6108a0f7101e from=translated src=- shape=7f265d33 vocab=b7e40f4e
-/
theorem latticeMap_scalarGL_pow_le_of_le {c : Kˣ}
    (hc : ∀ L : Submodule R (Fin 2 → K), latticeMap (scalarGL c) L ≤ L) (k : ℕ) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (c ^ k)) L ≤ L := by
  induction k with
  | zero => rw [pow_zero, scalarGL_one, latticeMap_one]
  | succ k ih =>
      rw [pow_succ, scalarGL_mul, latticeMap_mul]
      exact le_trans (latticeMap_mono _ (hc L)) ih

/--
@isnad1 id=latticew.3h7v.s9.8742eed4a24c from=translated src=- shape=978615e1 vocab=b8463c61
-/
theorem LatticeWithin.mono {c : Kˣ} (hc : ∀ L : Submodule R (Fin 2 → K), latticeMap (scalarGL c) L ≤ L)
    {m n : ℕ} (hmn : m ≤ n) {L M : Submodule R (Fin 2 → K)} (h : LatticeWithin c m L M) :
    LatticeWithin c n L M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine ⟨le_trans ?_ h.1, h.2⟩
  rw [pow_add, scalarGL_mul, latticeMap_mul]
  exact latticeMap_mono _ (latticeMap_scalarGL_pow_le_of_le hc k L)

/--
@isnad1 id=iswithin.3h7v.s9.79adad399fc2 from=translated src=- shape=fc26d934 vocab=1bf7ca6f
-/
theorem Vertex.IsWithin.mono {c : Kˣ} (hc : ∀ L : Submodule R (Fin 2 → K), latticeMap (scalarGL c) L ≤ L)
    {m n : ℕ} (hmn : m ≤ n) {v w : Vertex R K} (h : Vertex.IsWithin c m v w) : Vertex.IsWithin c n v w := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h
  exact ⟨L, M, hL, hM, rfl, rfl, hLM.mono hc hmn⟩

/--
@isnad1 id=iff.0h7v.s8.16b3c91eb970 from=translated src=- shape=a695c7bc vocab=72fafd1f
-/
theorem latticeWithin_latticeMap_iff (c : Kˣ) (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L M : Submodule R (Fin 2 → K)) :
    LatticeWithin c n (latticeMap g L) (latticeMap g M) ↔ LatticeWithin c n L M := by
  unfold LatticeWithin
  rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · simpa only [latticeMap_inv_latticeMap] using latticeMap_mono g⁻¹ h1
    · simpa only [latticeMap_inv_latticeMap] using latticeMap_mono g⁻¹ h2
  · rintro ⟨h1, h2⟩
    exact ⟨latticeMap_mono g h1, latticeMap_mono g h2⟩

/--
@isnad1 id=iff.0h7v.s7.c71ac8079cf2 from=translated src=- shape=528da247 vocab=5a7d379b
-/
theorem latticeWithin_latticeGal_iff (σ : IntegralAut R K) (c : Kˣ) (n : ℕ) (L M : Submodule R (Fin 2 → K)) :
    LatticeWithin (σ.unitMap c) n (latticeGal σ L) (latticeGal σ M) ↔ LatticeWithin c n L M := by
  have hpow : σ.unitMap c ^ n = σ.unitMap (c ^ n) := by
    ext
    simp only [Units.val_pow_eq_pow_val, IntegralAut.unitMap_coe, map_pow]
  unfold LatticeWithin
  rw [hpow, ← latticeGal_scalarGL]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · simpa only [latticeGal_symm_latticeGal] using latticeGal_mono σ.symm h1
    · simpa only [latticeGal_symm_latticeGal] using latticeGal_mono σ.symm h2
  · rintro ⟨h1, h2⟩
    exact ⟨latticeGal_mono σ h1, latticeGal_mono σ h2⟩

end DepthCurrency

section DepthBaseChange

variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ι : IntegralHom R' K' R K)

/--
@isnad1 id=latticew.1h9v.s9.1799cf29e2ca from=translated src=- shape=045595f5 vocab=63aa8447
-/
theorem LatticeWithin.baseChange {c : K'ˣ} {n : ℕ} {L M : Submodule R' (Fin 2 → K')}
    (h : LatticeWithin c n L M) :
    LatticeWithin (Units.map (ι.toField : K' →* K) c) n (latticeBaseChange ι L) (latticeBaseChange ι M) := by
  refine ⟨?_, latticeBaseChange_mono ι h.2⟩
  have := latticeBaseChange_mono ι h.1
  rwa [latticeBaseChange_scalarGL, map_pow] at this

/--
@isnad1 id=iswithin.1h9v.s8.11404764c426 from=translated src=- shape=e1c94268 vocab=3a0cf0f4
-/
theorem Vertex.IsWithin.baseChange {c : K'ˣ} {n : ℕ} {v w : Vertex R' K'} (h : Vertex.IsWithin c n v w) :
    Vertex.IsWithin (Units.map (ι.toField : K' →* K) c) n
      (Vertex.baseChange ι v) (Vertex.baseChange ι w) := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h
  exact ⟨latticeBaseChange ι L, latticeBaseChange ι M, hL.baseChange ι, hM.baseChange ι, rfl, rfl,
    hLM.baseChange ι⟩

end DepthBaseChange

section DepthOrbital

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

def orbitalBall (c : Kˣ) (n : ℕ) (γ : Matrix.GeneralLinearGroup (Fin 2) K) : Set (Vertex R K) :=
  {x | Vertex.IsWithin c n x (Vertex.act γ x)}

def twistedOrbitalBall (c : Kˣ) (n : ℕ) (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    Set (Vertex R K) :=
  {x | Vertex.IsWithin c n x (Vertex.twistedAct δ σ x)}

/--
@isnad1 id=iff.0h6v.s6.421cceaaf9fd from=translated src=- shape=a160eb6c vocab=0d53d2ed
-/
theorem mem_orbitalBall {c : Kˣ} {n : ℕ} {γ : Matrix.GeneralLinearGroup (Fin 2) K}
    {x : Vertex R K} : x ∈ orbitalBall (R := R) c n γ ↔ Vertex.IsWithin c n x (Vertex.act γ x) :=
  Iff.rfl

/--
@isnad1 id=iff.0h7v.s7.e6b29889af67 from=translated src=- shape=b67de997 vocab=415efbaa
-/
theorem mem_twistedOrbitalBall {c : Kˣ} {n : ℕ} {δ : Matrix.GeneralLinearGroup (Fin 2) K}
    {σ : IntegralAut R K} {x : Vertex R K} :
    x ∈ twistedOrbitalBall c n δ σ ↔ Vertex.IsWithin c n x (Vertex.twistedAct δ σ x) :=
  Iff.rfl

attribute [local simp] mem_orbitalBall mem_twistedOrbitalBall

/--
@isnad1 id=eq.0h4v.s6.1d2d8a2f01db from=translated src=- shape=4f3b7b64 vocab=f79039b5
-/
theorem orbitalBall_zero (c : Kˣ) (γ : Matrix.GeneralLinearGroup (Fin 2) K) :
    orbitalBall (R := R) c 0 γ = fixedVertexSet γ := by
  ext x
  rw [mem_orbitalBall, Vertex.isWithin_zero_iff, mem_fixedVertexSet, eq_comm]

/--
@isnad1 id=eq.0h5v.s6.aa6cd47189a3 from=translated src=- shape=43826148 vocab=b98a50b4
-/
theorem twistedOrbitalBall_zero (c : Kˣ) (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    twistedOrbitalBall c 0 δ σ = twistedFixedVertexSet δ σ := by
  ext x
  rw [mem_twistedOrbitalBall, Vertex.isWithin_zero_iff, mem_twistedFixedVertexSet, eq_comm]

/--
@isnad1 id=eq.0h5v.s6.56b5648eb6d5 from=translated src=- shape=3ee91ff7 vocab=8d099582
-/
theorem twistedOrbitalBall_refl (c : Kˣ) (n : ℕ) (δ : Matrix.GeneralLinearGroup (Fin 2) K) :
    twistedOrbitalBall c n δ (IntegralAut.refl R K) = orbitalBall c n δ := by
  ext x
  rw [mem_twistedOrbitalBall, mem_orbitalBall, Vertex.twistedAct, Vertex.galAct_refl]

/--
@isnad1 id=eq.1h4v.s9.587f41280e33 from=translated src=- shape=ef56472b vocab=d1ced076
-/
theorem orbitalBall_one {c : Kˣ} (hc : ∀ L : Submodule R (Fin 2 → K), latticeMap (scalarGL c) L ≤ L)
    (n : ℕ) : orbitalBall (R := R) c n 1 = Set.univ := by
  ext x
  simp only [mem_orbitalBall, Vertex.act_one, Set.mem_univ, iff_true]
  exact ((Vertex.isWithin_zero_iff c x x).mpr rfl).mono hc (Nat.zero_le n)

end DepthOrbital

end BaseChangeVocabulary

end LT.LatticeTree
