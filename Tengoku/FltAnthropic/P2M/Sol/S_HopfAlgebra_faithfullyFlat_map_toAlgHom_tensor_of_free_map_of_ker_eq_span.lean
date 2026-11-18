import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

open scoped TensorProduct

universe u v

namespace S17Torsor

variable {k : Type u} [CommRing k] {H : Type v} [CommRing H] [HopfAlgebra k H]
variable (K : Subalgebra k H)

def J : Ideal H := Ideal.span {x : H | x ∈ K ∧ Coalgebra.counit (R := k) x = 0}

abbrev Q : Type v := H ⧸ J K

def π : H →ₐ[k] Q K := Ideal.Quotient.mkₐ k (J K)

/--
@isnad1 id=eq.1h4v.s9.ac3316de5e7f from=translated src=- shape=ccb05c07 vocab=fc125d09
-/
theorem π_eq_algebraMap_counit_of_mem {x : H} (hx : x ∈ K) :
    π K x = algebraMap k (Q K) (Coalgebra.counit (R := k) x) := by
  have hmem : x - algebraMap k H (Coalgebra.counit (R := k) x) ∈ J K := by
    apply Ideal.subset_span
    refine ⟨K.sub_mem hx (K.algebraMap_mem _), ?_⟩
    rw [map_sub, Bialgebra.counit_algebraMap]; simp
  have := (Ideal.Quotient.mkₐ_eq_mk k (J K)) ▸ (Ideal.Quotient.eq.mpr hmem : Ideal.Quotient.mk (J K) x = Ideal.Quotient.mk (J K) _)
  rw [π]
  show Ideal.Quotient.mkₐ k (J K) x = _
  rw [Ideal.Quotient.mkₐ_eq_mk] at *
  rw [this, ← Ideal.Quotient.mkₐ_eq_mk k, AlgHom.commutes]

noncomputable def mapK : H ⊗[k] H →ₗ[k] H ⊗[↥K] H :=
  TensorProduct.lift
    (LinearMap.mk₂ k (fun x y : H => x ⊗ₜ[↥K] y)
      (fun x₁ x₂ y => TensorProduct.add_tmul x₁ x₂ y)
      (fun c x y => by show (c • x) ⊗ₜ[↥K] y = c • (x ⊗ₜ[↥K] y); exact (TensorProduct.smul_tmul' c x y).symm)
      (fun x y₁ y₂ => TensorProduct.tmul_add x y₁ y₂)
      (fun c x y => by show x ⊗ₜ[↥K] (c • y) = c • (x ⊗ₜ[↥K] y); exact TensorProduct.tmul_smul c x y))

/--
@isnad1 id=eq.0h5v.s12.9d61b75b9dda from=translated src=- shape=b943edb7 vocab=0688c595
-/
@[scoped simp] theorem mapK_tmul (x y : H) : mapK K (x ⊗ₜ[k] y) = x ⊗ₜ[↥K] y := rfl

/--
@isnad1 id=eq.0h5v.s13.0049202edbe8 from=translated src=- shape=e5f6660b vocab=08fd46cd
-/
theorem mapK_mul (s t : H ⊗[k] H) : mapK K (s * t) = mapK K s * mapK K t := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c d => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp [mul_add, hx, hy]
  | add x y hx hy => simp [add_mul, hx, hy]

noncomputable def mapKₐ : H ⊗[k] H →ₐ[k] H ⊗[↥K] H :=
  AlgHom.ofLinearMap (mapK K) (by simp [Algebra.TensorProduct.one_def]) (mapK_mul K)

noncomputable def Sₐ : H →ₐ[k] H :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode k) HopfAlgebra.antipode_one
    (fun a b => by rw [HopfAlgebra.antipode_mul_antidistrib, mul_comm])

noncomputable def ψ₀ : H →ₐ[k] H ⊗[↥K] H :=
  (mapKₐ K).comp ((Algebra.TensorProduct.map (Sₐ (k := k) (H := H)) (AlgHom.id k H)).comp (Bialgebra.comulAlgHom k H))

/--
@isnad1 id=eq.0h4v.s13.61cb2752f63b from=translated src=- shape=72846537 vocab=85d5a4f0
-/
theorem ψ₀_apply (c : H) :
    ψ₀ K c = mapK K ((HopfAlgebra.antipode k).rTensor H (Coalgebra.comul (R := k) c)) := by
  simp only [ψ₀, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  show mapK K (Algebra.TensorProduct.map (Sₐ (k := k)) (AlgHom.id k H) (Coalgebra.comul c)) = _
  congr 1

/--
@isnad1 id=eq.3h4v.s12.6c6349664770 from=translated src=- shape=45dc84ad vocab=fffdc0ad
-/
theorem ψ₀_eq_zero_of_mem {a : H} (ha : a ∈ K) (hε : Coalgebra.counit (R := k) a = 0)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) :
    ψ₀ K a = 0 := by

  have key : ∀ t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b},
      mapK K ((HopfAlgebra.antipode k).rTensor H t)
        = (LinearMap.mul' k H ((HopfAlgebra.antipode k).rTensor H t)) ⊗ₜ[↥K] (1 : H) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨x, hx, y, hy, rfl⟩ := ht
      simp only [LinearMap.rTensor_tmul, mapK_tmul, LinearMap.mul'_apply]
      rw [show (HopfAlgebra.antipode k x) ⊗ₜ[↥K] y = (HopfAlgebra.antipode k x) ⊗ₜ[↥K] ((⟨y, hy⟩ : ↥K) • (1 : H)) by
        simp [Subalgebra.smul_def]]
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Subalgebra.smul_def, smul_eq_mul, mul_comm]
    | zero => simp
    | add s t _ _ hs ht => simp [map_add, TensorProduct.add_tmul, hs, ht]
    | smul c t _ ht => simp [map_smul, ht, TensorProduct.smul_tmul']
  rw [ψ₀_apply, key _ (hΔ a ha), HopfAlgebra.mul_antipode_rTensor_comul_apply, hε, map_zero,
    TensorProduct.zero_tmul]

variable (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
  Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})

abbrev C : Type v := H ⊗[k] Q K

noncomputable def θ : H ⊗[k] H →ₐ[k] C K := Algebra.TensorProduct.map (AlgHom.id k H) (π K)

/--
@isnad1 id=eq.0h5v.s10.ecbc0b61810b from=translated src=- shape=1bbe0ef8 vocab=0185ca9a
-/
@[scoped simp] theorem θ_tmul (x y : H) : θ K (x ⊗ₜ[k] y) = x ⊗ₜ[k] π K y := rfl

/--
@isnad1 id=eq.1h4v.s12.9537c32d2674 from=translated src=- shape=ed25422b vocab=eceece8d
-/
theorem θ_eq_of_mem_span (t : H ⊗[k] H)
    (ht : t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) :
    θ K t = (TensorProduct.rid k H ((Coalgebra.counit (R := k) (A := H)).lTensor H t)) ⊗ₜ[k] (1 : Q K) := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨x, hx, y, hy, rfl⟩ := ht
    simp only [θ_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    rw [π_eq_algebraMap_counit_of_mem K hy, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  | zero => simp
  | add s t _ _ hs ht => simp [map_add, TensorProduct.add_tmul, hs, ht]
  | smul c t _ ht => simp [map_smul, ht, TensorProduct.smul_tmul']

include hΔ in
/--
@isnad1 id=eq.2h4v.s12.162a270c98de from=translated src=- shape=9991ceee vocab=1145cdec
-/
theorem θ_comul_of_mem {a : H} (ha : a ∈ K) : θ K (Coalgebra.comul (R := k) a) = a ⊗ₜ[k] (1 : Q K) := by
  rw [θ_eq_of_mem_span K _ (hΔ a ha), Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]

noncomputable def g : H →ₐ[↥K] C K :=
  { ((θ K).comp (Bialgebra.comulAlgHom k H)).toRingHom with
    commutes' := fun a => by
      show θ K (Coalgebra.comul (R := k) (a : H)) = algebraMap (↥K) (C K) a
      rw [θ_comul_of_mem K hΔ a.2]
      rfl }

noncomputable def β : H ⊗[↥K] H →ₐ[H] C K :=
  Algebra.TensorProduct.lift (Algebra.ofId H (C K)) (g K hΔ) (fun _ _ => Commute.all _ _)

/--
@isnad1 id=eq.1h5v.s13.b4653e91ba08 from=translated src=- shape=d871cd0d vocab=a26cf6a6
-/
theorem β_tmul (x y : H) : β K hΔ (x ⊗ₜ[↥K] y) = (x ⊗ₜ[k] (1 : Q K)) * θ K (Coalgebra.comul (R := k) y) := by
  rw [β, Algebra.TensorProduct.lift_tmul]
  rfl

noncomputable def ψ : Q K →ₐ[k] H ⊗[↥K] H :=
  Ideal.Quotient.liftₐ (J K) (ψ₀ K) (fun a ha => by
    have hle : J K ≤ RingHom.ker (ψ₀ K).toRingHom := by
      rw [J, Ideal.span_le]
      rintro x ⟨hxK, hxε⟩
      exact ψ₀_eq_zero_of_mem K hxK hxε hΔ
    exact hle ha)

/--
@isnad1 id=eq.1h4v.s13.9cb8bc60baae from=translated src=- shape=70db2a89 vocab=325c5c09
-/
theorem ψ_π (c : H) : ψ K hΔ (π K c) = ψ₀ K c := rfl

noncomputable def δ : C K →ₐ[H] H ⊗[↥K] H :=
  Algebra.TensorProduct.lift (Algebra.ofId H (H ⊗[↥K] H)) (ψ K hΔ) (fun _ _ => Commute.all _ _)

/--
@isnad1 id=eq.1h5v.s13.12c153cb56b6 from=translated src=- shape=cef5a786 vocab=dcf0cf99
-/
theorem δ_tmul (x c : H) : δ K hΔ (x ⊗ₜ[k] π K c) = x • ψ₀ K c := by
  rw [δ, Algebra.TensorProduct.lift_tmul, ψ_π, Algebra.ofId_apply]
  exact (Algebra.smul_def x (ψ₀ K c)).symm

omit [HopfAlgebra k H] in

/--
@isnad1 id=eq.0h3v.s12.8ed58af4b9e3 from=translated src=- shape=0559203b vocab=6fde7a56
-/
theorem assoc_symm_lTensor_rTensor_assoc [AddCommGroup H] [Module k H] (f : H →ₗ[k] H) :
    (TensorProduct.assoc k H H H).symm.toLinearMap ∘ₗ (f.rTensor H).lTensor H ∘ₗ
      (TensorProduct.assoc k H H H).toLinearMap = (f.lTensor H).rTensor H := by
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

/--
@isnad1 id=eq.0h5v.s14.22fa2af6e86a from=translated src=- shape=eff1d0c5 vocab=5ba502c3
-/
theorem smul_mapK (x : H) (s : H ⊗[k] H) :
    x • mapK K s = mapK K ((LinearMap.mul' k H).rTensor H ((TensorProduct.assoc k H H H).symm (x ⊗ₜ[k] s))) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [mapK_tmul, TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearMap.mul'_apply]
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  | add s t hs ht => simp only [map_add, smul_add, hs, ht, TensorProduct.tmul_add]

/--
@isnad1 id=eq.1h4v.s15.a1cd6eea78ae from=translated src=- shape=2753c0d8 vocab=4f492e09
-/
theorem δ_θ (t : H ⊗[k] H) :
    δ K hΔ (θ K t) = mapK K ((LinearMap.mul' k H).rTensor H ((TensorProduct.assoc k H H H).symm
      ((((HopfAlgebra.antipode k).rTensor H) ∘ₗ Coalgebra.comul).lTensor H t))) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [θ_tmul, δ_tmul, ψ₀_apply, smul_mapK]
    rfl
  | add s t hs ht => simp only [map_add, hs, ht]

/--
@isnad1 id=eq.0h3v.s14.8ee1b0ca0b99 from=translated src=- shape=41170630 vocab=2520e9d3
-/
theorem sweedler₁ (h : H) :
    (LinearMap.mul' k H).rTensor H ((TensorProduct.assoc k H H H).symm
      ((((HopfAlgebra.antipode k).rTensor H) ∘ₗ Coalgebra.comul).lTensor H (Coalgebra.comul (R := k) h)))
      = (1 : H) ⊗ₜ[k] h := by
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply, ← Coalgebra.coassoc_apply]
  have h1 := LinearMap.congr_fun (assoc_symm_lTensor_rTensor_assoc (k := k) (H := H) (HopfAlgebra.antipode k))
    ((Coalgebra.comul (R := k)).rTensor H (Coalgebra.comul (R := k) h))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at h1
  rw [h1, ← LinearMap.comp_apply (f := (LinearMap.mul' k H).rTensor H), ← LinearMap.rTensor_comp,
    ← LinearMap.comp_apply (f := ((LinearMap.mul' k H) ∘ₗ (HopfAlgebra.antipode k).lTensor H).rTensor H),
    ← LinearMap.rTensor_comp, LinearMap.comp_assoc, HopfAlgebra.mul_antipode_lTensor_comul,
    LinearMap.rTensor_comp, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul]
  simp

/--
@isnad1 id=eq.1h4v.s13.08307319b781 from=translated src=- shape=da54b4d6 vocab=321ba0b5
-/
theorem δ_β_includeRight (h : H) : δ K hΔ (β K hΔ ((1 : H) ⊗ₜ[↥K] h)) = (1 : H) ⊗ₜ[↥K] h := by
  rw [β_tmul, show ((1 : H) ⊗ₜ[k] (1 : Q K)) = 1 from rfl, one_mul, δ_θ, sweedler₁, mapK_tmul]

/--
@isnad1 id=eq.0h3v.s14.da569c3171cc from=translated src=- shape=4fff4a69 vocab=369de4fe
-/
theorem sweedler₂ (c : H) :
    (LinearMap.mul' k H).rTensor H ((TensorProduct.assoc k H H H).symm
      ((Coalgebra.comul (R := k)).lTensor H (((HopfAlgebra.antipode k).rTensor H) (Coalgebra.comul (R := k) c))))
      = (1 : H) ⊗ₜ[k] c := by

  have e1 : (Coalgebra.comul (R := k)).lTensor H (((HopfAlgebra.antipode k).rTensor H) (Coalgebra.comul (R := k) c))
      = ((HopfAlgebra.antipode k).rTensor (H ⊗[k] H)) ((Coalgebra.comul (R := k)).lTensor H (Coalgebra.comul (R := k) c)) := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply (g := (Coalgebra.comul (R := k)).lTensor H),
      LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor]
  rw [e1, ← Coalgebra.coassoc_apply]
  have e2 : ∀ t : (H ⊗[k] H) ⊗[k] H, (TensorProduct.assoc k H H H).symm
      (((HopfAlgebra.antipode k).rTensor (H ⊗[k] H)) (TensorProduct.assoc k H H H t))
      = ((HopfAlgebra.antipode k).rTensor H).rTensor H t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s z =>
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => rfl
      | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [e2, ← LinearMap.comp_apply (f := (LinearMap.mul' k H).rTensor H), ← LinearMap.rTensor_comp,
    ← LinearMap.comp_apply (f := ((LinearMap.mul' k H) ∘ₗ (HopfAlgebra.antipode k).rTensor H).rTensor H),
    ← LinearMap.rTensor_comp, LinearMap.comp_assoc, HopfAlgebra.mul_antipode_rTensor_comul,
    LinearMap.rTensor_comp, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul]
  simp

/--
@isnad1 id=eq.1h5v.s13.2f2dc2ed12aa from=translated src=- shape=49406b63 vocab=5a822709
-/
theorem β_mapK (x y : H) : β K hΔ (mapK K (x ⊗ₜ[k] y)) = (x ⊗ₜ[k] (1 : Q K)) * θ K (Coalgebra.comul (R := k) y) := by
  rw [mapK_tmul, β_tmul]

/--
@isnad1 id=eq.1h4v.s13.e548565991a9 from=translated src=- shape=b286abaa vocab=e8cc5ccf
-/
theorem β_ψ₀ (c : H) : β K hΔ (ψ₀ K c) = (1 : H) ⊗ₜ[k] π K c := by
  rw [ψ₀_apply]

  have hgen : ∀ s : H ⊗[k] H, β K hΔ (mapK K s)
      = θ K ((LinearMap.mul' k H).rTensor H ((TensorProduct.assoc k H H H).symm
          ((Coalgebra.comul (R := k)).lTensor H s))) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [β_mapK, LinearMap.lTensor_tmul]

      have : ∀ w : H ⊗[k] H, (x ⊗ₜ[k] (1 : Q K)) * θ K w
          = θ K ((LinearMap.mul' k H).rTensor H ((TensorProduct.assoc k H H H).symm (x ⊗ₜ[k] w))) := by
        intro w
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
        | add a b ha hb => simp only [map_add, mul_add, ha, hb, TensorProduct.tmul_add]
      exact this _
    | add s t hs ht => simp only [map_add, hs, ht]
  rw [hgen, sweedler₂, θ_tmul]

/--
@isnad1 id=eq.1h4v.s13.1ec08bf6e0af from=translated src=- shape=f8f4c460 vocab=6d1eb463
-/
theorem β_δ_includeRight (c : H) : β K hΔ (δ K hΔ ((1 : H) ⊗ₜ[k] π K c)) = (1 : H) ⊗ₜ[k] π K c := by
  rw [δ_tmul, one_smul, β_ψ₀]

/--
@isnad1 id=eq.1h3v.s13.4e4e04cda2fd from=translated src=- shape=81996313 vocab=3473ec5e
-/
theorem δ_comp_β : (δ K hΔ).comp (β K hΔ) = AlgHom.id H (H ⊗[↥K] H) := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply AlgHom.ext
    intro h
    simpa using δ_β_includeRight K hΔ h

/--
@isnad1 id=eq.1h3v.s12.0bb9b097ab61 from=translated src=- shape=40ef727c vocab=3473ec5e
-/
theorem β_comp_δ : (β K hΔ).comp (δ K hΔ) = AlgHom.id H (C K) := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro c
    simpa [π] using β_δ_includeRight K hΔ c

noncomputable def βEquiv : (H ⊗[↥K] H) ≃ₐ[H] C K :=
  AlgEquiv.ofAlgHom (β K hΔ) (δ K hΔ) (β_comp_δ K hΔ) (δ_comp_β K hΔ)

end S17Torsor
open scoped _root_.P2MW.S_HopfAlgebra_faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span.S17Torsor

namespace S17Sq
open S17Torsor

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
variable (K' K : Subalgebra k H) [Algebra ↥K' ↥K] [IsScalarTower ↥K' ↥K H]
variable (hΔ' : ∀ x ∈ K', Coalgebra.comul (R := k) x ∈
  Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b})
variable (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
  Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})

noncomputable abbrev inclKH : ↥K →ₐ[↥K'] H := IsScalarTower.toAlgHom (↥K') (↥K) H

noncomputable abbrev idIncl : H ⊗[↥K'] ↥K →ₐ[↥K'] H ⊗[↥K'] H :=
  Algebra.TensorProduct.map (AlgHom.id (↥K') H) (inclKH K' K)

noncomputable abbrev Kbar : Subalgebra k (Q K') := K.map (π K')

noncomputable abbrev ιbar : H ⊗[k] ↥(Kbar K' K) →ₐ[k] C K' :=
  Algebra.TensorProduct.map (AlgHom.id k H) (Kbar K' K).val

/--
@isnad1 id=injectiv.0h4v.s13.89fa966af2d9 from=translated src=- shape=3253508b vocab=2834a50a
-/
theorem ιbar_injective : Function.Injective (ιbar K' K) := by
  have : Function.Injective ((Kbar K' K).val.toLinearMap.lTensor H) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  intro x y hxy
  exact this (by exact hxy)

noncomputable def c : H ⊗[↥K'] ↥K →ₐ[k] C K' :=
  ((β K' hΔ').restrictScalars k).comp ((idIncl K' K).restrictScalars k)

/--
@isnad1 id=eq.1h6v.s14.ee984d5b8e96 from=translated src=- shape=7d0b5a0b vocab=e00513bb
-/
theorem c_tmul (h : H) (a : ↥K) : c K' K hΔ' (h ⊗ₜ[↥K'] a) = (h ⊗ₜ[k] (1 : Q K')) * θ K' (Coalgebra.comul (R := k) (a : H)) := by
  simp only [c, AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  exact β_tmul K' hΔ' h _

/--
@isnad1 id=mem.1h5v.s13.d766b15b8170 from=translated src=- shape=8d7329a1 vocab=213c934d
-/
theorem θ_mem_range_of_mem_span (t : H ⊗[k] H)
    (ht : t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) :
    θ K' t ∈ (ιbar K' K).range := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨x, hx, y, hy, rfl⟩ := ht
    refine ⟨x ⊗ₜ[k] ⟨π K' y, Subalgebra.mem_map.mpr ⟨y, hy, rfl⟩⟩, ?_⟩
    simp
  | zero => simp
  | add s t _ _ hs ht => rw [map_add]; exact add_mem hs ht
  | smul r t _ ht => rw [map_smul]; exact Subalgebra.smul_mem _ ht r

include hΔ in

/--
@isnad1 id=le.2h4v.s13.7636222aa051 from=translated src=- shape=c7a098f1 vocab=cdffea68
-/
theorem range_c_le : (c K' K hΔ').range ≤ (ιbar K' K).range := by
  rintro _ ⟨t, rfl⟩
  show c K' K hΔ' t ∈ _
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul h a =>
    rw [c_tmul]
    have hθ : θ K' (Coalgebra.comul (R := k) (a : H)) ∈ (ιbar K' K).range :=
      θ_mem_range_of_mem_span K' K _ (hΔ a a.2)
    have h1 : (h ⊗ₜ[k] (1 : Q K')) ∈ (ιbar K' K).range := ⟨h ⊗ₜ[k] 1, by simp⟩
    exact mul_mem h1 hθ
  | add s t hs ht => rw [map_add]; exact add_mem hs ht

include hΔ in

/--
@isnad1 id=le.2h4v.s13.f4fbcd835663 from=translated src=- shape=aabd9c80 vocab=cdffea68
-/
theorem le_range_c : (ιbar K' K).range ≤ (c K' K hΔ').range := by
  rw [Algebra.TensorProduct.map_range]
  apply sup_le
  · rintro _ ⟨h, rfl⟩
    refine ⟨h ⊗ₜ[↥K'] 1, ?_⟩
    show c K' K hΔ' (h ⊗ₜ[↥K'] 1) = h ⊗ₜ[k] (1 : Q K')
    rw [c_tmul, Subalgebra.coe_one, Bialgebra.comul_one, show (1 : H ⊗[k] H) = (1 : H) ⊗ₜ[k] (1 : H) from rfl,
      θ_tmul, map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]
  · rintro _ ⟨⟨_, ha⟩, rfl⟩
    obtain ⟨a, haK, rfl⟩ := Subalgebra.mem_map.mp ha

    have key' : ∀ t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b},
        ∃ s : H ⊗[↥K'] ↥K, (idIncl K' K) s = mapK K' ((HopfAlgebra.antipode k).rTensor H t) := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨x, hx, y, hy, rfl⟩ := ht
        exact ⟨(HopfAlgebra.antipode k x) ⊗ₜ[↥K'] ⟨y, hy⟩, rfl⟩
      | zero => exact ⟨0, by simp⟩
      | add s t _ _ hs ht =>
        obtain ⟨s₁, hs₁⟩ := hs; obtain ⟨t₁, ht₁⟩ := ht
        exact ⟨s₁ + t₁, by simp [map_add, hs₁, ht₁]⟩
      | smul r t _ ht =>
        obtain ⟨t₁, ht₁⟩ := ht
        refine ⟨algebraMap k (↥K') r • t₁, ?_⟩
        rw [map_smul, ht₁, map_smul, algebraMap_smul, map_smul]
    obtain ⟨s, hs⟩ := key' _ (hΔ a haK)
    refine ⟨s, ?_⟩
    show (β K' hΔ') ((idIncl K' K) s) = (1 : H) ⊗ₜ[k] π K' a
    rw [hs, ← ψ₀_apply, β_ψ₀]

include hΔ in
/--
@isnad1 id=eq.2h4v.s13.685c0010d74c from=translated src=- shape=43a19a1f vocab=4b6a9f27
-/
theorem range_c_eq : (c K' K hΔ').range = (ιbar K' K).range :=
  le_antisymm (range_c_le K' K hΔ' hΔ) (le_range_c K' K hΔ' hΔ)

/--
@isnad1 id=nontrivi.0h3v.s6.1c8bb887a133 from=translated src=- shape=0ce3dfc9 vocab=876b2537
-/
theorem nontrivial_Q : Nontrivial (Q K') := by
  refine ⟨⟨0, 1, fun h01 => ?_⟩⟩
  have h1 : J K' = ⊤ := Ideal.Quotient.zero_eq_one_iff.mp h01
  revert h1
  intro h1

  have hε : ∀ x ∈ J K', Coalgebra.counit (R := k) x = 0 := by
    intro x hx
    rw [J] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hx.2
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [Bialgebra.counit_mul, hx]
  have := hε 1 ((Ideal.eq_top_iff_one _).mp h1)
  rw [Bialgebra.counit_one] at this
  exact one_ne_zero this

noncomputable def e₂ [Module.Flat (↥K') H] : (H ⊗[↥K'] ↥K) ≃ₐ[k] (H ⊗[k] ↥(Kbar K' K)) :=
  have hinj : Function.Injective (c K' K hΔ') := by
    have h1 : Function.Injective (idIncl K' K) := by
      have : Function.Injective ((inclKH K' K).toLinearMap.lTensor H) :=
        Module.Flat.lTensor_preserves_injective_linearMap _ (fun x y h => Subtype.ext h)
      intro x y hxy
      exact this (by exact hxy)
    intro x y hxy
    exact h1 ((βEquiv K' hΔ').injective hxy)
  (AlgEquiv.ofInjective (c K' K hΔ') hinj).trans
    ((Subalgebra.equivOfEq _ _ (range_c_eq K' K hΔ' hΔ)).trans
      (AlgEquiv.ofInjective (ιbar K' K) (ιbar_injective K' K)).symm)

/--
@isnad1 id=eq.2h5v.s15.0ffb095d68f7 from=translated src=- shape=8b44b4e4 vocab=201f0836
-/
theorem ιbar_e₂ [Module.Flat (↥K') H] (s : H ⊗[↥K'] ↥K) :
    ιbar K' K (e₂ K' K hΔ' hΔ s) = c K' K hΔ' s := by
  simp only [e₂, AlgEquiv.trans_apply]

  have h1 : ∀ y : ↥((ιbar K' K).range), ιbar K' K ((AlgEquiv.ofInjective (ιbar K' K) (ιbar_injective K' K)).symm y) = y := by
    intro y
    have := AlgEquiv.ofInjective_apply (ιbar K' K) (ιbar_injective K' K) ((AlgEquiv.ofInjective (ιbar K' K) (ιbar_injective K' K)).symm y)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm
  rw [h1]
  rfl

/--
@isnad1 id=eq.2h4v.s15.82979f83d1de from=translated src=- shape=a750b1c3 vocab=05e96d73
-/
theorem idIncl_eq [Module.Flat (↥K') H] :
    (idIncl K' K).toRingHom = ((βEquiv K' hΔ').symm.toRingEquiv.toRingHom.comp (ιbar K' K).toRingHom).comp
      (e₂ K' K hΔ' hΔ).toRingEquiv.toRingHom := by
  apply RingHom.ext
  intro s
  show idIncl K' K s = (βEquiv K' hΔ').symm (ιbar K' K (e₂ K' K hΔ' hΔ s))
  rw [ιbar_e₂, AlgEquiv.eq_symm_apply]
  rfl

/--
@isnad1 id=faithful.1h5v.s7.2b93b5844326 from=translated src=- shape=3409187a vocab=508e47b5
-/
theorem respectsIso_left {R S T : Type v} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (e : S ≃+* T)
    (hf : f.FaithfullyFlat) : (e.toRingHom.comp f).FaithfullyFlat :=
  RingHom.FaithfullyFlat.respectsIso.1 f e hf

/--
@isnad1 id=faithful.1h5v.s7.2c566da91dc0 from=translated src=- shape=89aa432e vocab=508e47b5
-/
theorem respectsIso_right {R S T : Type v} [CommRing R] [CommRing S] [CommRing T] (f : S →+* T) (e : R ≃+* S)
    (hf : f.FaithfullyFlat) : (f.comp e.toRingHom).FaithfullyFlat :=
  RingHom.FaithfullyFlat.respectsIso.2 f e hf

set_option maxHeartbeats 1600000 in

/--
@isnad1 id=faithful.0h4v.s12.77b0b1f3f675 from=translated src=- shape=3d25ca5f vocab=bef66092
-/
theorem ff_map_val_id (L : Subalgebra k (Q K')) [Module.Free ↥L (Q K')] :
    (Algebra.TensorProduct.map L.val (AlgHom.id k H) : ↥L ⊗[k] H →ₐ[k] Q K' ⊗[k] H).toRingHom.FaithfullyFlat := by
  haveI : Nontrivial (Q K') := nontrivial_Q K'
  haveI : Module.FaithfullyFlat (↥L) (Q K') := inferInstance
  haveI : Module.FaithfullyFlat (↥L ⊗[k] H) ((↥L ⊗[k] H) ⊗[↥L] Q K') := inferInstance
  have h1 : (algebraMap (↥L ⊗[k] H) ((↥L ⊗[k] H) ⊗[↥L] Q K')).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

  let e : ((↥L ⊗[k] H) ⊗[↥L] Q K') ≃ₐ[↥L] (Q K' ⊗[k] H) :=
    (Algebra.TensorProduct.comm (↥L) (↥L ⊗[k] H) (Q K')).trans
      (Algebra.TensorProduct.cancelBaseChange k (↥L) (↥L) (Q K') H)
  have h2 := respectsIso_left _ e.toRingEquiv h1
  convert h2 using 1
  apply RingHom.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a h =>
    show (a : Q K') ⊗ₜ[k] h = e ((a ⊗ₜ[k] h) ⊗ₜ[↥L] (1 : Q K'))
    simp only [e, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul]
    erw [Algebra.TensorProduct.cancelBaseChange_tmul]
    rw [Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/--
@isnad1 id=faithful.0h4v.s12.d642e2dbe3de from=translated src=- shape=741cbc96 vocab=e89e11f4
-/
theorem ff_ιbar [Module.Free ↥(Kbar K' K) (Q K')] : (ιbar K' K).toRingHom.FaithfullyFlat := by
  have h := ff_map_val_id K' (Kbar K' K)
  have h2 := respectsIso_right _ (Algebra.TensorProduct.comm k H ↥(Kbar K' K)).toRingEquiv
    (respectsIso_left _ (Algebra.TensorProduct.comm k (Q K') H).toRingEquiv h)
  convert h2 using 1
  apply RingHom.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul h a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

include hΔ' hΔ in

/--
@isnad1 id=faithful.2h4v.s14.d219ffdda899 from=translated src=- shape=ae5f6620 vocab=c642d5e3
-/
theorem ff_idIncl [Module.Flat (↥K') H] [Module.Free ↥(Kbar K' K) (Q K')] :
    (idIncl K' K).toRingHom.FaithfullyFlat := by
  rw [idIncl_eq K' K hΔ' hΔ]
  exact respectsIso_right _ _ (respectsIso_left _ _ (ff_ιbar K' K))

include hΔ' hΔ in

/--
@isnad1 id=faithful.2h4v.s14.61d19d444463 from=translated src=- shape=510501c4 vocab=32e24a0d
-/
theorem ff_inclId [Module.Flat (↥K') H] [Module.Free ↥(Kbar K' K) (Q K')] :
    (Algebra.TensorProduct.map (inclKH K' K) (AlgHom.id (↥K') H)).toRingHom.FaithfullyFlat := by
  have h := ff_idIncl K' K hΔ' hΔ
  have h2 := respectsIso_right _ (Algebra.TensorProduct.comm (↥K') (↥K) H).toRingEquiv
    (respectsIso_left _ (Algebra.TensorProduct.comm (↥K') H H).toRingEquiv h)
  convert h2 using 1
  apply RingHom.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a h => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end S17Sq
open scoped _root_.P2MW.S_HopfAlgebra_faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span.S17Torsor

open S17Torsor S17Sq in
/--
@isnad1 id=faithful.4h6v.s14.9635cf18c7ca from=translated src=- shape=bff81b2a vocab=b864c87e
-/
theorem solution
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K' K : Subalgebra k H) [Algebra ↥K' ↥K] [IsScalarTower ↥K' ↥K H]
    (hΔ' : ∀ x ∈ K', Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b})
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    [Module.Flat ↥K' H]
    (Hb : Type v) [CommRing Hb] [Algebra k Hb] (π : H →ₐ[k] Hb) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = Ideal.span {x : H | x ∈ K' ∧ Coalgebra.counit (R := k) x = 0})
    [Module.Free ↥(K.map π) Hb] :
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ↥K' ↥K H) (AlgHom.id ↥K' H)).toRingHom.FaithfullyFlat := by
  classical

  have hJ : J K' = RingHom.ker π := by rw [hker]; rfl
  let e : Q K' ≃ₐ[k] Hb :=
    (Ideal.quotientEquivAlgOfEq k hJ).trans (Ideal.quotientKerAlgEquivOfSurjective hπ)
  have he : ∀ x : H, e (S17Torsor.π K' x) = π x := by
    intro x
    show (Ideal.quotientKerAlgEquivOfSurjective hπ) ((Ideal.quotientEquivAlgOfEq k hJ) (Ideal.Quotient.mkₐ k (J K') x)) = π x
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.quotientEquivAlgOfEq_mk]
    try exact Ideal.quotientKerAlgEquivOfSurjective_apply hπ x
  have hmap : (Kbar K' K).map e.toAlgHom = K.map π := by
    rw [Kbar, Subalgebra.map_map]
    congr 1
  let eK : ↥(Kbar K' K) ≃ₐ[k] ↥(K.map π) :=
    ((Kbar K' K).equivMapOfInjective e.toAlgHom e.injective).trans (Subalgebra.equivOfEq _ _ hmap)
  have heK : ∀ a : ↥(Kbar K' K), ((eK a : ↥(K.map π)) : Hb) = e (a : Q K') := fun a => rfl
  have heK' : ∀ b : ↥(K.map π), ((eK.symm b : ↥(Kbar K' K)) : Q K') = e.symm (b : Hb) := by
    intro b
    apply e.injective
    rw [AlgEquiv.apply_symm_apply, ← heK, AlgEquiv.apply_symm_apply]

  haveI : Module.Free ↥(Kbar K' K) (Q K') := by
    let σ : ↥(K.map π) →+* ↥(Kbar K' K) := eK.symm.toRingEquiv.toRingHom
    let σ' : ↥(Kbar K' K) →+* ↥(K.map π) := eK.toRingEquiv.toRingHom
    haveI : RingHomInvPair σ σ' := RingHomInvPair.of_ringEquiv eK.symm.toRingEquiv
    haveI : RingHomInvPair σ' σ := RingHomInvPair.of_ringEquiv eK.toRingEquiv
    let f : Hb ≃ₛₗ[σ] Q K' :=
      { e.symm.toLinearEquiv.toAddEquiv with
        map_smul' := fun b x => by
          show e.symm ((b : Hb) * x) = (eK.symm b : Q K') * e.symm x
          rw [map_mul, heK'] }
    exact Module.Free.of_equiv f
  exact ff_inclId K' K hΔ' hΔ
