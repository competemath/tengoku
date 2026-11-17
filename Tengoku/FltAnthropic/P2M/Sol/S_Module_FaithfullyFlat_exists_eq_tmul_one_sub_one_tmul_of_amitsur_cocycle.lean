import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_FaithfullyFlat_exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_FaithfullyFlat_exists_eq_tmul_one_sub_one_tmul_of_amitsur_cocycle

set_option autoImplicit false

universe u v

open TensorProduct

namespace AmitsurDegreeOne

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

noncomputable abbrev d0 : S →ₗ[R] S ⊗[R] S := Algebra.TensorProduct.includeLeftSubRight R S

noncomputable def d1 : S ⊗[R] S →ₗ[R] S ⊗[R] (S ⊗[R] S) :=
  (Algebra.TensorProduct.map (AlgHom.id R S)
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S)).toLinearMap -
    (Algebra.TensorProduct.map (AlgHom.id R S)
      (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S)).toLinearMap +
    (Algebra.TensorProduct.includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)).toLinearMap

/--
@isnad1 id=eq.0h3v.s13.a21bd9dc9f85 from=translated src=- shape=670bd36c vocab=81681742
-/
theorem d1_apply (c : S ⊗[R] S) : d1 R S c =
    Algebra.TensorProduct.map (AlgHom.id R S) (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) c -
      Algebra.TensorProduct.map (AlgHom.id R S) (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) c +
      (Algebra.TensorProduct.includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) c := rfl

/--
@isnad1 id=eq.0h4v.s12.dd49286fe206 from=translated src=- shape=25a9215f vocab=176b71db
-/
theorem d1_tmul (a b : S) :
    d1 R S (a ⊗ₜ[R] b) = a ⊗ₜ[R] (b ⊗ₜ[R] 1) - a ⊗ₜ[R] (1 ⊗ₜ[R] b) + 1 ⊗ₜ[R] (a ⊗ₜ[R] b) := by
  rw [d1_apply, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.includeRight_apply]
  rfl

/--
@isnad1 id=eq.0h3v.s9.8a1da627445e from=translated src=- shape=72d2dc7c vocab=6a9fd158
-/
theorem d0_apply (s : S) : d0 R S s = s ⊗ₜ[R] 1 - 1 ⊗ₜ[R] s := rfl

/--
@isnad1 id=eq.0h2v.s11.95c850d21a0d from=translated src=- shape=f0b796ab vocab=6f74be19
-/
theorem d1_comp_d0 : d1 R S ∘ₗ d0 R S = 0 := by
  ext s
  rw [LinearMap.comp_apply, d0_apply, map_sub, d1_tmul, d1_tmul, LinearMap.zero_apply]
  abel

noncomputable def h1 : S ⊗[R] (S ⊗[R] S) →ₗ[R] S ⊗[R] S :=
  (LinearMap.mul' R S).rTensor S ∘ₗ (TensorProduct.assoc R S S S).symm.toLinearMap

noncomputable def h2 : S ⊗[R] (S ⊗[R] (S ⊗[R] S)) →ₗ[R] S ⊗[R] (S ⊗[R] S) :=
  (LinearMap.mul' R S).rTensor (S ⊗[R] S) ∘ₗ (TensorProduct.assoc R S S (S ⊗[R] S)).symm.toLinearMap

/--
@isnad1 id=eq.0h5v.s10.d3b8fdcecbda from=translated src=- shape=ef48f034 vocab=03d3c118
-/
theorem h1_tmul (t a b : S) : h1 R S (t ⊗ₜ[R] (a ⊗ₜ[R] b)) = (t * a) ⊗ₜ[R] b := by
  simp [h1]

/--
@isnad1 id=eq.0h5v.s12.9d5b3bddf13b from=translated src=- shape=0c647d2e vocab=f72aa5f7
-/
theorem h2_tmul (t a : S) (w : S ⊗[R] S) : h2 R S (t ⊗ₜ[R] (a ⊗ₜ[R] w)) = (t * a) ⊗ₜ[R] w := by
  simp [h2]

/--
@isnad1 id=eq.0h2v.s13.fb6f90de2cbb from=translated src=- shape=ec55363b vocab=541d8157
-/
theorem homotopy :
    h2 R S ∘ₗ (d1 R S).lTensor S - (d0 R S).lTensor S ∘ₗ h1 R S = LinearMap.id := by
  apply TensorProduct.ext'
  intro t w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.lTensor_tmul, d1_tmul,
      tmul_add, tmul_sub, map_add, map_sub, h2_tmul, h2_tmul, h2_tmul, h1_tmul, LinearMap.lTensor_tmul,
      d0_apply, tmul_sub, mul_one, LinearMap.id_apply]
    abel
  | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]

/--
@isnad1 id=exact.0h2v.s13.314a5f4451f0 from=translated src=- shape=f68de3bc vocab=f15e1212
-/
theorem exact_lTensor : Function.Exact ((d0 R S).lTensor S) ((d1 R S).lTensor S) := by
  intro x
  constructor
  · intro hx
    have key := LinearMap.congr_fun (homotopy R S) x
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, hx, map_zero, zero_sub,
      LinearMap.id_apply] at key
    exact ⟨-(h1 R S x), by rw [map_neg]; exact key⟩
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, d1_comp_d0, LinearMap.lTensor_zero, LinearMap.zero_apply]

/--
@isnad1 id=exact.0h2v.s11.6a24f68a8cf4 from=translated src=- shape=5b8328ff vocab=fd1430c0
-/
theorem exact [Module.FaithfullyFlat R S] : Function.Exact (d0 R S) (d1 R S) :=
  Module.FaithfullyFlat.lTensor_reflects_exact R S _ _ (exact_lTensor R S)

end AmitsurDegreeOne

/--
@isnad1 id=ex.1h3v.s12.a4ef166d96d3 from=translated src=- shape=29c933f9 vocab=6f9bb497
-/
theorem solution
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (c : S ⊗[R] S)
    (hc : Algebra.TensorProduct.map (AlgHom.id R S)
            (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) c +
          (Algebra.TensorProduct.includeRight : S ⊗[R] S →ₐ[R] S ⊗[R] (S ⊗[R] S)) c =
        Algebra.TensorProduct.map (AlgHom.id R S)
            (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) c) :
    ∃ s : S, c = s ⊗ₜ[R] (1 : S) - (1 : S) ⊗ₜ[R] s := by
  have hd : AmitsurDegreeOne.d1 R S c = 0 := by
    rw [AmitsurDegreeOne.d1_apply, sub_add_eq_add_sub, hc, sub_self]
  obtain ⟨s, hs⟩ := ((AmitsurDegreeOne.exact R S) c).mp hd
  exact ⟨s, hs.symm⟩
