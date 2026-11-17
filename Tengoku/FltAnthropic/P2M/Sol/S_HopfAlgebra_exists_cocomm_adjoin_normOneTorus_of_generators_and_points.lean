import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_exists_cocomm_adjoin_normOneTorus_of_generators_and_points.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_exists_cocomm_adjoin_normOneTorus_of_generators_and_points

set_option maxHeartbeats 12800000
open scoped TensorProduct

noncomputable section NormOneTorus
variable (K : Type) [Field K] (c : K)

abbrev normOneRel : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ 2 - MvPolynomial.C c * MvPolynomial.X 1 ^ 2 - 1
def B₀ := MvPolynomial (Fin 2) K ⧸ Ideal.span {normOneRel K c}

scoped instance instCR : CommRing (B₀ K c) := inferInstanceAs (CommRing (MvPolynomial (Fin 2) K ⧸ _))
scoped instance instAlg : Algebra K (B₀ K c) := inferInstanceAs (Algebra K (MvPolynomial (Fin 2) K ⧸ _))

def U : B₀ K c := Ideal.Quotient.mk _ (MvPolynomial.X 0)
def V : B₀ K c := Ideal.Quotient.mk _ (MvPolynomial.X 1)
abbrev C₀ : B₀ K c := algebraMap K (B₀ K c) c

/--
@isnad1 id=eq.0h2v.s7.dc7f5adb58b7 from=translated src=- shape=a6781dac vocab=1958849c
-/
lemma UVrel₀ : (U K c) ^ 2 - (C₀ K c) * (V K c) ^ 2 = 1 := by
  let mkB : MvPolynomial (Fin 2) K →ₐ[K] B₀ K c := Ideal.Quotient.mkₐ K _
  have hU : U K c = mkB (MvPolynomial.X 0) := rfl
  have hV : V K c = mkB (MvPolynomial.X 1) := rfl
  have hC : C₀ K c = mkB (MvPolynomial.C c) := (mkB.commutes c).symm
  have h0 : mkB (normOneRel K c) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have h1 : mkB (MvPolynomial.X 0 ^ 2 - MvPolynomial.C c * MvPolynomial.X 1 ^ 2 - 1) = 0 := h0
  rw [map_sub, map_sub, map_mul, map_pow, map_pow, map_one, ← hU, ← hV, ← hC] at h1
  linear_combination h1

def B₀.lift {R : Type} [CommRing R] [Algebra K R] (u v : R)
    (huv : u ^ 2 - algebraMap K R c * v ^ 2 = 1) : B₀ K c →ₐ[K] R :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![u, v])
    (fun p hp => by
      rw [Ideal.mem_span_singleton] at hp
      obtain ⟨q, rfl⟩ := hp
      simp only [map_mul, MvPolynomial.aeval_def, normOneRel, map_sub, map_pow,
        map_one, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]
      rw [show u^2 - algebraMap K R c * v^2 - 1 = 0 from by linear_combination huv]
      ring)

/--
@isnad1 id=eq.1h5v.s8.5270b5200d08 from=translated src=- shape=55025be8 vocab=a4f27a01
-/
lemma B₀.lift_U {R : Type} [CommRing R] [Algebra K R] (u v : R) (huv) :
    B₀.lift K c u v huv (U K c) = u := by
  show (MvPolynomial.aeval ![u, v] : MvPolynomial (Fin 2) K →ₐ[K] R) (MvPolynomial.X 0) = u
  rw [MvPolynomial.aeval_X]; rfl

/--
@isnad1 id=eq.1h5v.s8.e9af714b42d4 from=translated src=- shape=c367e6a7 vocab=5a2ef919
-/
lemma B₀.lift_V {R : Type} [CommRing R] [Algebra K R] (u v : R) (huv) :
    B₀.lift K c u v huv (V K c) = v := by
  show (MvPolynomial.aeval ![u, v] : MvPolynomial (Fin 2) K →ₐ[K] R) (MvPolynomial.X 1) = v
  rw [MvPolynomial.aeval_X]; rfl

/--
@isnad1 id=eq.2h5v.s8.8230c2e2eb8d from=translated src=- shape=813066d5 vocab=c62ba2ad
-/
lemma B₀.algHom_ext {R : Type} [CommRing R] [Algebra K R] {f g : B₀ K c →ₐ[K] R}
    (hU : f (U K c) = g (U K c)) (hV : f (V K c) = g (V K c)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i; fin_cases i
  · exact hU
  · exact hV

/--
@isnad1 id=eq.0h2v.s12.569e9e3162a7 from=translated src=- shape=809eb0c0 vocab=58085bf2
-/
lemma comulB_welldef :
    ((U K c)⊗ₜ[K](U K c) + ((C₀ K c)⊗ₜ[K](1:B₀ K c))*((V K c)⊗ₜ[K](V K c)))^2
    - ((C₀ K c) ⊗ₜ[K] (1 : B₀ K c))
      * ((U K c)⊗ₜ[K](V K c) + (V K c)⊗ₜ[K](U K c))^2
    = (1 : B₀ K c ⊗[K] B₀ K c) := by
  set a : B₀ K c ⊗[K] B₀ K c := (U K c) ⊗ₜ[K] 1 with ha
  set b : B₀ K c ⊗[K] B₀ K c := (V K c) ⊗ₜ[K] 1 with hb
  set x : B₀ K c ⊗[K] B₀ K c := 1 ⊗ₜ[K] (U K c) with hx
  set y : B₀ K c ⊗[K] B₀ K c := 1 ⊗ₜ[K] (V K c) with hy
  set CT : B₀ K c ⊗[K] B₀ K c := (C₀ K c) ⊗ₜ[K] 1 with hCT
  have rUU : (U K c) ⊗ₜ[K] (U K c) = a * x := by
    rw [ha, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have rVV : (V K c) ⊗ₜ[K] (V K c) = b * y := by
    rw [hb, hy, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have rUV : (U K c) ⊗ₜ[K] (V K c) = a * y := by
    rw [ha, hy, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have rVU : (V K c) ⊗ₜ[K] (U K c) = b * x := by
    rw [hb, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hL : a^2 - CT * b^2 = 1 := by
    rw [ha, hb, hCT]
    calc (U K c ⊗ₜ[K] (1:B₀ K c))^2 - (C₀ K c ⊗ₜ[K] 1) * (V K c ⊗ₜ[K] (1:B₀ K c))^2
        = ((U K c)^2 - C₀ K c * (V K c)^2) ⊗ₜ[K] (1:B₀ K c) := by
          rw [sq, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
            sq, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
            Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            ← TensorProduct.sub_tmul]
          ring_nf
      _ = (1:B₀ K c) ⊗ₜ[K] (1:B₀ K c) := by rw [UVrel₀]
      _ = 1 := (Algebra.TensorProduct.one_def).symm
  have hCTshuttle : CT = (1:B₀ K c) ⊗ₜ[K] (C₀ K c) := by
    rw [hCT, show C₀ K c = c • (1:B₀ K c) from (Algebra.algebraMap_eq_smul_one c),
      TensorProduct.smul_tmul]
  have hR : x^2 - CT * y^2 = 1 := by
    rw [hx, hy, hCTshuttle]
    calc ((1:B₀ K c) ⊗ₜ[K] U K c)^2
        - ((1:B₀ K c) ⊗ₜ[K] C₀ K c) * ((1:B₀ K c) ⊗ₜ[K] V K c)^2
        = (1:B₀ K c) ⊗ₜ[K] ((U K c)^2 - C₀ K c * (V K c)^2) := by
          rw [sq, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            sq, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            ← TensorProduct.tmul_sub]
          ring_nf
      _ = (1:B₀ K c) ⊗ₜ[K] (1:B₀ K c) := by rw [UVrel₀]
      _ = 1 := (Algebra.TensorProduct.one_def).symm
  rw [rUU, rVV, rUV, rVU]
  linear_combination (x^2 - CT * y^2) * hL + hR

def comulB : B₀ K c →ₐ[K] (B₀ K c ⊗[K] B₀ K c) :=
  B₀.lift K c
    ((U K c) ⊗ₜ[K] (U K c) + ((C₀ K c) ⊗ₜ[K] (1:B₀ K c)) * ((V K c) ⊗ₜ[K] (V K c)))
    ((U K c) ⊗ₜ[K] (V K c) + (V K c) ⊗ₜ[K] (U K c))
    (comulB_welldef K c)

def counitB : B₀ K c →ₐ[K] K := B₀.lift K c 1 0 (by ring)
def antipodeB : B₀ K c →ₐ[K] B₀ K c :=
  B₀.lift K c (U K c) (-(V K c)) (by linear_combination UVrel₀ K c)

/--
@isnad1 id=eq.0h2v.s11.3722343eea8d from=translated src=- shape=4b34109c vocab=dd9ea57c
-/
lemma comulB_U : comulB K c (U K c)
    = ((U K c) ⊗ₜ[K] (U K c) + ((C₀ K c) ⊗ₜ[K] (1:B₀ K c)) * ((V K c) ⊗ₜ[K] (V K c))) :=
  B₀.lift_U K c ((U K c) ⊗ₜ[K] (U K c) + ((C₀ K c) ⊗ₜ[K] (1:B₀ K c)) * ((V K c) ⊗ₜ[K] (V K c))) ((U K c) ⊗ₜ[K] (V K c) + (V K c) ⊗ₜ[K] (U K c)) (comulB_welldef K c)
/--
@isnad1 id=eq.0h2v.s10.50045db8696d from=translated src=- shape=1ada70ae vocab=a99cda7f
-/
lemma comulB_V : comulB K c (V K c) = ((U K c) ⊗ₜ[K] (V K c) + (V K c) ⊗ₜ[K] (U K c)) :=
  B₀.lift_V K c ((U K c) ⊗ₜ[K] (U K c) + ((C₀ K c) ⊗ₜ[K] (1:B₀ K c)) * ((V K c) ⊗ₜ[K] (V K c))) ((U K c) ⊗ₜ[K] (V K c) + (V K c) ⊗ₜ[K] (U K c)) (comulB_welldef K c)
/--
@isnad1 id=eq.0h2v.s7.a126bfa35348 from=translated src=- shape=8414e4b4 vocab=eb748ced
-/
lemma counitB_U : counitB K c (U K c) = 1 := B₀.lift_U K c _ _ _
/--
@isnad1 id=eq.0h2v.s7.c85560b7eb88 from=translated src=- shape=8414e4b4 vocab=8bdd72c9
-/
lemma counitB_V : counitB K c (V K c) = 0 := B₀.lift_V K c _ _ _
/--
@isnad1 id=eq.0h2v.s7.1d57bd95e222 from=translated src=- shape=1785d281 vocab=d8df5483
-/
lemma antipodeB_U : antipodeB K c (U K c) = U K c :=
  B₀.lift_U K c (U K c) (-(V K c)) (by linear_combination UVrel₀ K c)
/--
@isnad1 id=eq.0h2v.s7.8778482bffdc from=translated src=- shape=0d1315b7 vocab=c145c618
-/
lemma antipodeB_V : antipodeB K c (V K c) = -(V K c) :=
  B₀.lift_V K c (U K c) (-(V K c)) (by linear_combination UVrel₀ K c)

/--
@isnad1 id=eq.0h2v.s10.fc6149716344 from=translated src=- shape=b61015b2 vocab=4ce496bd
-/
lemma CT_eq_smul_one : (C₀ K c) ⊗ₜ[K] (1:B₀ K c) = c • (1 : B₀ K c ⊗[K] B₀ K c) := by
  rw [show (C₀ K c : B₀ K c) = c • (1:B₀ K c) from Algebra.algebraMap_eq_smul_one c]
  rfl

/--
@isnad1 id=eq.0h3v.s10.715869934180 from=translated src=- shape=c5492ae6 vocab=63d0794d
-/
lemma CT_mul_eq_smul (p : B₀ K c ⊗[K] B₀ K c) :
    ((C₀ K c) ⊗ₜ[K] (1:B₀ K c)) * p = c • p := by
  rw [CT_eq_smul_one]
  exact smul_one_mul c p

/--
@isnad1 id=eq.0h2v.s10.cdebc8450112 from=translated src=- shape=562fc2ef vocab=6a87a0ef
-/
lemma comulB_U' : comulB K c (U K c)
    = (U K c) ⊗ₜ[K] (U K c) + c • ((V K c) ⊗ₜ[K] (V K c)) := by
  rw [comulB_U, CT_mul_eq_smul]

/--
@isnad1 id=existsun.1h4v.s9.2cfd128b3cb9 from=translated src=- shape=4ea3b480 vocab=df27ee5d
-/
lemma hliftB₀ (w z : AlgebraicClosure K)
    (hwz : w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1) :
    ∃! f : B₀ K c →ₐ[K] AlgebraicClosure K, f (U K c) = w ∧ f (V K c) = z := by
  refine ⟨B₀.lift K c w z hwz,
    ⟨B₀.lift_U K c w z hwz, B₀.lift_V K c w z hwz⟩,
    fun g ⟨hgu, hgv⟩ => ?_⟩
  exact B₀.algHom_ext K c
    (hgu.trans (B₀.lift_U K c w z hwz).symm)
    (hgv.trans (B₀.lift_V K c w z hwz).symm)

scoped instance instCoalgStruct : CoalgebraStruct K (B₀ K c) where
  comul := (comulB K c).toLinearMap
  counit := (counitB K c).toLinearMap

section helpers
variable {R : Type} [CommRing R] [Algebra K R]

/--
@isnad1 id=eq.0h6v.s12.d556a65155bd from=translated src=- shape=1bbfc2b5 vocab=f11a40a8
-/
lemma rTensor_algHom_mul (φ : B₀ K c →ₐ[K] R) (p q : B₀ K c ⊗[K] B₀ K c) :
    LinearMap.rTensor (B₀ K c) φ.toLinearMap (p * q)
    = LinearMap.rTensor (B₀ K c) φ.toLinearMap p
      * LinearMap.rTensor (B₀ K c) φ.toLinearMap q := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction q using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' => simp only [Algebra.TensorProduct.tmul_mul_tmul,
        LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_mul]
    | add r s hr hs => simp only [mul_add, map_add, hr, hs]
  | add r s hr hs => simp only [add_mul, map_add, hr, hs]

/--
@isnad1 id=eq.0h6v.s12.da81e69d629c from=translated src=- shape=da5cec78 vocab=7b95d2c9
-/
lemma lTensor_algHom_mul (φ : B₀ K c →ₐ[K] R) (p q : B₀ K c ⊗[K] B₀ K c) :
    LinearMap.lTensor (B₀ K c) φ.toLinearMap (p * q)
    = LinearMap.lTensor (B₀ K c) φ.toLinearMap p
      * LinearMap.lTensor (B₀ K c) φ.toLinearMap q := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction q using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' => simp only [Algebra.TensorProduct.tmul_mul_tmul,
        LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, map_mul]
    | add r s hr hs => simp only [mul_add, map_add, hr, hs]
  | add r s hr hs => simp only [add_mul, map_add, hr, hs]

/--
@isnad1 id=eq.0h4v.s13.b4f3312b5e5a from=translated src=- shape=ca3c52ed vocab=b37cb326
-/
lemma comm_mul (p q : B₀ K c ⊗[K] B₀ K c) :
    (TensorProduct.comm K (B₀ K c) (B₀ K c)) (p * q)
    = (TensorProduct.comm K (B₀ K c) (B₀ K c)) p
      * (TensorProduct.comm K (B₀ K c) (B₀ K c)) q := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction q using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.comm_tmul]
    | add r s hr hs => simp only [mul_add, map_add, hr, hs]
  | add r s hr hs => simp only [add_mul, map_add, hr, hs]

/--
@isnad1 id=eq.0h4v.s12.cec27d320c43 from=translated src=- shape=6c72d227 vocab=04a28ef2
-/
lemma mul'_mul (p q : B₀ K c ⊗[K] B₀ K c) :
    (LinearMap.mul' K (B₀ K c)) (p * q)
    = (LinearMap.mul' K (B₀ K c)) p * (LinearMap.mul' K (B₀ K c)) q := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction q using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.mul'_apply]
      ring
    | add r s hr hs => simp only [mul_add, map_add, hr, hs]
  | add r s hr hs => simp only [add_mul, map_add, hr, hs]

/--
@isnad1 id=eq.0h4v.s15.811e82a07518 from=translated src=- shape=215a04e2 vocab=0ecb1b43
-/
lemma assoc_mul (p q : (B₀ K c ⊗[K] B₀ K c) ⊗[K] B₀ K c) :
    (TensorProduct.assoc K (B₀ K c) (B₀ K c) (B₀ K c)) (p * q)
    = (TensorProduct.assoc K (B₀ K c) (B₀ K c) (B₀ K c)) p
      * (TensorProduct.assoc K (B₀ K c) (B₀ K c) (B₀ K c)) q := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul ab d =>
    induction q using TensorProduct.induction_on with
    | zero => simp
    | tmul ab' d' =>
      induction ab using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        induction ab' using TensorProduct.induction_on with
        | zero => simp
        | tmul a' b' =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.assoc_tmul]
        | add r s hr hs =>
          simp only [TensorProduct.add_tmul, mul_add, map_add, hr, hs]
      | add r s hr hs =>
        simp only [add_mul, TensorProduct.add_tmul, map_add, hr, hs]
    | add r s hr hs => simp only [mul_add, map_add, hr, hs]
  | add r s hr hs => simp only [add_mul, map_add, hr, hs]

end helpers

/--
@isnad1 id=eq.0h4v.s14.b995ab95376f from=translated src=- shape=43b1ff3f vocab=0a94f857
-/
lemma rTensor_comulB_mul (p q : B₀ K c ⊗[K] B₀ K c) :
    LinearMap.rTensor (B₀ K c) (comulB K c).toLinearMap (p * q)
    = LinearMap.rTensor (B₀ K c) (comulB K c).toLinearMap p
      * LinearMap.rTensor (B₀ K c) (comulB K c).toLinearMap q := by
  induction p using TensorProduct.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | tmul a b =>
    induction q using TensorProduct.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | tmul a' b' => simp only [Algebra.TensorProduct.tmul_mul_tmul,
        LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, _root_.map_mul]
    | add r s hr hs => simp only [mul_add, map_add, hr, hs]
  | add r s hr hs => simp only [add_mul, map_add, hr, hs]

/--
@isnad1 id=eq.0h4v.s14.f20220d15f08 from=translated src=- shape=253d55ff vocab=7f57b8a5
-/
lemma lTensor_comulB_mul (p q : B₀ K c ⊗[K] B₀ K c) :
    LinearMap.lTensor (B₀ K c) (comulB K c).toLinearMap (p * q)
    = LinearMap.lTensor (B₀ K c) (comulB K c).toLinearMap p
      * LinearMap.lTensor (B₀ K c) (comulB K c).toLinearMap q := by
  induction p using TensorProduct.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | tmul a b =>
    induction q using TensorProduct.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | tmul a' b' => simp only [Algebra.TensorProduct.tmul_mul_tmul,
        LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, _root_.map_mul]
    | add r s hr hs => simp only [mul_add, map_add, hr, hs]
  | add r s hr hs => simp only [add_mul, map_add, hr, hs]

/--
@isnad1 id=eq.6h5v.s11.f6497e3ed735 from=translated src=- shape=6d828439 vocab=a7475c78
-/
lemma B₀.linearMap_ext {M : Type} [CommRing M] [Algebra K M]
    {f g : B₀ K c →ₗ[K] M}
    (hf1 : f 1 = 1) (hg1 : g 1 = 1)
    (hfmul : ∀ a b, f (a * b) = f a * f b) (hgmul : ∀ a b, g (a * b) = g a * g b)
    (hU : f (U K c) = g (U K c)) (hV : f (V K c) = g (V K c)) :
    f = g := by
  set φ : B₀ K c →ₐ[K] M :=
    { toFun := f, map_one' := hf1, map_mul' := hfmul,
      map_zero' := map_zero f, map_add' := map_add f,
      commutes' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one, map_smul, hf1, Algebra.algebraMap_eq_smul_one] }
  set ψ : B₀ K c →ₐ[K] M :=
    { toFun := g, map_one' := hg1, map_mul' := hgmul,
      map_zero' := map_zero g, map_add' := map_add g,
      commutes' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one, map_smul, hg1, Algebra.algebraMap_eq_smul_one] }
  have hφψ : φ = ψ := B₀.algHom_ext K c hU hV
  exact LinearMap.ext fun x => DFunLike.congr_fun hφψ x

def assocLM : (B₀ K c ⊗[K] B₀ K c) ⊗[K] B₀ K c →ₗ[K] B₀ K c ⊗[K] (B₀ K c ⊗[K] B₀ K c) :=
  (TensorProduct.assoc K (B₀ K c) (B₀ K c) (B₀ K c)).toLinearMap

/--
@isnad1 id=eq.0h5v.s12.3d3925720edb from=translated src=- shape=dd3e34c3 vocab=e9fdb894
-/
lemma assocLM_tmul (a b d : B₀ K c) :
    assocLM K c ((a ⊗ₜ[K] b) ⊗ₜ[K] d) = a ⊗ₜ[K] (b ⊗ₜ[K] d) :=
  TensorProduct.assoc_tmul a b d

/--
@isnad1 id=eq.0h4v.s14.3eaabf898d56 from=translated src=- shape=fd21db1c vocab=fdc4999f
-/
lemma assocLM_add (p q : (B₀ K c ⊗[K] B₀ K c) ⊗[K] B₀ K c) :
    assocLM K c (p + q) = assocLM K c p + assocLM K c q :=
  (assocLM K c).map_add p q

/--
@isnad1 id=eq.0h4v.s13.b0a1adf15530 from=translated src=- shape=aab7941b vocab=a6569b24
-/
lemma assocLM_smul (r : K) (p : (B₀ K c ⊗[K] B₀ K c) ⊗[K] B₀ K c) :
    assocLM K c (r • p) = r • assocLM K c p :=
  (assocLM K c).map_smul r p

/--
@isnad1 id=eq.0h4v.s14.08a724820944 from=translated src=- shape=fd21db1c vocab=6d992b55
-/
lemma assocLM_mul (p q : (B₀ K c ⊗[K] B₀ K c) ⊗[K] B₀ K c) :
    assocLM K c (p * q) = assocLM K c p * assocLM K c q :=
  assoc_mul K c p q

/--
@isnad1 id=eq.0h2v.s13.582c92b03ee1 from=translated src=- shape=0f6c146b vocab=c910c877
-/
lemma coassocB₀_lhs1 :
    assocLM K c (LinearMap.rTensor (B₀ K c) (comulB K c).toLinearMap ((comulB K c) 1)) = 1 := by
  rw [map_one, Algebra.TensorProduct.one_def, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, map_one, Algebra.TensorProduct.one_def,
    assocLM_tmul, ← Algebra.TensorProduct.one_def, ← Algebra.TensorProduct.one_def]

/--
@isnad1 id=eq.0h2v.s13.d558255066c3 from=translated src=- shape=e2f4b5ae vocab=821e23ec
-/
lemma coassocB₀_rhs1 :
    LinearMap.lTensor (B₀ K c) (comulB K c).toLinearMap ((comulB K c) 1) = 1 := by
  rw [map_one, Algebra.TensorProduct.one_def, LinearMap.lTensor_tmul,
    AlgHom.toLinearMap_apply, map_one, ← Algebra.TensorProduct.one_def]

/--
@isnad1 id=eq.0h4v.s15.325f321566cc from=translated src=- shape=5af93a0e vocab=6d5fe3f1
-/
lemma coassocB₀_lhsmul (a b : B₀ K c) :
    assocLM K c (LinearMap.rTensor (B₀ K c) (comulB K c).toLinearMap ((comulB K c) (a * b)))
    = assocLM K c (LinearMap.rTensor (B₀ K c) (comulB K c).toLinearMap ((comulB K c) a))
      * assocLM K c (LinearMap.rTensor (B₀ K c) (comulB K c).toLinearMap ((comulB K c) b)) := by
  rw [map_mul, rTensor_comulB_mul, assocLM_mul]

/--
@isnad1 id=eq.0h4v.s14.abb4a79aa50a from=translated src=- shape=f73ae6c4 vocab=711dfa09
-/
lemma coassocB₀_rhsmul (a b : B₀ K c) :
    LinearMap.lTensor (B₀ K c) (comulB K c).toLinearMap ((comulB K c) (a * b))
    = LinearMap.lTensor (B₀ K c) (comulB K c).toLinearMap ((comulB K c) a)
      * LinearMap.lTensor (B₀ K c) (comulB K c).toLinearMap ((comulB K c) b) := by
  rw [map_mul, lTensor_comulB_mul]

abbrev rTcB : B₀ K c ⊗[K] B₀ K c →ₗ[K] (B₀ K c ⊗[K] B₀ K c) ⊗[K] B₀ K c :=
  LinearMap.rTensor (B₀ K c) (comulB K c).toLinearMap
abbrev lTcB : B₀ K c ⊗[K] B₀ K c →ₗ[K] B₀ K c ⊗[K] (B₀ K c ⊗[K] B₀ K c) :=
  LinearMap.lTensor (B₀ K c) (comulB K c).toLinearMap

/--
@isnad1 id=eq.0h4v.s13.08bf9b201e46 from=translated src=- shape=07b25aca vocab=c63279d2
-/
lemma rTcB_add (p q : B₀ K c ⊗[K] B₀ K c) : rTcB K c (p + q) = rTcB K c p + rTcB K c q :=
  (rTcB K c).map_add p q
/--
@isnad1 id=eq.0h4v.s13.f0fe834aa01d from=translated src=- shape=b5326296 vocab=96d4aaf4
-/
lemma rTcB_smul (r : K) (p : B₀ K c ⊗[K] B₀ K c) : rTcB K c (r • p) = r • rTcB K c p :=
  (rTcB K c).map_smul r p
/--
@isnad1 id=eq.0h4v.s12.3d01bea38f73 from=translated src=- shape=37ca449c vocab=348daf8b
-/
lemma rTcB_tmul (a b : B₀ K c) : rTcB K c (a ⊗ₜ[K] b) = (comulB K c a) ⊗ₜ[K] b := by
  simp only [rTcB, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]

/--
@isnad1 id=eq.0h4v.s13.db0dd17598ee from=translated src=- shape=9a86e550 vocab=7a421264
-/
lemma lTcB_add (p q : B₀ K c ⊗[K] B₀ K c) : lTcB K c (p + q) = lTcB K c p + lTcB K c q :=
  (lTcB K c).map_add p q
/--
@isnad1 id=eq.0h4v.s13.0cd5bea2816e from=translated src=- shape=22f20cf8 vocab=904cec83
-/
lemma lTcB_smul (r : K) (p : B₀ K c ⊗[K] B₀ K c) : lTcB K c (r • p) = r • lTcB K c p :=
  (lTcB K c).map_smul r p
/--
@isnad1 id=eq.0h4v.s12.c58fc4e20290 from=translated src=- shape=b223465b vocab=4636c404
-/
lemma lTcB_tmul (a b : B₀ K c) : lTcB K c (a ⊗ₜ[K] b) = a ⊗ₜ[K] (comulB K c b) := by
  simp only [lTcB, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply]

/--
@isnad1 id=eq.0h5v.s11.79e8268bf3a7 from=translated src=- shape=e96b838f vocab=883d4248
-/
lemma smul_tmul3_l (r : K) (a : B₀ K c ⊗[K] B₀ K c) (b : B₀ K c) :
    (r • a) ⊗ₜ[K] b = r • (a ⊗ₜ[K] b : (B₀ K c ⊗[K] B₀ K c) ⊗[K] B₀ K c) :=
  TensorProduct.smul_tmul' r a b
/--
@isnad1 id=eq.0h5v.s11.41b3e1c1ce84 from=translated src=- shape=85877c8e vocab=883d4248
-/
lemma smul_tmul3_r (r : K) (a : B₀ K c) (b : B₀ K c ⊗[K] B₀ K c) :
    a ⊗ₜ[K] (r • b) = r • (a ⊗ₜ[K] b : B₀ K c ⊗[K] (B₀ K c ⊗[K] B₀ K c)) :=
  TensorProduct.tmul_smul r a b

set_option synthInstance.maxHeartbeats 3200000 in
/--
@isnad1 id=eq.0h6v.s13.9c9c420ec506 from=translated src=- shape=5f143fec vocab=38504f21
-/
lemma four_reorder_B₀₃ (A B C D : B₀ K c ⊗[K] (B₀ K c ⊗[K] B₀ K c)) :
    A + D + (B + C) = A + B + (C + D) := by
  rw [add_assoc A D (B + C), add_comm D (B + C), add_assoc B C D, ← add_assoc A B (C + D)]

set_option synthInstance.maxHeartbeats 1600000 in
/--
@isnad1 id=eq.0h2v.s14.940cfec5c6f0 from=translated src=- shape=d901683f vocab=95f294fa
-/
lemma coassocB₀_U :
    assocLM K c (LinearMap.rTensor (B₀ K c) (comulB K c).toLinearMap ((comulB K c) (U K c)))
    = LinearMap.lTensor (B₀ K c) (comulB K c).toLinearMap ((comulB K c) (U K c)) := by
  show assocLM K c (rTcB K c ((comulB K c) (U K c))) = lTcB K c ((comulB K c) (U K c))
  simp only [comulB_U', comulB_V,
    rTcB_add, rTcB_smul, rTcB_tmul, lTcB_add, lTcB_smul, lTcB_tmul,
    TensorProduct.add_tmul, TensorProduct.tmul_add,
    smul_tmul3_l, smul_tmul3_r,
    assocLM_add, assocLM_smul, assocLM_tmul, smul_add]
  exact four_reorder_B₀₃ K c _ _ _ _

set_option synthInstance.maxHeartbeats 1600000 in
/--
@isnad1 id=eq.0h2v.s14.b3da6cb27b7d from=translated src=- shape=d901683f vocab=403580f4
-/
lemma coassocB₀_V :
    assocLM K c (LinearMap.rTensor (B₀ K c) (comulB K c).toLinearMap ((comulB K c) (V K c)))
    = LinearMap.lTensor (B₀ K c) (comulB K c).toLinearMap ((comulB K c) (V K c)) := by
  show assocLM K c (rTcB K c ((comulB K c) (V K c))) = lTcB K c ((comulB K c) (V K c))
  simp only [comulB_U', comulB_V,
    rTcB_add, rTcB_smul, rTcB_tmul, lTcB_add, lTcB_smul, lTcB_tmul,
    TensorProduct.add_tmul, TensorProduct.tmul_add,
    smul_tmul3_l, smul_tmul3_r,
    assocLM_add, assocLM_smul, assocLM_tmul, smul_add]
  exact four_reorder_B₀₃ K c _ _ _ _

/--
@isnad1 id=eq.0h2v.s13.f59987653927 from=translated src=- shape=42a963d1 vocab=cc2c228c
-/
lemma coassocB₀ :
    ((TensorProduct.assoc K (B₀ K c) (B₀ K c) (B₀ K c)).toLinearMap
      ∘ₗ LinearMap.rTensor (B₀ K c) (comulB K c).toLinearMap
      ∘ₗ (comulB K c).toLinearMap : B₀ K c →ₗ[K] B₀ K c ⊗[K] (B₀ K c ⊗[K] B₀ K c))
    = LinearMap.lTensor (B₀ K c) (comulB K c).toLinearMap ∘ₗ (comulB K c).toLinearMap := by
  refine B₀.linearMap_ext (M := B₀ K c ⊗[K] (B₀ K c ⊗[K] B₀ K c)) K c ?_ ?_ ?_ ?_ ?_ ?_
  · exact coassocB₀_lhs1 K c
  · exact coassocB₀_rhs1 K c
  · exact coassocB₀_lhsmul K c
  · exact coassocB₀_rhsmul K c
  · exact coassocB₀_U K c
  · exact coassocB₀_V K c

scoped instance instCoalg : Coalgebra K (B₀ K c) :=
  { instCoalgStruct K c with
    coassoc := coassocB₀ K c
    rTensor_counit_comp_comul := by
      refine B₀.linearMap_ext K c ?_ ?_ ?_ ?_ ?_ ?_
      · show LinearMap.rTensor _ (counitB K c).toLinearMap ((comulB K c) 1) = 1
        rw [map_one, Algebra.TensorProduct.one_def, LinearMap.rTensor_tmul,
          AlgHom.toLinearMap_apply, map_one, ← Algebra.TensorProduct.one_def]
      · show (1:K) ⊗ₜ[K] (1:B₀ K c) = 1
        exact (Algebra.TensorProduct.one_def).symm
      · intro a b
        show LinearMap.rTensor _ (counitB K c).toLinearMap ((comulB K c) (a*b))
          = (LinearMap.rTensor _ (counitB K c).toLinearMap ((comulB K c) a))
            * (LinearMap.rTensor _ (counitB K c).toLinearMap ((comulB K c) b))
        rw [map_mul]; exact rTensor_algHom_mul K c (counitB K c) _ _
      · intro a b
        show (1:K) ⊗ₜ[K] (a*b : B₀ K c) = ((1:K)⊗ₜ[K]a) * ((1:K)⊗ₜ[K]b)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      · show LinearMap.rTensor _ (counitB K c).toLinearMap ((comulB K c) (U K c))
          = (1:K) ⊗ₜ[K] (U K c)
        rw [comulB_U', map_add, map_smul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
          AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, counitB_U, counitB_V,
          TensorProduct.zero_tmul, smul_zero, add_zero]
      · show LinearMap.rTensor _ (counitB K c).toLinearMap ((comulB K c) (V K c))
          = (1:K) ⊗ₜ[K] (V K c)
        rw [comulB_V, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
          AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, counitB_U, counitB_V,
          TensorProduct.zero_tmul, add_zero]
    lTensor_counit_comp_comul := by
      refine B₀.linearMap_ext K c ?_ ?_ ?_ ?_ ?_ ?_
      · show LinearMap.lTensor _ (counitB K c).toLinearMap ((comulB K c) 1) = 1
        rw [map_one, Algebra.TensorProduct.one_def, LinearMap.lTensor_tmul,
          AlgHom.toLinearMap_apply, map_one, ← Algebra.TensorProduct.one_def]
      · show (1:B₀ K c) ⊗ₜ[K] (1:K) = 1
        exact (Algebra.TensorProduct.one_def).symm
      · intro a b
        show LinearMap.lTensor _ (counitB K c).toLinearMap ((comulB K c) (a*b))
          = _ * _
        rw [map_mul]; exact lTensor_algHom_mul K c (counitB K c) _ _
      · intro a b
        show (a*b : B₀ K c) ⊗ₜ[K] (1:K) = (a⊗ₜ[K](1:K)) * (b⊗ₜ[K](1:K))
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      · show LinearMap.lTensor _ (counitB K c).toLinearMap ((comulB K c) (U K c))
          = (U K c) ⊗ₜ[K] (1:K)
        rw [comulB_U', map_add, map_smul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
          AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, counitB_U, counitB_V,
          TensorProduct.tmul_zero, smul_zero, add_zero]
      · show LinearMap.lTensor _ (counitB K c).toLinearMap ((comulB K c) (V K c))
          = (V K c) ⊗ₜ[K] (1:K)
        rw [comulB_V, map_add, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
          AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, counitB_U, counitB_V,
          TensorProduct.tmul_zero, zero_add] }

noncomputable scoped instance instBialg : Bialgebra K (B₀ K c) :=
  Bialgebra.mk' K (B₀ K c)
    (by exact (counitB K c).map_one)
    (by intro a b; exact (counitB K c).map_mul a b)
    (by exact (comulB K c).map_one)
    (by intro a b; exact (comulB K c).map_mul a b)

noncomputable scoped instance instHopf : HopfAlgebra K (B₀ K c) :=
  { antipode := (antipodeB K c).toLinearMap
    mul_antipode_rTensor_comul := by
      refine B₀.linearMap_ext K c ?_ ?_ ?_ ?_ ?_ ?_
      · show LinearMap.mul' K _ (LinearMap.rTensor _ (antipodeB K c).toLinearMap ((comulB K c) 1)) = 1
        rw [map_one, Algebra.TensorProduct.one_def, LinearMap.rTensor_tmul,
          AlgHom.toLinearMap_apply, map_one, LinearMap.mul'_apply, one_mul]
      · show algebraMap K (B₀ K c) ((counitB K c) 1) = 1
        rw [map_one, map_one]
      · intro a b
        show LinearMap.mul' K _ (LinearMap.rTensor _ (antipodeB K c).toLinearMap ((comulB K c) (a*b)))
          = _ * _
        rw [map_mul, rTensor_algHom_mul K c (antipodeB K c)]
        exact mul'_mul K c _ _
      · intro a b
        exact ((Algebra.ofId K (B₀ K c)).comp (counitB K c)).map_mul a b
      · show LinearMap.mul' K _ (LinearMap.rTensor _ (antipodeB K c).toLinearMap ((comulB K c) (U K c)))
          = algebraMap K (B₀ K c) ((counitB K c) (U K c))
        rw [comulB_U', map_add, map_smul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
          AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, antipodeB_U, antipodeB_V,
          map_add, map_smul, LinearMap.mul'_apply, LinearMap.mul'_apply,
          counitB_U, map_one, neg_mul, smul_neg, ← sub_eq_add_neg, ← sq, ← sq,
          Algebra.smul_def]
        exact UVrel₀ K c
      · show LinearMap.mul' K _ (LinearMap.rTensor _ (antipodeB K c).toLinearMap ((comulB K c) (V K c)))
          = algebraMap K (B₀ K c) ((counitB K c) (V K c))
        rw [comulB_V, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
          AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, antipodeB_U, antipodeB_V,
          map_add, LinearMap.mul'_apply, LinearMap.mul'_apply,
          counitB_V, map_zero, neg_mul]
        ring
    mul_antipode_lTensor_comul := by
      refine B₀.linearMap_ext K c ?_ ?_ ?_ ?_ ?_ ?_
      · show LinearMap.mul' K _ (LinearMap.lTensor _ (antipodeB K c).toLinearMap ((comulB K c) 1)) = 1
        rw [map_one, Algebra.TensorProduct.one_def, LinearMap.lTensor_tmul,
          AlgHom.toLinearMap_apply, map_one, LinearMap.mul'_apply, one_mul]
      · show algebraMap K (B₀ K c) ((counitB K c) 1) = 1
        rw [map_one, map_one]
      · intro a b
        show LinearMap.mul' K _ (LinearMap.lTensor _ (antipodeB K c).toLinearMap ((comulB K c) (a*b)))
          = _ * _
        rw [map_mul, lTensor_algHom_mul K c (antipodeB K c)]
        exact mul'_mul K c _ _
      · intro a b
        exact ((Algebra.ofId K (B₀ K c)).comp (counitB K c)).map_mul a b
      · show LinearMap.mul' K _ (LinearMap.lTensor _ (antipodeB K c).toLinearMap ((comulB K c) (U K c)))
          = algebraMap K (B₀ K c) ((counitB K c) (U K c))
        rw [comulB_U', map_add, map_smul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
          AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, antipodeB_U, antipodeB_V,
          map_add, map_smul, LinearMap.mul'_apply, LinearMap.mul'_apply,
          counitB_U, map_one, mul_neg, smul_neg, ← sub_eq_add_neg, ← sq, ← sq,
          Algebra.smul_def]
        exact UVrel₀ K c
      · show LinearMap.mul' K _ (LinearMap.lTensor _ (antipodeB K c).toLinearMap ((comulB K c) (V K c)))
          = algebraMap K (B₀ K c) ((counitB K c) (V K c))
        rw [comulB_V, map_add, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
          AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, antipodeB_U, antipodeB_V,
          map_add, LinearMap.mul'_apply, LinearMap.mul'_apply,
          counitB_V, map_zero, mul_neg]
        ring }

/--
@isnad1 id=iscocomm.0h2v.s6.2fb6baa88c54 from=translated src=- shape=d0042f13 vocab=91077faa
-/
scoped instance instCocomm : Coalgebra.IsCocomm K (B₀ K c) := by
  constructor
  refine B₀.linearMap_ext K c ?_ ?_ ?_ ?_ ?_ ?_
  · show (TensorProduct.comm K (B₀ K c) (B₀ K c)) ((comulB K c) 1) = 1
    rw [map_one, Algebra.TensorProduct.one_def, TensorProduct.comm_tmul,
      ← Algebra.TensorProduct.one_def]
  · exact (comulB K c).map_one
  · intro a b
    show (TensorProduct.comm K (B₀ K c) (B₀ K c)) ((comulB K c) (a*b)) = _ * _
    rw [map_mul]; exact comm_mul K c _ _
  · exact fun a b => (comulB K c).map_mul a b
  · show (TensorProduct.comm K (B₀ K c) (B₀ K c)) ((comulB K c) (U K c)) = (comulB K c) (U K c)
    rw [comulB_U', map_add, map_smul, TensorProduct.comm_tmul, TensorProduct.comm_tmul]
  · show (TensorProduct.comm K (B₀ K c) (B₀ K c)) ((comulB K c) (V K c)) = (comulB K c) (V K c)
    rw [comulB_V, map_add, TensorProduct.comm_tmul, TensorProduct.comm_tmul, add_comm]

/--
@isnad1 id=eq.0h2v.s9.e67f7d3ce33a from=translated src=- shape=11e1d039 vocab=0ecc8a44
-/
lemma B₀_adjoin_top : Algebra.adjoin K {U K c, V K c} = (⊤ : Subalgebra K (B₀ K c)) := by
  let mkB : MvPolynomial (Fin 2) K →ₐ[K] B₀ K c := Ideal.Quotient.mkₐ K _
  have hsurj : Function.Surjective mkB := Ideal.Quotient.mkₐ_surjective K _
  rw [eq_top_iff]
  rintro x -
  obtain ⟨p, rfl⟩ := hsurj x
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [show mkB (MvPolynomial.C a) = algebraMap K (B₀ K c) a from mkB.commutes a]
    exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    fin_cases i
    · show (U K c) ∈ _; exact Algebra.subset_adjoin (Set.mem_insert _ _)
    · show (V K c) ∈ _; exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

end NormOneTorus

open scoped TensorProduct in
/--
@isnad1 id=ex.6h5v.s13.dd6e429569a5 from=translated src=- shape=06f30c10 vocab=88373d08
-/
theorem solution
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (B : Type) [CommRing B] [HopfAlgebra K B] (u v : B)
    (hrel : u ^ 2 - algebraMap K B c * v ^ 2 = 1)
    (hcu : Coalgebra.comul (R := K) u = u ⊗ₜ[K] u + c • (v ⊗ₜ[K] v))
    (hcv : Coalgebra.comul (R := K) v = u ⊗ₜ[K] v + v ⊗ₜ[K] u)
    (hliftB : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      ∃! f : B →ₐ[K] AlgebraicClosure K, f u = w ∧ f v = z) :
    ∃ (B₀ : Type) (_ : CommRing B₀) (_ : HopfAlgebra K B₀),
      Coalgebra.IsCocomm K B₀ ∧
      ∃ (u₀ v₀ : B₀),
        (Algebra.adjoin K {u₀, v₀} = ⊤) ∧
        (u₀ ^ 2 - algebraMap K B₀ c * v₀ ^ 2 = 1) ∧
        (Coalgebra.comul (R := K) u₀ = u₀ ⊗ₜ[K] u₀ + c • (v₀ ⊗ₜ[K] v₀)) ∧
        (Coalgebra.comul (R := K) v₀ = u₀ ⊗ₜ[K] v₀ + v₀ ⊗ₜ[K] u₀) ∧
        (∀ (w z : AlgebraicClosure K),
          w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
          ∃! g : B₀ →ₐ[K] AlgebraicClosure K, g u₀ = w ∧ g v₀ = z) := by
  exact ⟨_root_.P2MW.S_HopfAlgebra_exists_cocomm_adjoin_normOneTorus_of_generators_and_points.B₀ K c, inferInstance, instHopf K c, instCocomm K c,
    U K c, V K c, B₀_adjoin_top K c,
    UVrel₀ K c, comulB_U' K c, comulB_V K c, hliftB₀ K c⟩
