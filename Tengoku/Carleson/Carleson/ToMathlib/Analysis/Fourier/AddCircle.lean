module

public import Tengoku.Carleson.Carleson.ToMathlib.Topology.Instances.AddCircle.Defs

public section

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h4v.s9.6e1a7b2d7a33 from=translated src=- shape=3d735aaa vocab=34fd40c0
-/
theorem fourier_comp_equivAddCircle {p q : ℝ} [hp : Fact (0 < p)] [hq : Fact (0 < q)]
  {x : AddCircle p} {n : ℤ} :
    fourier n (AddCircle.equivAddCircle p q hp.out.ne' hq.out.ne' x) = fourier n x := by
  simp only [fourier_apply, SetLike.coe_eq_coe]
  rw [AddCircle.toCircle_zsmul, AddCircle.toCircle_zsmul]
  congr 1
  rw [AddCircle.equivAddCircle_eq]
  have : ↑↑((AddCircle.equivIco p 0) x) = x := AddCircle.coe_equivIco
  nth_rw 2 [← this]
  rw [AddCircle.toCircle_apply_mk, AddCircle.toCircle_apply_mk]
  congr 1
  field [hq.out.ne']

/--
@isnad1 id=eq.0h4v.s9.9812d286ba0b from=translated src=- shape=882163ed vocab=4a38fb6e
-/
theorem fourierCoeff_comp_equivAddCircle {p q : ℝ} [hp : Fact (0 < p)] [hq : Fact (0 < q)]
  {f : AddCircle q → ℂ} {n : ℤ} :
    fourierCoeff (fun x ↦ f ((AddCircle.equivAddCircle p q hp.out.ne' hq.out.ne') x)) n
      = fourierCoeff f n := by
  unfold fourierCoeff
  simp only [smul_eq_mul]
  simp_rw [← @fourier_comp_equivAddCircle p q, ← Pi.mul_apply]
  apply AddCircle.measurePreserving_equivAddCircle.integral_comp
    (AddCircle.homeomorphAddCircle _ _ _ _).measurableEmbedding
