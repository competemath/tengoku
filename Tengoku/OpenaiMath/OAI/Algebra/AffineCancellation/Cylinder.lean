import Tengoku.OpenaiMath.OAI.Algebra.AffineCancellation.CylinderMaps

namespace OAI

noncomputable section

namespace ComplexCancellation.Cylinder

/-- Saturation needed at p=0. It does not assume the hypersurface is integral.
@isnad1 id=isleftre.2h3v.s8.d082d8d7b470 from=translated src=- shape=fbc39715 vocab=40186730
-/
lemma regular_quotient_of_prime {R : Type*} [CommRing R] [IsDomain R]
    {p h : R} (hp : Prime p) (hph : ¬p ∣ h) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {h}) p) := by
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro q hq
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hq
  obtain ⟨c, hc⟩ := hq
  have hpc : p ∣ c := (hp.dvd_or_dvd (show p ∣ h * c by rw [← hc]; exact dvd_mul_right _ _)).resolve_left hph
  obtain ⟨d, rfl⟩ := hpc
  have hr : r = h * d := by
    apply mul_left_cancel₀ hp.ne_zero
    linear_combination hc
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hr]
  exact dvd_mul_right _ _

/--
@isnad1 id=isleftre.1h2v.s6.a2b3aa2e12ec from=translated src=- shape=b9ae1cc9 vocab=fa760234
-/
lemma polynomial_C_regular {R : Type*} [CommRing R] {r : R} (hr : IsLeftRegular r) :
    IsLeftRegular (Polynomial.C r) := by
  intro f g hfg
  apply Polynomial.ext
  intro n
  apply hr
  simpa using congrArg (fun f : Polynomial R => f.coeff n) hfg

end ComplexCancellation.Cylinder

namespace ComplexCancellation.Cylinder

open MvPolynomial

def universal : Point P := ⟨p, s, u, F, J⟩
def parameters : Frame P := ⟨p, s, u, F⟩

namespace Point
variable {R S : Type*} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]

def eval (q : Point R) : P →ₐ[ℂ] R := MvPolynomial.aeval ![q.p, q.s, q.u, q.f, q.j]

/--
@isnad1 id=eq.0h2v.s6.1e59a6adfd26 from=translated src=- shape=a9b0c3cc vocab=0c60f326
-/
@[simp] lemma universal_eval (q : Point R) : universal.map q.eval.toRingHom = q := by
  ext <;> simp [universal, map, eval, ComplexCancellation.p, ComplexCancellation.s, ComplexCancellation.u, F, J]

/--
@isnad1 id=eq.0h2v.s7.850915b58a73 from=translated src=- shape=85488bad vocab=0ca3268c
-/
lemma eval_equation (q : Point R) : q.eval H = q.equation := by
  have h := universal.map_equation q.eval.toRingHom
  rw [universal_eval] at h
  exact h.symm

/--
@isnad1 id=eq.0h4v.s7.d03e4aa62477 from=translated src=- shape=9e444e10 vocab=6157e008
-/
lemma map_eval (q : Point R) (g : R →ₐ[ℂ] S) :
    g.comp q.eval = (q.map g.toRingHom).eval := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [eval, map]

/--
@isnad1 id=eq.0h0v.s8.cb3234f24517 from=translated src=- shape=3ca53db0 vocab=ee4637ee
-/
@[simp] lemma universal_eval_id : universal.eval = AlgHom.id ℂ P := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [eval, universal, ComplexCancellation.p, ComplexCancellation.s, ComplexCancellation.u, F, J]

end Point

def paramPoint {R : Type*} (t : Frame R) (z : R) : Point R := ⟨t.p, t.s, t.u, t.m, z⟩

/--
@isnad1 id=eq.0h5v.s6.c42b3422d0c4 from=translated src=- shape=72eb4439 vocab=6a35ae9b
-/
lemma paramPoint_map {R S : Type*} [CommRing R] [CommRing S]
    (t : Frame R) (z : R) (g : R →+* S) :
    (paramPoint t z).map g = paramPoint (t.map g) (g z) := rfl

/--
@isnad1 id=and.0h3v.s8.8c8a903f81e4 from=translated src=- shape=8c2257c6 vocab=86b82749
-/
lemma parameters_eval {R : Type*} [CommRing R] [Algebra ℂ R] (t : Frame R) (z : R) :
    parameters.map (paramPoint t z).eval.toRingHom = t ∧
    (paramPoint t z).eval J = z := by
  constructor
  · ext <;> simp [parameters, Frame.map, paramPoint, Point.eval, p, s, u, F]
  · simp [paramPoint, Point.eval, J]

/--
@isnad1 id=not.0h0v.s5.4c003f39fa52 from=translated src=- shape=6516253f vocab=18d6266b
-/
lemma p_not_dvd : ¬ p ∣ H := by
  intro h
  let q : Point ℂ := ⟨0, 0, 0, 0, 1⟩
  have h' := map_dvd q.eval h
  have hp : q.eval p = 0 := by simp [Point.eval, p, q]
  have hh : q.eval H = -1 := by rw [q.eval_equation]; norm_num [Point.equation, Point.x, q]
  rw [hp, hh, zero_dvd_iff] at h'
  norm_num at h'

/--
@isnad1 id=isleftre.0h0v.s10.15581efa686a from=translated src=- shape=fa1e4d4c vocab=ea8adca0
-/
lemma p_regular : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {H}) p) :=
  regular_quotient_of_prime (MvPolynomial.X_prime (i := 0)) p_not_dvd

def sourcePoint : Point (Polynomial A) :=
  universal.map ((Polynomial.CAlgHom : A →ₐ[ℂ] Polynomial A).comp
    (Ideal.Quotient.mkₐ ℂ (Ideal.span {H}))).toRingHom

/--
@isnad1 id=eq.0h0v.s8.759a2755e5df from=translated src=- shape=aa786730 vocab=d8dd1a6b
-/
lemma source_equation : sourcePoint.equation = 0 := by
  rw [sourcePoint, Point.map_equation]
  change Polynomial.C (Ideal.Quotient.mk (Ideal.span {H}) H) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton H)), Polynomial.C_0]

/--
@isnad1 id=isleftre.0h0v.s7.ba65d855d803 from=translated src=- shape=d7be7e0e vocab=bbba6216
-/
lemma source_p_regular : IsLeftRegular sourcePoint.p := polynomial_C_regular p_regular

/--
@isnad1 id=eq.1h1v.s10.7815eb0b55f3 from=translated src=- shape=acecbdc3 vocab=0c27ba30
-/
lemma source_p_cube (r : Polynomial A) (h : sourcePoint.p ^ 3 * r = 0) : r = 0 :=
  isLeftRegular_iff_right_eq_zero_of_mul.mp (source_p_regular.pow 3) r h

def model : Point P × P := decode parameters J

/--
@isnad1 id=eq.0h0v.s6.2b510d5a8c73 from=translated src=- shape=f0be4540 vocab=b3bc4b78
-/
lemma model_equation : model.1.equation = 0 := decode_equation _ _

def coefficientMap : A →ₐ[ℂ] P :=
  Ideal.Quotient.liftₐ (Ideal.span {H}) model.1.eval (by
    have hle : Ideal.span {H} ≤ RingHom.ker model.1.eval.toRingHom := by
      apply Ideal.span_le.mpr
      intro r hr
      rw [Set.mem_singleton_iff] at hr
      subst r
      change model.1.eval H = 0
      rw [Point.eval_equation, model_equation]
    exact fun r hr => hle hr)

def forward : Polynomial A →ₐ[ℂ] P :=
  Polynomial.eval₂AlgHom coefficientMap model.2 (fun _ => Commute.all _ _)

def backward : P →ₐ[ℂ] Polynomial A :=
  (paramPoint (encode sourcePoint Polynomial.X).1 (encode sourcePoint Polynomial.X).2).eval

/--
@isnad1 id=eq.0h0v.s9.11c75051be77 from=translated src=- shape=fc1ee070 vocab=5b2a7e46
-/
@[simp] lemma forward_X : forward Polynomial.X = model.2 := by simp [forward]

/--
@isnad1 id=eq.0h1v.s10.86844e04fb01 from=translated src=- shape=eb5b77a4 vocab=6ebbb299
-/
@[simp] lemma coefficientMap_mk (r : P) :
    coefficientMap (Ideal.Quotient.mk (Ideal.span {H}) r) = model.1.eval r := by
  exact Ideal.Quotient.lift_mk _ _ _

/--
@isnad1 id=eq.0h1v.s10.4db1f3a921a4 from=translated src=- shape=1e055f53 vocab=3da34cc7
-/
@[simp] lemma forward_C (r : A) : forward (Polynomial.C r) = coefficientMap r := by
  simp [forward]

/--
@isnad1 id=eq.0h0v.s8.db48bc86fd15 from=translated src=- shape=938f6dbb vocab=d5f2c401
-/
lemma forward_source : sourcePoint.map forward.toRingHom = model.1 := by
  apply Point.ext <;>
    simp [sourcePoint, Point.map, universal, Point.eval, p, s, u, F, J]

/--
@isnad1 id=eq.0h0v.s9.e3e1f597a03a from=translated src=- shape=b0793d97 vocab=0bcd20f7
-/
lemma forward_backward : forward.comp backward = AlgHom.id ℂ P := by
  have he := encode_map sourcePoint Polynomial.X forward.toRingHom
  rw [forward_source] at he
  change ((encode sourcePoint Polynomial.X).1.map forward.toRingHom,
    forward (encode sourcePoint Polynomial.X).2) = encode model.1 (forward Polynomial.X) at he
  rw [forward_X] at he
  change _ = encode (decode parameters J).1 (decode parameters J).2 at he
  rw [encode_decode] at he
  unfold backward
  rw [Point.map_eval (R := Polynomial A) (S := P) _ forward, paramPoint_map]
  have he₁ : (encode sourcePoint Polynomial.X).1.map forward.toRingHom = parameters :=
    congrArg Prod.fst he
  have he₂ : forward.toRingHom (encode sourcePoint Polynomial.X).2 = J :=
    congrArg Prod.snd he
  rw [he₁, he₂]
  exact Point.universal_eval_id

/--
@isnad1 id=eq.0h0v.s10.fa2456891966 from=translated src=- shape=ab599f01 vocab=295c16ac
-/
lemma backward_model :
    (model.1.map backward.toRingHom, backward model.2) = (sourcePoint, Polynomial.X) := by
  have hp := parameters_eval (encode sourcePoint Polynomial.X).1 (encode sourcePoint Polynomial.X).2
  have hd := decode_map (R := P) (S := Polynomial A) parameters J backward.toRingHom
  have hp₁ : parameters.map backward.toRingHom = (encode sourcePoint Polynomial.X).1 := hp.1
  have hp₂ : backward.toRingHom J = (encode sourcePoint Polynomial.X).2 := hp.2
  rw [hp₁, hp₂] at hd
  exact hd.trans (decode_encode sourcePoint Polynomial.X source_equation source_p_cube)

/--
@isnad1 id=eq.0h0v.s10.ddb727f0e570 from=translated src=- shape=314c40ee vocab=0bcd20f7
-/
lemma backward_forward : backward.comp forward = AlgHom.id ℂ (Polynomial A) := by
  apply Polynomial.algHom_ext'
  · apply Ideal.Quotient.algHom_ext ℂ
    apply MvPolynomial.algHom_ext
    intro i
    have h := congrArg (fun q : Point (Polynomial A) =>
      ![q.p, q.s, q.u, q.f, q.j] i) (congrArg Prod.fst backward_model)
    simp only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      forward_C, coefficientMap_mk, AlgHom.id_apply]
    fin_cases i <;>
      simpa [Point.eval, sourcePoint, Point.map, universal, p, s, u, F, J] using h
  · simpa using congrArg Prod.snd backward_model

/-- The explicit scalar-preserving polynomial cylinder isomorphism. -/
def equivalence : Polynomial A ≃ₐ[ℂ] P :=
  AlgEquiv.ofAlgHom forward backward forward_backward backward_forward

end ComplexCancellation.Cylinder

end

end OAI
