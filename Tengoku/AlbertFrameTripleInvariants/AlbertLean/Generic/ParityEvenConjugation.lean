import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.RationalEvenFamilyInverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms clifford_even_conjugate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms evenV_conjugate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceEvenAut_conjugate_apply` (it only prints; the queue checks the axioms of every declaration). -/

/-! Conjugation covariance for the normalized source even action, proved on
the complete source carrier. -/
noncomputable section
namespace AlbertLean.Triality.ParityEvenConjugation

open ExteriorSix CoordinateTensor StructuredCubic StructuredAdjoint
open SourceCliffordLinear SourceCliffordIdentities SourceCliffordReflection
open SourceEvenReflections SourceEvenAutomorphism SourceEvenTriality
open SourceVectorPairReflection RationalEvenFamilyInverse

universe u
variable {K : Type u} [Field K] [CharZero K]

/--
@isnad1 id=injectiv.1h2v.s5.32366652c6b9 from=translated src=- shape=e6bd6910 vocab=6aee5c18
-/
theorem reflectV_injective (a : VCoord K) (ha : nV a ≠ 0) :
    Function.Injective (reflectV a) := by
  intro x y h
  have := congrArg (reflectV a) h
  simpa only [reflectV_involutive a x ha,
    reflectV_involutive a y ha] using this

/--
@isnad1 id=eq.1h4v.s6.afdb193e4522 from=translated src=- shape=341e80f5 vocab=ae3db609
-/
theorem reflectV_covariant (a b v : VCoord K) (ha : nV a ≠ 0) :
    reflectV (reflectV a b) (reflectV a v) =
      reflectV a (reflectV b v) := by
  apply reflectV_injective a ha
  rw [reflectV_reflected_conjugate a b (reflectV a v) ha,
    reflectV_involutive a v ha,
    reflectV_involutive a (reflectV b v) ha]

/--
@isnad1 id=eq.2h5v.s6.07316943c6a4 from=translated src=- shape=b28fb649 vocab=4dc2d511
-/
theorem evenV_reflect_covariant (e c A v : VCoord K)
    (he : nV e ≠ 0) (hc : nV c ≠ 0) :
    reflectV (evenV e c A) (evenV e c v) =
      evenV e c (reflectV A v) := by
  simp only [evenV]
  rw [reflectV_covariant e (reflectV c A) (reflectV c v) he,
    reflectV_covariant c A v hc]

/--
@isnad1 id=eq.2h6v.s6.4045286ce1dd from=translated src=- shape=5a82b055 vocab=4dc2d511
-/
theorem evenV_conjugate (e c A B v : VCoord K)
    (he : nV e ≠ 0) (hc : nV c ≠ 0) :
    evenV e (reflectV e c)
      (evenV (evenV e c A) (evenV e c B) (evenV e c v)) =
      evenV A B v := by
  rw [evenV_reflected_reverse e c _ he]
  have hcovB := evenV_reflect_covariant e c B v he hc
  have hcovA := evenV_reflect_covariant e c A (reflectV B v) he hc
  simp only [evenV] at hcovB hcovA ⊢
  rw [hcovB, hcovA]
  rw [reflectV_involutive e _ he, reflectV_involutive c _ hc]

/-- Clifford intertwining gives conjugation of a two-vector product by the
unit-norm even lift.
@isnad1 id=eq.2h5v.s14.f17ffd40ddc8 from=translated src=- shape=49121c33 vocab=72755147
-/
theorem clifford_even_conjugate (e c A B : VCoord K)
    (he : nV e = 1) (hc : nV c = 1) :
    (C c * C e) * (C (evenV e c A) * C (evenV e c B)) *
        (C e * C c) = C A * C B := by
  have he0 : nV e ≠ 0 := by simpa [he]
  have hc0 : nV c ≠ 0 := by simpa [hc]
  have hA := C_evenV_intertwine e c A he0 hc0
  have hB := C_evenV_intertwine e c B he0 hc0
  let U := C e * C c
  let V := C c * C e
  change U * C A = C (evenV e c A) * U at hA
  change U * C B = C (evenV e c B) * U at hB
  have hinv : V * U = 1 := by
    change (C c * C e) * (C e * C c) = 1
    calc
      (C c * C e) * (C e * C c) = C c * (C e * C e) * C c := by
        noncomm_ring
      _ = 1 := by
        rw [C_square, he, one_smul, mul_one, C_square, hc, one_smul]
  calc
    (C c * C e) * (C (evenV e c A) * C (evenV e c B)) * (C e * C c) =
        V * C (evenV e c A) * (C (evenV e c B) * U) := by
          dsimp only [U, V]
          noncomm_ring
    _ = V * C (evenV e c A) * (U * C B) := by rw [← hB]
    _ = V * (C (evenV e c A) * U) * C B := by noncomm_ring
    _ = V * (U * C A) * C B := by rw [← hA]
    _ = (V * U) * (C A * C B) := by noncomm_ring
    _ = C A * C B := by rw [hinv, one_mul]

/-- A small typed bridge for moving a scalar through the `C → S` Clifford
action without unfolding its coordinate implementation.-/
private theorem sourceMuS_smul_input (v : VCoord K) (a : K) (d : CCoord K) :
    sourceMuS (a • d) v = a • sourceMuS d v := by
  exact (muSLinear v).map_smul a d

/-- A small typed bridge for moving a scalar through the `S → C` Clifford
action without unfolding its coordinate implementation.-/
private theorem sourceMuC_smul_input (v : VCoord K) (a : K) (s : SCoord K) :
    sourceMuC v (a • s) = a • sourceMuC v s := by
  exact (muCLinear v).map_smul a s

set_option maxHeartbeats 600000 in
/--
@isnad1 id=eq.2h7v.s7.fc98cea63ef5 from=translated src=- shape=e3d381b1 vocab=47c86819
-/
theorem evenS_conjugate (e c A B : VCoord K) (rho : K)
    (he : nV e = 1) (hc : nV c = 1) (s : SCoord K) :
    evenS e (reflectV e c) (-1)
      (evenS (evenV e c A) (evenV e c B) rho
        (evenS e c 1 s)) = evenS A B rho s := by
  rw [evenS_reflected_neg_reverse e c 1 (by simpa [he]) (by norm_num)]
  have h := LinearMap.congr_fun (clifford_even_conjugate e c A B he hc) (s, 0)
  have hs := congrArg Prod.fst h
  simp only [Module.End.mul_apply, C_apply] at hs
  simp only [evenS, inv_one, one_smul]
  rw [sourceMuC_smul_input, sourceMuS_smul_input, hs]

set_option maxHeartbeats 600000 in
/--
@isnad1 id=eq.2h7v.s7.b1b52e8e820d from=translated src=- shape=e3d381b1 vocab=5ff1241a
-/
theorem evenC_conjugate (e c A B : VCoord K) (rho : K)
    (he : nV e = 1) (hc : nV c = 1) (d : CCoord K) :
    evenC e (reflectV e c) (-1)
      (evenC (evenV e c A) (evenV e c B) rho
        (evenC e c 1 d)) = evenC A B rho d := by
  rw [evenC_reflected_neg_reverse e c 1 (by simpa [he]) (by norm_num)]
  have h := LinearMap.congr_fun (clifford_even_conjugate e c A B he hc) (0, d)
  have hd := congrArg Prod.snd h
  simp only [Module.End.mul_apply, C_apply] at hd
  simp only [evenC, inv_one, one_smul]
  rw [sourceMuS_smul_input, sourceMuC_smul_input, hd]

/-- Opaque application bridge: expose only the six carrier components, not
the cubic-automorphism proof fields packaged by `sourceEvenAut`.
@isnad1 id=eq.4h5v.s9.0674f2f7ee41 from=translated src=- shape=ac051a58 vocab=9ff69b90
-/
@[simp] theorem sourceEvenAut_linear_apply
    (a b : VCoord K) (rho : K)
    (ha : nV a ≠ 0) (hb : nV b ≠ 0)
    (hr : rho ^ 2 = nV a * nV b) (hr0 : rho ≠ 0) (x : JCoord K) :
    (sourceEvenAut a b rho ha hb hr hr0).linear x =
      { d1 := x.d1, d2 := x.d2, d3 := x.d3
        v := evenV a b x.v
        s := evenS a b rho x.s
        c := evenC a b rho x.c } := by
  exact evenJEquiv_apply a b rho ha hb hr hr0 x

set_option maxHeartbeats 800000 in
/--
@isnad1 id=other.6h7v.s11.435bd9e0a0de from=translated src=- shape=3b68e251 vocab=324d1153
-/
theorem sourceEvenAut_conjugate_apply
    (e c A B : VCoord K) (rho : K)
    (he : nV e = 1) (hc : nV c = 1)
    (hA : nV A ≠ 0) (hB : nV B ≠ 0)
    (hr : rho ^ 2 = nV A * nV B) (hr0 : rho ≠ 0)
    (x : JCoord K) :
    let he0 : nV e ≠ 0 := by simpa [he]
    let hc0 : nV c ≠ 0 := by simpa [hc]
    let hrc : nV (reflectV e c) ≠ 0 := by
      simpa [nV_reflectV e c he0] using hc0
    let hAc : nV (evenV e c A) ≠ 0 := by
      simpa [nV_evenV e c A he0 hc0] using hA
    let hBc : nV (evenV e c B) ≠ 0 := by
      simpa [nV_evenV e c B he0 hc0] using hB
    let hminus : (-1 : K) ^ 2 = nV e * nV (reflectV e c) := by
      rw [he, one_mul, nV_reflectV e c he0, hc]
      norm_num
    let hone : (1 : K) ^ 2 = nV e * nV c := by rw [he, hc]; norm_num
    let hrcAB : rho ^ 2 = nV (evenV e c A) * nV (evenV e c B) := by
      simpa [nV_evenV e c A he0 hc0, nV_evenV e c B he0 hc0] using hr
    (sourceEvenAut e (reflectV e c) (-1) he0 hrc hminus (by norm_num)).linear
      ((sourceEvenAut (evenV e c A) (evenV e c B) rho hAc hBc hrcAB hr0).linear
        ((sourceEvenAut e c 1 he0 hc0 hone (by norm_num)).linear x)) =
      (sourceEvenAut A B rho hA hB hr hr0).linear x := by
  intro he0 hc0 hrc hAc hBc hminus hone hrcAB
  simp only [sourceEvenAut_linear_apply]
  apply JCoord.ext
  · rfl
  · rfl
  · rfl
  · exact evenV_conjugate e c A B x.v he0 hc0
  · exact evenS_conjugate e c A B rho he hc x.s
  · exact evenC_conjugate e c A B rho he hc x.c

end AlbertLean.Triality.ParityEvenConjugation
