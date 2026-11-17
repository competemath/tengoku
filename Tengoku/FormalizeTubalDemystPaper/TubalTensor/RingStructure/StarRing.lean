import Tengoku.FormalizeTubalDemystPaper.TubalTensor.RingStructure.CommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/RingStructure/StarRing.lean
  ⋆_M-conjugate, *-ring instance.

  The ⋆_M-conjugation is defined as: a* := M⁻¹(conj(Ma))
  This makes K_M into a *-ring.
-/

namespace TubalTensor

open Complex Matrix

variable {n : ℕ}

/-! ## Complex-level conjugation: starConjC -/

/-- The ⋆_M-conjugation on complex vectors: M⁻¹(conj(Ma)).-/
noncomputable def starConjC (td : TubalData n) (a : Fin n → ℂ) : Fin n → ℂ :=
  td.applyMinv (vecConj (td.applyM a))

/-- The ⋆_M-conjugation on real vectors.-/
noncomputable def starConjM (td : TubalData n) (a : Fin n → ℝ) : Fin n → ℝ :=
  vecRe (starConjC td (toComplex a))

/-! ## Realness: starConjC maps real vectors to real vectors -/

/-- The conjugate of a vector with real-paired structure also has real-paired structure.-/
private theorem vecConj_applyM_hasPairedStructure (td : TubalData n) (a : Fin n → ℝ) :
    HasRealPairedStructure td (vecConj (td.applyM (toComplex a))) := by
  have hps := applyM_toComplex_hasPairedStructure td a
  constructor
  · intro i hreal
    simp only [vecConj_apply]
    have him := hps.1 i hreal
    rw [starRingEnd_apply, star_def, Complex.conj_im, neg_eq_zero]
    exact him
  · intro i k hki hconj
    -- Need: vecConj v k = conj(vecConj v i) where v = Ma
    -- i.e., conj(v k) = conj(conj(v i))
    -- From hps.2: v k = conj(v i), so conj(v k) = conj(conj(v i)). Done.
    show starRingEnd ℂ (td.applyM (toComplex a) k) =
      starRingEnd ℂ (starRingEnd ℂ (td.applyM (toComplex a) i))
    congr 1; exact hps.2 i k hki hconj

/-- starConjC maps real vectors to real vectors.
@isnad1 id=isrealve.0h3v.s4.7015516dbc8f from=translated src=- shape=01803419 vocab=e14d0eb7
-/
theorem starConjC_real (td : TubalData n) (a : Fin n → ℝ) :
    IsRealVec (starConjC td (toComplex a)) :=
  applyMinv_real_of_pairedStructure td _ (vecConj_applyM_hasPairedStructure td a)

/-- The real ⋆_M-conjugation equals the complex version on real inputs.
@isnad1 id=eq.0h3v.s4.01068711c910 from=translated src=- shape=16fde087 vocab=84848658
-/
theorem starConjM_eq_starConjC (td : TubalData n) (a : Fin n → ℝ) :
    toComplex (starConjM td a) = starConjC td (toComplex a) :=
  toComplex_vecRe _ (starConjC_real td a)

/-! ## StarRing axiom proofs -/

/-- Complex-level: starConjC is involutive.-/
private theorem starConjC_involutive (td : TubalData n) (a : Fin n → ℂ) :
    starConjC td (starConjC td a) = a := by
  unfold starConjC
  rw [td.applyM_applyMinv]
  -- Need: M⁻¹(conj(conj(Ma))) = a
  -- conj(conj(Ma)) = Ma, so M⁻¹(Ma) = a
  have : vecConj (vecConj (td.applyM a)) = td.applyM a := by
    ext i
    show starRingEnd ℂ (starRingEnd ℂ (td.applyM a i)) = td.applyM a i
    rw [starRingEnd_apply, starRingEnd_apply, star_star]
  rw [this]
  exact td.applyMinv_applyM a

/-- Complex-level: starConjC is additive.-/
private theorem starConjC_add (td : TubalData n) (a b : Fin n → ℂ) :
    starConjC td (a + b) = starConjC td a + starConjC td b := by
  unfold starConjC
  rw [td.applyM_add]
  -- conj distributes over +
  have : vecConj (td.applyM a + td.applyM b) = vecConj (td.applyM a) + vecConj (td.applyM b) := by
    ext i; simp [vecConj_apply, map_add]
  rw [this]
  exact td.applyMinv_add _ _

/-- Complex-level: starConjC is antimultiplicative w.r.t. starMC.
    Since the ring is commutative, this is the same as being multiplicative.-/
private theorem starConjC_mul (td : TubalData n) (a b : Fin n → ℂ) :
    starConjC td (starMC td a b) = starMC td (starConjC td a) (starConjC td b) := by
  unfold starConjC starMC
  -- LHS: M⁻¹(conj(M(M⁻¹(Ma ∘ₕ Mb))))
  -- = M⁻¹(conj(Ma ∘ₕ Mb))           [M * M⁻¹ = I]
  -- = M⁻¹(conj(Ma) ∘ₕ conj(Mb))     [conj distributes over ∘ₕ]
  rw [td.applyM_applyMinv]
  -- RHS: M⁻¹(M(M⁻¹(conj(Ma))) ∘ₕ M(M⁻¹(conj(Mb))))
  -- = M⁻¹(conj(Ma) ∘ₕ conj(Mb))
  rw [td.applyM_applyMinv, td.applyM_applyMinv]
  -- Now both sides are M⁻¹(vecConj(Ma ∘ₕ Mb)) vs M⁻¹(vecConj(Ma) ∘ₕ vecConj(Mb))
  congr 1
  ext i
  simp [vecConj_apply, vecHadamard_apply, map_mul]

/-! ## Lift to real operations -/

/--
@isnad1 id=eq.0h3v.s4.b58e8de4bee0 from=translated src=- shape=e025fdef vocab=75a00cca
-/
theorem starConjM_involutive (td : TubalData n) (a : Fin n → ℝ) :
    starConjM td (starConjM td a) = a := by
  apply toComplex_injective
  rw [starConjM_eq_starConjC, starConjM_eq_starConjC]
  exact starConjC_involutive td _

/--
@isnad1 id=eq.0h4v.s6.58c89c96faea from=translated src=- shape=0c3f930b vocab=531d6f14
-/
theorem starConjM_add (td : TubalData n) (a b : Fin n → ℝ) :
    starConjM td (a + b) = starConjM td a + starConjM td b := by
  apply toComplex_injective
  rw [starConjM_eq_starConjC, toComplex_add, starConjC_add, toComplex_add,
      starConjM_eq_starConjC, starConjM_eq_starConjC]

/--
@isnad1 id=eq.0h4v.s5.233700b821bd from=translated src=- shape=d1055ae2 vocab=fe7a0347
-/
theorem starConjM_mul (td : TubalData n) (a b : Fin n → ℝ) :
    starConjM td (starM td a b) = starM td (starConjM td a) (starConjM td b) := by
  apply toComplex_injective
  rw [starConjM_eq_starConjC, starM_eq_starMC, starConjC_mul,
      starM_eq_starMC, starConjM_eq_starConjC, starConjM_eq_starConjC]

/-! ## StarRing instance for KM -/

namespace KM

variable {td : TubalData n}

/-- The star operation on KM is ⋆_M-conjugation.-/
noncomputable instance instStar : Star (KM n td) :=
  ⟨fun a => ofFun (starConjM td (toFun a))⟩

/--
@isnad1 id=eq.0h3v.s5.c42d6ba3112b from=translated src=- shape=0b342eea vocab=f8eca635
-/
@[simp] theorem toFun_star (a : KM n td) :
    toFun (star a) = starConjM td (toFun a) := rfl

/-- KM is a *-ring under ⋆_M-conjugation (Section 3.3).-/
noncomputable instance instStarRing : StarRing (KM n td) where
  star_involutive a := by
    show ofFun _ = _
    exact congr_arg ofFun (starConjM_involutive td _)
  star_mul a b := by
    show ofFun _ = ofFun _
    -- star(a * b) = star(b) * star(a)
    -- Since the ring is commutative, this is star(a) * star(b)
    have h := starConjM_mul td (toFun a) (toFun b)
    -- h : starConjM td (starM td a b) = starM td (starConjM a) (starConjM b)
    -- But star(a * b) = star(b) * star(a) = starM(star(b), star(a))
    -- = starM(starConj b, starConj a) = starM(starConj a, starConj b) by commutativity
    -- = starConjM(starM a b)
    exact congr_arg ofFun (h.trans (starM_comm td _ _))
  star_add a b := by
    show ofFun _ = ofFun _ + ofFun _
    exact congr_arg ofFun (starConjM_add td (toFun a) (toFun b))

end KM

end TubalTensor
