import Tengoku.NsP23.P23.Semigroup.AperyDualTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Intrinsic canonical dual and ordinary trace of the genuine chosen-base quotient
-/

namespace P23.Semigroup

noncomputable section

set_option maxHeartbeats 800000

variable {k : Type*} [Field k]
variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)

private abbrev Q (k : Type*) [Field k]
    (D : FourGeneratedNumericalSemigroup) (i : Fin 4) :=
  ChosenBaseQuotient (k := k) D i

private abbrev A (k : Type*) [Field k]
    (D : FourGeneratedNumericalSemigroup) (i : Fin 4) :=
  AperyArtin k D i

/-- Intrinsic canonical dual of the genuine quotient `k[Gamma]/(t^q)`.-/
abbrev ChosenBaseOmega (k : Type*) [Field k]
    (D : FourGeneratedNumericalSemigroup) (i : Fin 4) :=
  Module.Dual k (Q k D i)

namespace ChosenBaseOmega

variable {D i}

def act (q : Q k D i) (φ : ChosenBaseOmega k D i) :
    ChosenBaseOmega k D i where
  toFun r := φ (q * r)
  map_add' r r' := by simp [mul_add]
  map_smul' t r := by simp [mul_smul_comm]

instance : SMul (Q k D i) (ChosenBaseOmega k D i) := ⟨act⟩

/--
@isnad1 id=eq.0h6v.s10.c26703b86548 from=translated src=- shape=0d14d14c vocab=b14fe561
-/
@[simp] theorem smul_apply (q : Q k D i) (φ : ChosenBaseOmega k D i)
    (r : Q k D i) : (q • φ) r = φ (q * r) := rfl

instance : Module (Q k D i) (ChosenBaseOmega k D i) where
  one_smul φ := by
    apply LinearMap.ext
    intro r
    change φ (1 * r) = φ r
    rw [one_mul]
  mul_smul q r φ := by
    apply LinearMap.ext
    intro t
    change φ ((q * r) * t) = φ (r * (q * t))
    congr 1
    ac_rfl
  smul_zero q := by
    apply LinearMap.ext
    intro r
    rfl
  smul_add q φ ψ := by
    apply LinearMap.ext
    intro r
    rfl
  zero_smul φ := by
    apply LinearMap.ext
    intro r
    change φ (0 * r) = 0
    rw [zero_mul, map_zero]
  add_smul q r φ := by
    apply LinearMap.ext
    intro t
    change φ ((q + r) * t) = φ (q * t) + φ (r * t)
    rw [add_mul, map_add]

end ChosenBaseOmega

/-- Precomposition with the inverse chosen-base equivalence identifies the
two intrinsic canonical duals.-/
noncomputable def chosenBaseOmegaEquivAperyOmega :
    ChosenBaseOmega k D i ≃ₗ[k] AperyOmega k D i where
  toFun φ := φ.comp (chosenBaseEquivApery (k := k) D i).symm.toLinearMap
  invFun ψ := ψ.comp (chosenBaseEquivApery (k := k) D i).toLinearMap
  left_inv φ := by
    apply LinearMap.ext
    intro q
    exact congrArg φ ((chosenBaseEquivApery (k := k) D i).symm_apply_apply q)
  right_inv ψ := by
    apply LinearMap.ext
    intro a
    exact congrArg ψ ((chosenBaseEquivApery (k := k) D i).apply_symm_apply a)
  map_add' φ ψ := by apply LinearMap.ext; intro q; rfl
  map_smul' t φ := by apply LinearMap.ext; intro q; rfl

/--
@isnad1 id=eq.0h5v.s12.f67652ac6bc1 from=translated src=- shape=2cfe6cb7 vocab=f8233c0b
-/
@[simp] theorem chosenBaseOmegaEquivAperyOmega_apply_equiv
    (φ : ChosenBaseOmega k D i) (q : Q k D i) :
    chosenBaseOmegaEquivAperyOmega (k := k) D i φ
        (chosenBaseEquivApery (k := k) D i q) = φ q := by
  change φ ((chosenBaseEquivApery (k := k) D i).symm
    (chosenBaseEquivApery (k := k) D i q)) = φ q
  rw [(chosenBaseEquivApery (k := k) D i).symm_apply_apply]

/--
@isnad1 id=eq.0h5v.s12.546bf52b762f from=translated src=- shape=42cc9cfc vocab=9a21fb1a
-/
@[simp] theorem chosenBaseOmegaEquivAperyOmega_symm_apply
    (ψ : AperyOmega k D i) (q : Q k D i) :
    (chosenBaseOmegaEquivAperyOmega (k := k) D i).symm ψ q =
      ψ (chosenBaseEquivApery (k := k) D i q) := rfl

/--
@isnad1 id=eq.0h5v.s12.3e2d703055a2 from=translated src=- shape=e2c1d6a4 vocab=4b98153f
-/
theorem chosenBaseOmegaEquivAperyOmega_smul
    (q : Q k D i) (φ : ChosenBaseOmega k D i) :
    chosenBaseOmegaEquivAperyOmega (k := k) D i (q • φ) =
      chosenBaseEquivApery (k := k) D i q •
        chosenBaseOmegaEquivAperyOmega (k := k) D i φ := by
  apply LinearMap.ext
  intro a
  change φ (q * (chosenBaseEquivApery (k := k) D i).symm a) =
    φ ((chosenBaseEquivApery (k := k) D i).symm
      (chosenBaseEquivApery (k := k) D i q * a))
  congr 1
  simp

/--
@isnad1 id=eq.0h5v.s13.20db3a28adff from=translated src=- shape=271911a9 vocab=aa8a6e8c
-/
theorem chosenBaseOmegaEquivAperyOmega_symm_smul
    (a : A k D i) (ψ : AperyOmega k D i) :
    (chosenBaseOmegaEquivAperyOmega (k := k) D i).symm (a • ψ) =
      (chosenBaseEquivApery (k := k) D i).symm a •
        (chosenBaseOmegaEquivAperyOmega (k := k) D i).symm ψ := by
  apply (chosenBaseOmegaEquivAperyOmega (k := k) D i).injective
  rw [chosenBaseOmegaEquivAperyOmega_smul]
  simp

/-- Push a quotient canonical homomorphism to the Apéry model.-/
def pushChosenBaseCanonicalHom
    (F : ChosenBaseOmega k D i →ₗ[Q k D i] Q k D i) :
    AperyOmega k D i →ₗ[A k D i] A k D i where
  toFun ψ := chosenBaseEquivApery (k := k) D i
    (F ((chosenBaseOmegaEquivAperyOmega (k := k) D i).symm ψ))
  map_add' ψ ψ' := by simp
  map_smul' a ψ := by
    rw [chosenBaseOmegaEquivAperyOmega_symm_smul, F.map_smul]
    simp [smul_eq_mul]

/-- Pull an Apéry canonical homomorphism to the genuine quotient.-/
def pullChosenBaseCanonicalHom
    (F : AperyOmega k D i →ₗ[A k D i] A k D i) :
    ChosenBaseOmega k D i →ₗ[Q k D i] Q k D i where
  toFun φ := (chosenBaseEquivApery (k := k) D i).symm
    (F (chosenBaseOmegaEquivAperyOmega (k := k) D i φ))
  map_add' φ φ' := by simp
  map_smul' q φ := by
    rw [chosenBaseOmegaEquivAperyOmega_smul, F.map_smul]
    simp [smul_eq_mul]

/--
@isnad1 id=eq.0h4v.s10.8a4322c332f9 from=translated src=- shape=2ece820f vocab=373a97b2
-/
@[simp] theorem pull_pushChosenBaseCanonicalHom
    (F : ChosenBaseOmega k D i →ₗ[Q k D i] Q k D i) :
    pullChosenBaseCanonicalHom (k := k) D i
      (pushChosenBaseCanonicalHom (k := k) D i F) = F := by
  apply LinearMap.ext
  intro φ
  simp [pullChosenBaseCanonicalHom, pushChosenBaseCanonicalHom]

/--
@isnad1 id=eq.0h4v.s8.82f6b05c0139 from=translated src=- shape=2ece820f vocab=f942bce0
-/
@[simp] theorem push_pullChosenBaseCanonicalHom
    (F : AperyOmega k D i →ₗ[A k D i] A k D i) :
    pushChosenBaseCanonicalHom (k := k) D i
      (pullChosenBaseCanonicalHom (k := k) D i F) = F := by
  apply LinearMap.ext
  intro ψ
  simp [pullChosenBaseCanonicalHom, pushChosenBaseCanonicalHom]

/-- Ordinary trace on the genuine quotient, independently defined as the
supremum of ranges of all intrinsic canonical homomorphisms.-/
def ChosenBaseTraceSubmodule : Submodule (Q k D i) (Q k D i) :=
  ⨆ F : ChosenBaseOmega k D i →ₗ[Q k D i] Q k D i, F.range

/--
@isnad1 id=le.0h4v.s11.4d178ffc810d from=translated src=- shape=ae9259d4 vocab=def9f4a4
-/
theorem chosenBaseTrace_range_le
    (F : ChosenBaseOmega k D i →ₗ[Q k D i] Q k D i) :
    F.range ≤ ChosenBaseTraceSubmodule (k := k) D i :=
  le_iSup (fun G : ChosenBaseOmega k D i →ₗ[Q k D i] Q k D i => G.range) F

/-- Exact ordinary-trace membership transport.
@isnad1 id=iff.0h4v.s10.d47eddc4ebdd from=translated src=- shape=37ff0dce vocab=9d065d25
-/
theorem mem_chosenBaseTrace_iff_equiv_mem_aperyTrace (q : Q k D i) :
    q ∈ ChosenBaseTraceSubmodule (k := k) D i ↔
      chosenBaseEquivApery (k := k) D i q ∈
        AperyTraceSubmodule (k := k) D i := by
  let E := chosenBaseEquivApery (k := k) D i
  constructor
  · intro hq
    refine Submodule.iSup_induction
      (fun F : ChosenBaseOmega k D i →ₗ[Q k D i] Q k D i => F.range)
      (motive := fun x => E x ∈ AperyTraceSubmodule (k := k) D i)
      hq ?_ (by simp) ?_
    · intro F x hx
      rcases hx with ⟨φ, rfl⟩
      exact aperyTrace_range_le (k := k) D i
        (pushChosenBaseCanonicalHom (k := k) D i F)
        ⟨chosenBaseOmegaEquivAperyOmega (k := k) D i φ,
          by simp [pushChosenBaseCanonicalHom, E]⟩
    · intro x y hx hy
      simpa using (AperyTraceSubmodule (k := k) D i).add_mem hx hy
  · intro hq
    have hback : E.symm (E q) ∈ ChosenBaseTraceSubmodule (k := k) D i := by
      refine Submodule.iSup_induction
        (fun F : AperyOmega k D i →ₗ[A k D i] A k D i => F.range)
        (motive := fun x => E.symm x ∈ ChosenBaseTraceSubmodule (k := k) D i)
        hq ?_ (by simp) ?_
      · intro F x hx
        rcases hx with ⟨ψ, rfl⟩
        exact chosenBaseTrace_range_le (k := k) D i
          (pullChosenBaseCanonicalHom (k := k) D i F)
          ⟨(chosenBaseOmegaEquivAperyOmega (k := k) D i).symm ψ,
            by simp [pullChosenBaseCanonicalHom, E]⟩
      · intro x y hx hy
        simpa using (ChosenBaseTraceSubmodule (k := k) D i).add_mem hx hy
    simpa [E] using hback

/-- Intrinsic local nearly-Gorenstein condition on the genuine quotient.-/
def ChosenBaseNearlyGorenstein : Prop := by
  letI := chosenBaseIsLocalRing (k := k) D i
  exact IsLocalRing.maximalIdeal (Q k D i) ≤
    ChosenBaseTraceSubmodule (k := k) D i

/--
@isnad1 id=iff.0h3v.s4.4abf38600d80 from=translated src=- shape=faadfc7c vocab=339169c1
-/
theorem chosenBaseNearlyGorenstein_iff_aperyNearlyGorenstein :
    ChosenBaseNearlyGorenstein (k := k) D i ↔
      AperyNearlyGorenstein (k := k) D i := by
  let E := chosenBaseEquivApery (k := k) D i
  unfold ChosenBaseNearlyGorenstein AperyNearlyGorenstein
  letI := chosenBaseIsLocalRing (k := k) D i
  rw [chosenBaseMaximalIdeal_eq_augmentationIdeal (k := k) D i]
  constructor
  · intro hng a ha
    let q : Q k D i := E.symm a
    have hqaug : q ∈ chosenBaseAugmentationIdeal (k := k) D i := by
      change E q ∈ aperyAugmentationIdeal (k := k) D i
      simpa [q, E] using ha
    have hqt := hng hqaug
    have ht := (mem_chosenBaseTrace_iff_equiv_mem_aperyTrace
      (k := k) D i q).1 hqt
    simpa [q, E] using ht
  · intro hng q hq
    have hEq : E q ∈ aperyAugmentationIdeal (k := k) D i := hq
    have hEt := hng hEq
    exact (mem_chosenBaseTrace_iff_equiv_mem_aperyTrace
      (k := k) D i q).2 hEt

/-- Main Run22 bridge.
@isnad1 id=chosenba.1h3v.s4.f34ea1edaac3 from=translated src=- shape=59ed7ea6 vocab=f5c4966e
-/
theorem semigroupNearlyGorenstein_to_chosenBaseNearlyGorenstein
    (hng : SemigroupNearlyGorenstein D) :
    ChosenBaseNearlyGorenstein (k := k) D i :=
  (chosenBaseNearlyGorenstein_iff_aperyNearlyGorenstein
    (k := k) D i).2
      (semigroupNearlyGorenstein_to_aperyNearlyGorenstein
        (k := k) D i hng)

/--
@isnad1 id=and.2h3v.s5.8ddc251932fc from=translated src=- shape=f342c71f vocab=f159b0bf
-/
theorem semigroup_type_three_ng_gives_chosenBase_type_three_ng
    (htype : D.semigroupType = 3) (hng : SemigroupNearlyGorenstein D) :
    chosenBaseType (k := k) D i = 3 ∧
      ChosenBaseNearlyGorenstein (k := k) D i :=
  ⟨(chosenBaseType_eq_semigroupType (k := k) D i).trans htype,
    semigroupNearlyGorenstein_to_chosenBaseNearlyGorenstein
      (k := k) D i hng⟩

/-- Scope-explicit Run22 bridge package.  It contains no Betti, H-L5, rho, or
source-selection statement.-/
structure ChosenBaseNGBridge : Prop where
  ngVectorInterface : SemigroupNearlyGorenstein D ↔
    ∀ j : Fin 4, ∃ f : D.PseudoFrobeniusIndex,
      NGWitnessForGenerator D j f
  aperyOrdinaryTrace : AperyTraceSubmodule (k := k) D i =
    ⨆ F : AperyOmega k D i →ₗ[A k D i] A k D i, F.range
  semigroupToAperyNG : SemigroupNearlyGorenstein D →
    AperyNearlyGorenstein (k := k) D i
  chosenBaseOrdinaryTrace : ChosenBaseTraceSubmodule (k := k) D i =
    ⨆ F : ChosenBaseOmega k D i →ₗ[Q k D i] Q k D i, F.range
  traceTransport : ∀ q : Q k D i,
    q ∈ ChosenBaseTraceSubmodule (k := k) D i ↔
      chosenBaseEquivApery (k := k) D i q ∈
        AperyTraceSubmodule (k := k) D i
  ngTransport : ChosenBaseNearlyGorenstein (k := k) D i ↔
    AperyNearlyGorenstein (k := k) D i
  semigroupToChosenBaseNG : SemigroupNearlyGorenstein D →
    ChosenBaseNearlyGorenstein (k := k) D i

/--
@isnad1 id=chosenba.0h3v.s4.923579fe4ef1 from=translated src=- shape=9b42ccea vocab=f30d9642
-/
theorem chosenBaseNGBridge : ChosenBaseNGBridge (k := k) D i where
  ngVectorInterface := semigroupNearlyGorenstein_iff_ngVector D
  aperyOrdinaryTrace := rfl
  semigroupToAperyNG := semigroupNearlyGorenstein_to_aperyNearlyGorenstein
    (k := k) D i
  chosenBaseOrdinaryTrace := rfl
  traceTransport := mem_chosenBaseTrace_iff_equiv_mem_aperyTrace
    (k := k) D i
  ngTransport := chosenBaseNearlyGorenstein_iff_aperyNearlyGorenstein
    (k := k) D i
  semigroupToChosenBaseNG :=
    semigroupNearlyGorenstein_to_chosenBaseNearlyGorenstein (k := k) D i

end

end P23.Semigroup
