import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u v

namespace groupCohomology

namespace Kummer

section Unbundled

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/--
@isnad1 id=eq.0h4v.s9.88fcd5cdb15e from=translated src=- shape=f9bd9155 vocab=7bf8e047
-/
@[simp]
lemma val_smul_units (σ : L ≃ₐ[K] L) (α : Lˣ) : ((σ • α : Lˣ) : L) = σ (α : L) :=
  rfl

/--
@isnad1 id=eq.0h5v.s10.af31c6f45a8e from=translated src=- shape=67132357 vocab=3d5796b2
-/
lemma smul_units_div (σ : L ≃ₐ[K] L) (x y : Lˣ) : σ • (x / y) = σ • x / σ • y := by
  ext
  simp only [val_smul_units, Units.val_div_eq_div_val, map_div₀]

/--
@isnad1 id=eq.0h5v.s10.15110cf1cb2a from=translated src=- shape=fb8dd901 vocab=99e94061
-/
lemma smul_units_pow (σ : L ≃ₐ[K] L) (x : Lˣ) (n : ℕ) : σ • (x ^ n) = (σ • x) ^ n := by
  ext
  simp only [val_smul_units, Units.val_pow_eq_pow_val, map_pow]

/--
@isnad1 id=eq.1h4v.s9.b0a7b8943691 from=translated src=- shape=e9e7bcac vocab=3e2cd587
-/
lemma smul_units_eq_self_of_mem_range (σ : L ≃ₐ[K] L) {α : Lˣ}
    (hα : (α : L) ∈ Set.range (algebraMap K L)) : σ • α = α := by
  obtain ⟨b, hb⟩ := hα
  ext
  rw [val_smul_units, ← hb, AlgEquiv.commutes]

def kummerCocycle (α : Lˣ) (σ : L ≃ₐ[K] L) : Lˣ :=
  σ • α / α

/--
@isnad1 id=eq.0h4v.s9.ed4bd6e8fe77 from=translated src=- shape=7e53bab8 vocab=5f67566e
-/
lemma kummerCocycle_apply (α : Lˣ) (σ : L ≃ₐ[K] L) :
    kummerCocycle α σ = σ • α / α := rfl

/--
@isnad1 id=ismulcoc.0h3v.s9.6a8758e78b48 from=translated src=- shape=e8fe120f vocab=b698cd31
-/
theorem isMulCocycle₁_kummerCocycle (α : Lˣ) :
    IsMulCocycle₁ (kummerCocycle (K := K) α) := by
  intro σ τ
  show (σ * τ) • α / α = σ • (τ • α / α) * (σ • α / α)
  rw [mul_smul, smul_units_div, div_mul_div_cancel]

/--
@isnad1 id=eq.0h5v.s7.bdb98db07d41 from=translated src=- shape=e0ee5ba7 vocab=3a039001
-/
theorem kummerCocycle_mul (α β : Lˣ) (σ : L ≃ₐ[K] L) :
    kummerCocycle (α * β) σ = kummerCocycle α σ * kummerCocycle β σ := by
  show σ • (α * β) / (α * β) = (σ • α / α) * (σ • β / β)
  rw [smul_mul', mul_div_mul_comm]

/--
@isnad1 id=eq.1h6v.s8.889c9dc92e0c from=translated src=- shape=64bb5b74 vocab=1bab28f5
-/
theorem kummerCocycle_pow_eq_one {p : ℕ} {a : K} {α : Lˣ}
    (hα : algebraMap K L a = (α : L) ^ p) (σ : L ≃ₐ[K] L) :
    kummerCocycle α σ ^ p = 1 := by
  have hmem : ((α ^ p : Lˣ) : L) ∈ Set.range (algebraMap K L) :=
    ⟨a, by rw [hα, Units.val_pow_eq_pow_val]⟩
  rw [kummerCocycle_apply, div_pow, ← smul_units_pow,
    smul_units_eq_self_of_mem_range σ hmem, div_self']

/--
@isnad1 id=and.2h6v.s10.66fb7bc1ad9a from=translated src=- shape=407cb26e vocab=0af54d28
-/
theorem kummerCocycle_div_kummerCocycle_of_pow_eq {p : ℕ} {a : K} {α β : Lˣ}
    (hα : algebraMap K L a = (α : L) ^ p) (hβ : algebraMap K L a = (β : L) ^ p) :
    (α / β) ^ p = 1 ∧
      ∀ σ : L ≃ₐ[K] L, kummerCocycle α σ / kummerCocycle β σ = σ • (α / β) / (α / β) := by
  refine ⟨?_, fun σ => ?_⟩
  · rw [div_pow, div_eq_one]
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← hα, ← hβ]
  · rw [kummerCocycle_apply, kummerCocycle_apply, smul_units_div, div_div_div_comm]

/--
@isnad1 id=mem.1h5v.s9.7d03d555735e from=translated src=- shape=df4afec3 vocab=8daa5c62
-/
lemma smul_mem_rootsOfUnity {p : ℕ} (σ : L ≃ₐ[K] L) {ζ : Lˣ} (hζ : ζ ∈ rootsOfUnity p L) :
    σ • ζ ∈ rootsOfUnity p L := by
  rw [mem_rootsOfUnity] at hζ ⊢
  rw [← smul_units_pow, hζ, smul_one]

instance instMulDistribMulActionRootsOfUnity (p : ℕ) :
    MulDistribMulAction (L ≃ₐ[K] L) (rootsOfUnity p L) where
  smul σ ζ := ⟨σ • (ζ : Lˣ), smul_mem_rootsOfUnity σ ζ.2⟩
  one_smul ζ := Subtype.ext (one_smul _ (ζ : Lˣ))
  mul_smul σ τ ζ := Subtype.ext (mul_smul σ τ (ζ : Lˣ))
  smul_mul σ ζ η := Subtype.ext (smul_mul' σ (ζ : Lˣ) (η : Lˣ))
  smul_one σ := Subtype.ext (smul_one σ)

/--
@isnad1 id=eq.0h5v.s11.f3664f421e13 from=translated src=- shape=30b07281 vocab=3dc22845
-/
@[simp]
lemma coe_smul_rootsOfUnity {p : ℕ} (σ : L ≃ₐ[K] L) (ζ : rootsOfUnity p L) :
    ((σ • ζ : rootsOfUnity p L) : Lˣ) = σ • (ζ : Lˣ) :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.3121590d78f0 from=translated src=- shape=88223943 vocab=2449d4e6
-/
lemma coe_div_rootsOfUnity {p : ℕ} (ζ η : rootsOfUnity p L) :
    ((ζ / η : rootsOfUnity p L) : Lˣ) = (ζ : Lˣ) / (η : Lˣ) :=
  rfl

end Unbundled

section RepLevel

variable {K L : Type} [Field K] [Field L] [Algebra K L]

noncomputable abbrev kummerRep (K L : Type) [Field K] [Field L] [Algebra K L] (p : ℕ) :
    Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (rootsOfUnity p L)

variable {p : ℕ} {a : Kˣ} {α : Lˣ}

def kummerCocycleRoots (hα : algebraMap K L (a : K) = (α : L) ^ p) (σ : L ≃ₐ[K] L) :
    rootsOfUnity p L :=
  ⟨kummerCocycle α σ, kummerCocycle_pow_eq_one hα σ⟩

/--
@isnad1 id=eq.1h6v.s8.014a9aa417ae from=translated src=- shape=cb91385b vocab=b4cd3c56
-/
@[simp]
lemma coe_kummerCocycleRoots (hα : algebraMap K L (a : K) = (α : L) ^ p) (σ : L ≃ₐ[K] L) :
    (kummerCocycleRoots hα σ : Lˣ) = kummerCocycle α σ :=
  rfl

/--
@isnad1 id=ismulcoc.1h5v.s10.e8a822a57629 from=translated src=- shape=74bdfb58 vocab=a201c6ef
-/
theorem isMulCocycle₁_kummerCocycleRoots (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    IsMulCocycle₁ (kummerCocycleRoots hα) :=
  fun σ τ => Subtype.ext (isMulCocycle₁_kummerCocycle α σ τ)

noncomputable def kummerCocycles (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    cocycles₁ (kummerRep K L p) :=
  cocyclesOfIsMulCocycle₁ (isMulCocycle₁_kummerCocycleRoots hα)

/--
@isnad1 id=eq.1h5v.s12.e63309935923 from=translated src=- shape=9b701513 vocab=193872b3
-/
lemma coe_kummerCocycles (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    ⇑(kummerCocycles hα) = Additive.ofMul ∘ kummerCocycleRoots hα :=
  rfl

noncomputable def kummerClass (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    H1 (kummerRep K L p) :=
  H1π (kummerRep K L p) (kummerCocycles hα)

/--
@isnad1 id=eq.2h6v.s8.adf30a8bf47c from=translated src=- shape=bed26cbf vocab=aaed5cf2
-/
theorem kummerClass_eq_of_pow_eq {β : Lˣ} (hα : algebraMap K L (a : K) = (α : L) ^ p)
    (hβ : algebraMap K L (a : K) = (β : L) ^ p) :
    kummerClass hα = kummerClass hβ := by
  obtain ⟨hpow, hcob⟩ := kummerCocycle_div_kummerCocycle_of_pow_eq hα hβ
  rw [kummerClass, kummerClass, H1π_eq_iff]
  exact (coboundariesOfIsMulCoboundary₁
    (f := fun σ => kummerCocycleRoots hα σ / kummerCocycleRoots hβ σ)
    ⟨⟨α / β, hpow⟩, fun σ => Subtype.ext (hcob σ).symm⟩).2

/--
@isnad1 id=eq.2h7v.s9.700c66245855 from=translated src=- shape=c5cd9179 vocab=f090e0d9
-/
theorem mul_pow_eq {b : Kˣ} {β : Lˣ} (hα : algebraMap K L (a : K) = (α : L) ^ p)
    (hβ : algebraMap K L (b : K) = (β : L) ^ p) :
    algebraMap K L ((a * b : Kˣ) : K) = ((α * β : Lˣ) : L) ^ p := by
  rw [Units.val_mul, map_mul, hα, hβ, Units.val_mul, mul_pow]

/--
@isnad1 id=eq.2h7v.s9.18eb82d67370 from=translated src=- shape=b01380e5 vocab=560c3598
-/
theorem kummerClass_mul {b : Kˣ} {β : Lˣ} (hα : algebraMap K L (a : K) = (α : L) ^ p)
    (hβ : algebraMap K L (b : K) = (β : L) ^ p) :
    kummerClass (mul_pow_eq hα hβ) = kummerClass hα + kummerClass hβ := by
  rw [kummerClass, kummerClass, kummerClass, ← map_add]
  congr 1
  ext σ
  exact congrArg Additive.ofMul (Subtype.ext (kummerCocycle_mul α β σ))

/--
@isnad1 id=eq.1h5v.s8.76693ec2926b from=translated src=- shape=8b523e48 vocab=cb24621d
-/
theorem inv_pow_eq {a : Kˣ} {α : Lˣ} (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    algebraMap K L ((a⁻¹ : Kˣ) : K) = ((α⁻¹ : Lˣ) : L) ^ p := by
  rw [Units.val_inv_eq_inv_val, map_inv₀, hα, Units.val_inv_eq_inv_val, inv_pow]

def powerSubgroup (K L : Type) [Field K] [Field L] [Algebra K L] (p : ℕ) : Subgroup Kˣ where
  carrier := {a : Kˣ | ∃ α : Lˣ, algebraMap K L (a : K) = (α : L) ^ p}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := fun ⟨α, hα⟩ ⟨β, hβ⟩ => ⟨α * β, mul_pow_eq hα hβ⟩
  inv_mem' := fun ⟨α, hα⟩ => ⟨α⁻¹, inv_pow_eq hα⟩

/--
@isnad1 id=iff.0h4v.s8.ba6241d01d21 from=translated src=- shape=bb0f7ce4 vocab=4836d0c2
-/
@[simp]
theorem mem_powerSubgroup_iff {a : Kˣ} :
    a ∈ powerSubgroup K L p ↔ ∃ α : Lˣ, algebraMap K L (a : K) = (α : L) ^ p :=
  Iff.rfl

/--
@isnad1 id=le.0h3v.s7.738a58e30309 from=translated src=- shape=86d2344a vocab=f323a67f
-/
theorem range_powMonoidHom_le_powerSubgroup :
    (powMonoidHom p : Kˣ →* Kˣ).range ≤ powerSubgroup K L p := by
  rintro _ ⟨b, rfl⟩
  refine ⟨Units.map (algebraMap K L).toMonoidHom b, ?_⟩
  show algebraMap K L (((b ^ p : Kˣ) : K)) = (algebraMap K L (b : K)) ^ p
  rw [Units.val_pow_eq_pow_val, map_pow]

noncomputable def chosenRoot (a : powerSubgroup K L p) : Lˣ :=
  (mem_powerSubgroup_iff.mp a.2).choose

/--
@isnad1 id=eq.0h4v.s8.7582dd663016 from=translated src=- shape=fd0101ab vocab=0c90ac5c
-/
theorem chosenRoot_spec (a : powerSubgroup K L p) :
    algebraMap K L ((a : Kˣ) : K) = ((chosenRoot a : Lˣ) : L) ^ p :=
  (mem_powerSubgroup_iff.mp a.2).choose_spec

noncomputable def kummerHom (K L : Type) [Field K] [Field L] [Algebra K L] (p : ℕ) :
    powerSubgroup K L p →* Multiplicative (H1 (kummerRep K L p)) :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd (kummerClass (chosenRoot_spec a))) fun a b => by
    have h : kummerClass (chosenRoot_spec (a * b))
        = kummerClass (chosenRoot_spec a) + kummerClass (chosenRoot_spec b) := by
      rw [kummerClass_eq_of_pow_eq (chosenRoot_spec (a * b))
        (mul_pow_eq (chosenRoot_spec a) (chosenRoot_spec b))]
      exact kummerClass_mul _ _
    show Multiplicative.ofAdd (kummerClass (chosenRoot_spec (a * b)))
        = Multiplicative.ofAdd (kummerClass (chosenRoot_spec a))
          * Multiplicative.ofAdd (kummerClass (chosenRoot_spec b))
    rw [← ofAdd_add, h]

/--
@isnad1 id=eq.0h4v.s11.c6c8f697cf5f from=translated src=- shape=065e51b1 vocab=ccec751e
-/
@[simp]
theorem kummerHom_apply (a : powerSubgroup K L p) :
    kummerHom K L p a = Multiplicative.ofAdd (kummerClass (chosenRoot_spec a)) :=
  rfl

/--
@isnad1 id=eq.1h5v.s11.41bd612276a4 from=translated src=- shape=7dc011af vocab=4267e6b2
-/
theorem kummerHom_apply_mk (a : Kˣ) (α : Lˣ) (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    kummerHom K L p ⟨a, α, hα⟩ = Multiplicative.ofAdd (kummerClass hα) := by
  show Multiplicative.ofAdd (kummerClass (chosenRoot_spec ⟨a, α, hα⟩)) = _
  rw [kummerClass_eq_of_pow_eq (chosenRoot_spec ⟨a, α, hα⟩) hα]

end RepLevel

end Kummer

end groupCohomology
