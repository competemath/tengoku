import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_DeligneSerre_exists_minimalPrime_le
import Tengoku.FltAnthropic.Theorems.Thm_DeligneSerre_charZero_quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_DeligneSerre_exists_charZero_eigenvector_of_residual_character.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_DeligneSerre_exists_charZero_eigenvector_of_residual_character

namespace DeligneSerre
export _root_.DeligneSerre (exists_minimalPrime_le charZero_quotient)
namespace S17
open _root_.DeligneSerre

section Key

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

def torsionAway (M : Type*) [AddCommGroup M] [Module R M] (p : Ideal R) [hp : p.IsPrime] :
    Submodule R M where
  carrier := {x | ∃ s : R, s ∉ p ∧ s • x = 0}
  zero_mem' := ⟨1, fun h => hp.ne_top ((Ideal.eq_top_iff_one p).mpr h), smul_zero 1⟩
  add_mem' := by
    rintro x y ⟨s, hs, hsx⟩ ⟨t, ht, hty⟩
    refine ⟨s * t, fun h => (hp.mem_or_mem h).elim hs ht, ?_⟩
    rw [smul_add, mul_comm s t, mul_smul, hsx, smul_zero, mul_comm t s, mul_smul, hty, smul_zero,
      add_zero]
  smul_mem' := by
    rintro r x ⟨s, hs, hsx⟩
    exact ⟨s, hs, by rw [smul_comm, hsx, smul_zero]⟩

variable {p : Ideal R} [hp : p.IsPrime]

/--
@isnad1 id=iff.0h4v.s7.a85cf1b815a5 from=translated src=- shape=1cf1f268 vocab=da41114f
-/
theorem mem_torsionAway {x : M} : x ∈ torsionAway M p ↔ ∃ s : R, s ∉ p ∧ s • x = 0 := Iff.rfl

/--
@isnad1 id=mem.2h5v.s7.dacbc53b3ac3 from=translated src=- shape=bf7bbf9c vocab=da41114f
-/
theorem mem_torsionAway_of_smul_mem {s : R} (hs : s ∉ p) {x : M}
    (hx : s • x ∈ torsionAway M p) : x ∈ torsionAway M p := by
  obtain ⟨t, ht, htx⟩ := hx
  exact ⟨t * s, fun h => (hp.mem_or_mem h).elim ht hs, by rw [mul_smul, htx]⟩

/--
@isnad1 id=ne.0h3v.s7.d56ea6fe8715 from=translated src=- shape=86f3b0cc vocab=2a531c1d
-/
theorem torsionAway_ne_top [Module.Finite R M] [FaithfulSMul R M] : torsionAway M p ≠ ⊤ := by
  classical
  intro htop
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := R) (M := M)
  have hmem : ∀ g ∈ G, ∃ s : R, s ∉ p ∧ s • g = 0 := fun g _ =>
    (mem_torsionAway (p := p)).mp (by rw [htop]; exact Submodule.mem_top)
  choose! f hf using hmem
  have hsnot : (∏ g ∈ G, f g) ∉ p := by
    have hmemc : ∀ g ∈ G, f g ∈ p.primeCompl := fun g hg => (hf g hg).1
    exact prod_mem hmemc
  have hkill : ∀ g ∈ G, (∏ g ∈ G, f g) • g = 0 := fun g hg => by
    rw [← Finset.prod_erase_mul G f hg, mul_smul, (hf g hg).2, smul_zero]

  have hall : ∀ m : M, (∏ g ∈ G, f g) • m = 0 := by
    have hle : Submodule.span R (G : Set M)
        ≤ LinearMap.ker ((∏ g ∈ G, f g) • (LinearMap.id : M →ₗ[R] M)) := by
      rw [Submodule.span_le]
      intro g hg
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
      exact hkill g hg
    intro m
    have hm : m ∈ Submodule.span R (G : Set M) := by rw [hG]; exact Submodule.mem_top
    simpa using hle hm

  have hs0 : (∏ g ∈ G, f g) = 0 := FaithfulSMul.eq_of_smul_eq_smul (α := M) fun m => by
    rw [hall m, zero_smul]
  exact hsnot (hs0 ▸ p.zero_mem)

def annMod (p : Ideal R) [p.IsPrime] (y : M) : Ideal R :=
  (torsionAway M p).comap (LinearMap.toSpanSingleton R M y)

/--
@isnad1 id=iff.0h5v.s7.93c32c1d7425 from=translated src=- shape=4a386785 vocab=267616bd
-/
theorem mem_annMod {y : M} {r : R} : r ∈ annMod p y ↔ r • y ∈ torsionAway M p := by
  simp [annMod, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]

/--
@isnad1 id=le.1h4v.s7.cd17d65c28db from=translated src=- shape=b5ed6b62 vocab=5de9c6b8
-/
theorem annMod_le {y : M} (hy : y ∉ torsionAway M p) : annMod p y ≤ p := by
  intro r hr
  by_contra hrp
  exact hy (mem_torsionAway_of_smul_mem hrp (mem_annMod.mp hr))

/--
@isnad1 id=le.0h5v.s7.846e8d08c17d from=translated src=- shape=3e70bf8c vocab=e14f8224
-/
theorem annMod_mono (y : M) (a : R) : annMod p y ≤ annMod p (a • y) := by
  intro r hr
  rw [mem_annMod] at hr ⊢
  rw [smul_comm]
  exact Submodule.smul_mem _ a hr

/--
@isnad1 id=ex.1h3v.s8.d4dd6652019b from=translated src=- shape=408743fe vocab=6d9fa6d0
-/
theorem exists_exact_annihilator [IsNoetherianRing R] [Module.Finite R M] [FaithfulSMul R M]
    (hmin : p ∈ minimalPrimes R) :
    ∃ x : M, x ≠ 0 ∧ (∀ r ∈ p, r • x = 0) ∧ (∀ r : R, r • x = 0 → r ∈ p) := by
  classical

  obtain ⟨y₀, hy₀⟩ : ∃ y : M, y ∉ torsionAway M p := by
    by_contra h
    push_neg at h
    exact torsionAway_ne_top (p := p) (M := M) (eq_top_iff.mpr fun y _ => h y)

  obtain ⟨I₀, ⟨y, hy, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) {I | ∃ y : M, y ∉ torsionAway M p ∧ I = annMod p y}
    ⟨_, y₀, hy₀, rfl⟩

  have hne : annMod p y ≠ ⊤ := fun h => hp.ne_top (top_le_iff.mp (h ▸ annMod_le hy))
  have hprime : (annMod p y).IsPrime := by
    refine ⟨hne, fun {a b} hab => ?_⟩
    by_cases ha : a ∈ annMod p y
    · exact Or.inl ha
    · right
      have hay : a • y ∉ torsionAway M p := fun h => ha (mem_annMod.mpr h)
      have hle : annMod p y ≤ annMod p (a • y) := annMod_mono y a
      have heq : annMod p y = annMod p (a • y) :=
        eq_of_le_of_not_lt hle (hmax _ ⟨a • y, hay, rfl⟩)
      rw [heq, mem_annMod, smul_smul, mul_comm b a]
      exact mem_annMod.mp hab

  have hle : annMod p y ≤ p := annMod_le hy
  have hge : p ≤ annMod p y := hmin.2 ⟨hprime, bot_le⟩ hle
  have heq : annMod p y = p := le_antisymm hle hge

  obtain ⟨P, hP⟩ := (inferInstance : IsNoetherian R R).noetherian p
  have hgen : ∀ a ∈ P, ∃ s : R, s ∉ p ∧ s • (a • y) = 0 := fun a ha => by
    have hap : a ∈ annMod p y := by
      rw [heq, ← hP]
      exact Submodule.subset_span ha
    exact mem_annMod.mp hap
  choose! f hf using hgen
  set s : R := ∏ a ∈ P, f a with hs_def
  have hsnot : s ∉ p := by
    have hmemc : ∀ a ∈ P, f a ∈ p.primeCompl := fun a ha => (hf a ha).1
    exact prod_mem hmemc
  refine ⟨s • y, ?_, ?_, ?_⟩
  ·
    intro h0
    have : s • y ∈ torsionAway M p := by rw [h0]; exact Submodule.zero_mem _
    exact hy (mem_torsionAway_of_smul_mem hsnot this)
  ·
    have hkill : ∀ a ∈ P, a • (s • y) = 0 := fun a ha => by
      rw [hs_def, ← Finset.prod_erase_mul P f ha, smul_smul,
        show a * ((∏ x ∈ P.erase a, f x) * f a) = (∏ x ∈ P.erase a, f x) * (f a * a) by ring,
        mul_smul, mul_smul, (hf a ha).2, smul_zero]
    intro r hr
    have hle' : Submodule.span R (P : Set R) ≤ LinearMap.ker (LinearMap.toSpanSingleton R M (s • y)) := by
      rw [Submodule.span_le]
      intro a ha
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hkill a ha
    have hr' : r ∈ Submodule.span R (P : Set R) := by rw [hP]; exact hr
    simpa [LinearMap.toSpanSingleton_apply] using hle' hr'
  ·
    intro r hr
    by_contra hrp
    exact hy (mem_torsionAway_of_smul_mem hsnot ⟨r, hrp, hr⟩)

end Key

end DeligneSerre.S17

/--
@isnad1 id=ex.0h4v.s10.d0b30e87d6b1 from=translated src=- shape=25f9ed00 vocab=85564ffb
-/
theorem solution {T : Type*} [CommRing T] [Module.Finite ℤ T]
    [Module.IsTorsionFree ℤ T] {M : Type*} [AddCommGroup M] [Module T M] [Module.Finite T M] [FaithfulSMul T M]
    {k : Type*} [Field k] (χ : T →+* k) :
    ∃ 𝔭 ∈ minimalPrimes T,
      𝔭 ≤ RingHom.ker χ ∧
        (∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0) ∧
          CharZero (T ⧸ 𝔭) ∧
            (∃ red : T ⧸ 𝔭 →+* k, red.comp (Ideal.Quotient.mk 𝔭) = χ) ∧
              ∃ x : M,
                x ≠ 0 ∧
                  (∀ p ∈ 𝔭, p • x = 0) ∧
                    (∀ (r : T), r • x = 0 → r ∈ 𝔭) ∧
                      ∀ (h h' : T), (Ideal.Quotient.mk 𝔭) h = (Ideal.Quotient.mk 𝔭) h' → h • x = h' • x := by

  obtain ⟨𝔭, h𝔭min, h𝔭le, h𝔭char⟩ :=
    DeligneSerre.exists_minimalPrime_le (RingHom.ker χ) (RingHom.ker_isPrime χ)
  haveI h𝔭prime : 𝔭.IsPrime := h𝔭min.1.1
  have hred : ∃ red : T ⧸ 𝔭 →+* k, red.comp (Ideal.Quotient.mk 𝔭) = χ :=
    ⟨Ideal.Quotient.lift 𝔭 χ fun a ha => by
      have hker : a ∈ RingHom.ker χ := h𝔭le ha
      rwa [RingHom.mem_ker] at hker, rfl⟩

  haveI : IsNoetherianRing T := IsNoetherianRing.of_finite ℤ T
  obtain ⟨x, hx0, hxkill, hxann⟩ := DeligneSerre.S17.exists_exact_annihilator (M := M) h𝔭min
  refine ⟨𝔭, h𝔭min, h𝔭le, h𝔭char, DeligneSerre.charZero_quotient 𝔭 h𝔭char, hred, x, hx0, hxkill, hxann,
    fun h h' hhh => ?_⟩

  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hhh
  have hz := hxkill _ hhh
  rwa [sub_smul, sub_eq_zero] at hz
