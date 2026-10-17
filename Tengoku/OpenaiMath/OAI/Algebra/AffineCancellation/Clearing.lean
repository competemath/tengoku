import Tengoku.OpenaiMath.OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

namespace ComplexCancellation.Clearing
variable {k S R : Type*} [CommRing k] [CommRing S] [CommRing R] [Algebra k S] [Algebra k R]

/-- Elements whose denominators can be cleared with a power of a fixed base element. -/
def subalgebra (f : S →ₐ[k] R) (p : S) : Subalgebra k R where
  carrier := {r | ∃ n : ℕ, ∃ s : S, f p ^ n * r = f s}
  zero_mem' := ⟨0,0,by simp⟩
  one_mem' := ⟨0,1,by simp⟩
  add_mem' := by
    rintro r s ⟨n,a,ha⟩ ⟨m,b,hb⟩
    refine ⟨n+m,p^m*a+p^n*b,?_⟩
    rw [map_add,map_mul,map_mul,map_pow,map_pow,← ha,← hb,pow_add]
    ring
  mul_mem' := by
    rintro r s ⟨n,a,ha⟩ ⟨m,b,hb⟩
    refine ⟨n+m,a*b,?_⟩
    rw [map_mul,← ha,← hb,pow_add]
    ring
  algebraMap_mem' c := ⟨0,algebraMap k S c,by simp⟩

/--
@isnad1 id=mem.0h6v.s7.2ca5dc53b863 from=translated src=- shape=a58ea21d vocab=1344901e
-/
lemma mem_base (f : S →ₐ[k] R) (p s : S) : f s ∈ subalgebra f p := ⟨0,s,by simp⟩

/--
@isnad1 id=injectiv.3h7v.s9.1c23726521e0 from=translated src=- shape=5fbdaf2e vocab=5d671c37
-/
lemma injective_of_clearing {K : Type*} [CommRing K] [Algebra k K]
    (e : R →ₐ[k] K) (f : S →ₐ[k] R) (p : S)
    (hef : Function.Injective (e.comp f)) (hp : IsLeftRegular (f p))
    (h : subalgebra f p = ⊤) : Function.Injective e := by
  apply (injective_iff_map_eq_zero e).mpr
  intro r hr
  have hm : r ∈ subalgebra f p := by rw [h]; trivial
  obtain ⟨n,s,hs⟩ := hm
  have hz : s = 0 := by
    apply hef
    change e (f s) = e (f 0)
    rw [← hs,map_mul,hr,mul_zero,map_zero,map_zero]
  rw [hz,map_zero] at hs
  exact isLeftRegular_iff_right_eq_zero_of_mul.mp (hp.pow n) r hs

/--
@isnad1 id=eq.2h7v.s9.d8c8929b4c91 from=translated src=- shape=745c76b1 vocab=4c7eaa9f
-/
lemma top_of_generators {ι : Type*} (q : MvPolynomial ι k →ₐ[k] R)
    (hq : Function.Surjective q) (f : S →ₐ[k] R) (p : S)
    (hX : ∀ i, q (MvPolynomial.X i) ∈ subalgebra f p) : subalgebra f p = ⊤ := by
  apply top_unique
  intro r hrTop
  clear hrTop
  obtain ⟨r,rfl⟩ := hq r
  induction r using MvPolynomial.induction_on with
  | C c => exact (q.commutes c) ▸ (subalgebra f p).algebraMap_mem c
  | add r s hr hs => rw [map_add]; exact add_mem hr hs
  | mul_X r i hr => rw [map_mul]; exact mul_mem hr (hX i)

end ComplexCancellation.Clearing

end

end OAI
