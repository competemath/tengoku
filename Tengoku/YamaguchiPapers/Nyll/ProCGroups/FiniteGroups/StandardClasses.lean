/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.GroupTheory.Nilpotent
import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.FiniteGroups.AllFinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Standard classes of finite groups

This module constructs the cyclic, abelian, solvable, nilpotent, finite \(p\)-group,
\(\sigma\)-group, and bounded-exponent abelian classes.  It proves the subgroup, quotient,
product, extension, formation, and full-formation properties needed later, together with the
finite-order arithmetic and cyclic witnesses supporting those proofs.
-/

namespace ProCGroups

universe u v

namespace FiniteGroupClass

/-- If \(a \nmid b\), then some prime factor has a larger exponent in \(a\) than in \(b\).
@isnad1 id=ex.3h2v.s6.3b95e07187fc from=translated src=- shape=0d5271cb vocab=ca401e7d
-/
theorem exists_factorization_lt_of_not_dvd
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hndvd : ¬ a ∣ b) :
    ∃ p, b.factorization p < a.factorization p := by
  by_contra h
  push Not at h
  have hle : a.factorization ≤ b.factorization := by
    intro p
    exact h p
  exact hndvd ((Nat.factorization_le_iff_dvd ha hb).1 hle)

/-- The p-adic exponent of a positive integer is at most the integer itself.
@isnad1 id=le.1h2v.s4.fee7bbf13c29 from=translated src=- shape=ea3a2371 vocab=06eca969
-/
theorem nat_factorization_le_self_of_prime
    {A p : ℕ} (hp : Nat.Prime p) :
    A.factorization p ≤ A :=
  Nat.factorization_le_of_le_pow (le_of_lt (Nat.lt_pow_self (n := A) (a := p) hp.one_lt))

/-- The depth \((K*d)^(A+1)\) is large enough for the GCD-conditioned cyclic reduction.
@isnad1 id=dvd.3h3v.s6.5b498bf1b06d from=translated src=- shape=ae764e35 vocab=f77181e3
-/
theorem gcd_mul_dvd_pow_depth
    {K d A : ℕ} (hK : 0 < K) (hd : 0 < d) (hA : 0 < A) :
    Nat.gcd (d * A) (K * (K * d) ^ (A + 1)) ∣ (K * d) ^ (A + 1) := by
  let B : ℕ := K * d
  let M : ℕ := B ^ (A + 1)
  have hB : 0 < B := Nat.mul_pos hK hd
  have hM : 0 < M := pow_pos hB (A + 1)
  have hleft_ne : d * A ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hd hA)
  have hright_ne : K * M ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hK hM)
  have hgcd_ne : Nat.gcd (d * A) (K * M) ≠ 0 :=
    Nat.ne_of_gt (Nat.gcd_pos_of_pos_left (K * M) (Nat.mul_pos hd hA))
  rw [← Nat.factorization_le_iff_dvd hgcd_ne (Nat.ne_of_gt hM)]
  intro p
  by_cases hp : Nat.Prime p
  · by_cases hpB : p ∣ B
    · have hdvdB : d ∣ B := by
        exact Nat.dvd_mul_left d K
      have hdfacB : d.factorization p ≤ B.factorization p :=
        (Nat.factorization_le_iff_dvd (Nat.ne_of_gt hd) (Nat.ne_of_gt hB)).2 hdvdB p
      have hAfacle : A.factorization p ≤ A :=
        nat_factorization_le_self_of_prime hp
      have hBfacpos : 0 < B.factorization p := by
        exact lt_of_lt_of_le Nat.zero_lt_one
          ((hp.dvd_iff_one_le_factorization (Nat.ne_of_gt hB)).1 hpB)
      have hleft_fac_le :
          (d * A).factorization p ≤ M.factorization p := by
        calc
          (d * A).factorization p
              = d.factorization p + A.factorization p := by
                  rw [Nat.factorization_mul (Nat.ne_of_gt hd) (Nat.ne_of_gt hA)]
                  rfl
          _ ≤ B.factorization p + A := Nat.add_le_add hdfacB hAfacle
          _ ≤ B.factorization p + A * B.factorization p := by
                  exact Nat.add_le_add_left
                    (Nat.le_mul_of_pos_right A hBfacpos) (B.factorization p)
          _ = (A + 1) * B.factorization p := by
                  rw [Nat.add_mul, one_mul, add_comm]
          _ = M.factorization p := by
                  simp only [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, M]
      have hgcd_fac :
          (Nat.gcd (d * A) (K * M)).factorization p =
            min ((d * A).factorization p) ((K * M).factorization p) := by
        rw [Nat.factorization_gcd hleft_ne hright_ne]
        rfl
      rw [hgcd_fac]
      exact (min_le_left _ _).trans hleft_fac_le
    · have hnotK : ¬ p ∣ K := by
        intro hpK
        exact hpB (dvd_mul_of_dvd_left hpK d)
      have hnotM : ¬ p ∣ M := by
        intro hpM
        exact hpB (hp.dvd_of_dvd_pow hpM)
      have hnotKM : ¬ p ∣ K * M := by
        exact hp.not_dvd_mul hnotK hnotM
      have hright_fac : (K * M).factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hnotKM
      have hgcd_fac :
          (Nat.gcd (d * A) (K * M)).factorization p =
            min ((d * A).factorization p) ((K * M).factorization p) := by
        rw [Nat.factorization_gcd hleft_ne hright_ne]
        rfl
      rw [hgcd_fac, hright_fac]
      simp only [zero_le, inf_of_le_right]
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp, le_refl]

/-- The class of finite cyclic groups.-/
def cyclic : FiniteGroupClass.{u} where
  pred := fun G [_] => Finite G ∧ IsCyclic G
  finite_of_mem := fun hG => hG.1
  mem_of_mulEquiv := by
    intro G H _ _ e hG
    let : Finite G := hG.1
    exact ⟨Finite.of_equiv G e.toEquiv, e.isCyclic.mp hG.2⟩

/-- The class of finite abelian groups.-/
def abelian : FiniteGroupClass.{u} where
  pred := fun G [_] => Finite G ∧ ∀ a b : G, a * b = b * a
  finite_of_mem := fun hG => hG.1
  mem_of_mulEquiv := by
    intro G H _ _ e hG
    let : Finite G := hG.1
    refine ⟨Finite.of_equiv G e.toEquiv, ?_⟩
    intro a b
    apply e.symm.injective
    simpa using hG.2 (e.symm a) (e.symm b)

/-- The class of finite solvable groups.-/
def solvable : FiniteGroupClass.{u} where
  pred := fun G [_] => Finite G ∧ Group.IsSolvable G
  finite_of_mem := fun hG => hG.1
  mem_of_mulEquiv := by
    intro G H _ _ e hG
    let : Finite G := hG.1
    let : Group.IsSolvable G := hG.2
    exact ⟨Finite.of_equiv G e.toEquiv,
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective⟩

/-- The finite group class consisting of finite nilpotent groups.-/
def nilpotent : FiniteGroupClass.{u} where
  pred := fun G [_] => Finite G ∧ Group.IsNilpotent G
  finite_of_mem := fun hG => hG.1
  mem_of_mulEquiv := by
    intro G H _ _ e hG
    let : Finite G := hG.1
    exact ⟨Finite.of_equiv G e.toEquiv,
      (Group.isNilpotent_congr e).mp hG.2⟩

/-- The class of finite \(p\)-groups.-/
def pGroup (p : ℕ) [Fact (Nat.Prime p)] : FiniteGroupClass.{u} where
  pred := fun G [_] => Finite G ∧ IsPGroup p G
  finite_of_mem := fun hG => hG.1
  mem_of_mulEquiv := by
    intro G H _ _ e hG
    let : Finite G := hG.1
    exact ⟨Finite.of_equiv G e.toEquiv,
      hG.2.of_surjective e.toMonoidHom e.surjective⟩

/--
A natural number whose prime divisors all lie in \(\Sigma\). This is the finite-level condition
underlying finite \(\Sigma\)-groups and pro-\(\Sigma\) groups.-/
def IsSigmaNumber (sigma : Set ℕ) (n : ℕ) : Prop :=
  ∀ p, Nat.Prime p → p ∉ sigma → ¬ p ∣ n

namespace IsSigmaNumber

/-- Every divisor of a \(\Sigma\)-number is again a \(\Sigma\)-number.
@isnad1 id=issigman.2h3v.s4.5abb2dea2adb from=translated src=- shape=c3c20eef vocab=487557ac
-/
theorem of_dvd {sigma : Set ℕ} {m n : ℕ} (hn : IsSigmaNumber sigma n) (hmn : m ∣ n) :
    IsSigmaNumber sigma m := by
  intro p hp hpsigma hpm
  exact hn p hp hpsigma (dvd_trans hpm hmn)

/-- The product of two \(\Sigma\)-numbers is a \(\Sigma\)-number.
@isnad1 id=issigman.2h3v.s4.3a216841a6c4 from=translated src=- shape=26c66de5 vocab=154b890b
-/
theorem mul {sigma : Set ℕ} {m n : ℕ} (hm : IsSigmaNumber sigma m)
    (hn : IsSigmaNumber sigma n) :
    IsSigmaNumber sigma (m * n) := by
  intro p hp hpsigma hpmn
  exact (hp.not_dvd_mul (hm p hp hpsigma) (hn p hp hpsigma)) hpmn

/-- A finite product of \(\Sigma\)-numbers is a \(\Sigma\)-number.
@isnad1 id=issigman.1h4v.s5.240a2bfc9653 from=translated src=- shape=a3676b75 vocab=39cde1e6
-/
theorem prod {sigma : Set ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, IsSigmaNumber sigma (f i)) :
    IsSigmaNumber sigma (s.prod f) := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro p hp _ hpdvd
      exact hp.ne_one (Nat.dvd_one.mp hpdvd)
  | insert a s ha hs =>
      have hfa : IsSigmaNumber sigma (f a) := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, IsSigmaNumber sigma (f i) :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      simpa [Finset.prod_insert ha] using mul (sigma := sigma) hfa (hs hfs)

/-- A natural-number power of a \(\Sigma\)-number is a \(\Sigma\)-number.
@isnad1 id=issigman.1h3v.s4.3248b235e2cd from=translated src=- shape=cd8e4aa2 vocab=21f0334b
-/
theorem pow {sigma : Set ℕ} {n k : ℕ} (hn : IsSigmaNumber sigma n) :
    IsSigmaNumber sigma (n ^ k) := by
  induction k with
  | zero =>
      intro p hp _ hpdvd
      exact hp.ne_one (Nat.dvd_one.mp hpdvd)
  | succ k ih =>
      rw [pow_succ]
      exact mul ih hn

/-- A prime power whose prime lies in \(\Sigma\) is a \(\Sigma\)-number.
@isnad1 id=issigman.2h3v.s5.1499d874d69e from=translated src=- shape=58c8e679 vocab=7b343448
-/
theorem prime_pow_of_mem {sigma : Set ℕ} {p k : ℕ}
    (hpsigma : p ∈ sigma) (hp : Nat.Prime p) :
    IsSigmaNumber sigma (p ^ k) := by
  intro q hq hqsigma hqdiv
  by_cases hk : k = 0
  · simp only [hk, pow_zero, Nat.dvd_one] at hqdiv
    exact hq.ne_one hqdiv
  · have hq_dvd_p : q ∣ p := hq.dvd_of_dvd_pow hqdiv
    have hp_eq_q : p = q := (hp.dvd_iff_eq hq.ne_one).1 hq_dvd_p
    exact hqsigma (hp_eq_q ▸ hpsigma)

end IsSigmaNumber

/--
The class of finite \(\Sigma\)-groups: finite groups whose order has no prime divisors outside
\(\Sigma\).-/
def sigmaGroup (sigma : Set ℕ) : FiniteGroupClass.{u} where
  pred := fun G [_] => Finite G ∧ IsSigmaNumber sigma (Nat.card G)
  finite_of_mem := fun hG => hG.1
  mem_of_mulEquiv := by
    intro G H _ _ e hG
    let : Finite G := hG.1
    refine ⟨Finite.of_equiv G e.toEquiv, ?_⟩
    simpa [Nat.card_congr e.toEquiv] using hG.2

/-- The class of finite abelian groups of exponent dividing \(n\).-/
def abelianExponent (n : ℕ) : FiniteGroupClass.{u} where
  pred := fun G [_] =>
    Finite G ∧ (∀ a b : G, a * b = b * a) ∧ ∀ g : G, g ^ n = 1
  finite_of_mem := fun hG => hG.1
  mem_of_mulEquiv := by
    intro G H _ _ e hG
    let : Finite G := hG.1
    refine ⟨Finite.of_equiv G e.toEquiv, ?_, ?_⟩
    · intro a b
      apply e.symm.injective
      simpa using hG.2.1 (e.symm a) (e.symm b)
    · intro g
      apply e.symm.injective
      simpa using hG.2.2 (e.symm g)

section

variable {p : ℕ}

/-- Finite products of abstract \(p\)-groups are \(p\)-groups.
@isnad1 id=ispgroup.1h3v.s5.b63bee423bd4 from=translated src=- shape=4ca388a7 vocab=7cfccd02
-/
theorem isPGroup_pi {ι : Type u} [Finite ι] {G : ι → Type v}
    [∀ i, Group (G i)] (hG : ∀ i, IsPGroup p (G i)) :
    IsPGroup p ((i : ι) → G i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  intro g
  choose k hk using fun i => hG i (g i)
  let N : ℕ := Finset.univ.sup k
  refine ⟨N, ?_⟩
  funext i
  have hki : k i ≤ N := Finset.le_sup (Finset.mem_univ i)
  calc
    (g ^ p ^ N) i = (g i) ^ (p ^ N) := by simp only [Pi.pow_apply]
    _ = (g i) ^ (p ^ (k i) * p ^ (N - k i)) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hki]
    _ = ((g i) ^ (p ^ k i)) ^ (p ^ (N - k i)) := by
      rw [pow_mul]
    _ = 1 := by simp only [hk i, one_pow]

/-- The class of finite \(p\)-groups is a formation.
@isnad1 id=formatio.0h1v.s3.c43cb9b23132 from=translated src=- shape=9ee3c16b vocab=cafb12f8
-/
theorem pGroup_formation (p : ℕ) [Fact (Nat.Prime p)] :
    FiniteGroupClass.Formation (FiniteGroupClass.pGroup p) := by
  refine ⟨?_, ?_⟩
  · intro G _ N _ hG
    rcases hG with ⟨hfin, hpG⟩
    refine ⟨?_, hpG.to_quotient N⟩
    infer_instance
  · intro ι _ G _ H _ f hf _hsurj hH
    let : ∀ i, Finite (H i) := fun i => (hH i).1
    have hPi : IsPGroup p ((i : ι) → H i) := isPGroup_pi (p := p) fun i => (hH i).2
    exact ⟨Finite.of_injective f hf, hPi.of_injective f hf⟩

/-- Subgroups of finite \(p\)-groups are finite \(p\)-groups.
@isnad1 id=subgroup.0h1v.s3.a52728b5704b from=translated src=- shape=9ee3c16b vocab=4c09f0dd
-/
theorem pGroup_subgroupClosed (p : ℕ) [Fact (Nat.Prime p)] : SubgroupClosed (pGroup p) := by
  intro G _ H hG
  rcases hG with ⟨hfin, hpG⟩
  exact ⟨Finite.of_injective ((↑) : H → G) Subtype.coe_injective, hpG.to_subgroup H⟩

/-- A group is finite when a normal subgroup and the corresponding quotient are finite.
@isnad1 id=finite.0h2v.s5.224ef92800c7 from=translated src=- shape=1ef1b324 vocab=4acbc589
-/
theorem finite_of_finite_normalSubgroup_and_quotient
    {E : Type u} [Group E] (N : Subgroup E) [N.Normal]
    [Finite N] [Finite (E ⧸ N)] :
    Finite E := by
  classical
  let s : E ⧸ N → E := Quotient.out
  let f : N × (E ⧸ N) → E := fun z => z.1.1 * s z.2
  have hsurj : Function.Surjective f := by
    intro e
    let q : E ⧸ N := QuotientGroup.mk' N e
    have hsq : QuotientGroup.mk' N (s q) = q := Quotient.out_eq' q
    have hmem : e * (s q)⁻¹ ∈ N := by
      apply (QuotientGroup.eq_one_iff (N := N) (e * (s q)⁻¹)).1
      change QuotientGroup.mk' N e * (QuotientGroup.mk' N (s q))⁻¹ = 1
      rw [hsq]
      simp only [QuotientGroup.mk'_apply, mul_inv_cancel, q]
    refine ⟨(⟨e * (s q)⁻¹, hmem⟩, q), ?_⟩
    simp only [QuotientGroup.mk'_apply, mul_assoc, inv_mul_cancel, mul_one, f, q]
  exact Finite.of_surjective f hsurj

/-- Extensions of finite \(p\)-groups are finite \(p\)-groups.
@isnad1 id=extensio.0h1v.s3.7c17c8f28c8e from=translated src=- shape=9ee3c16b vocab=a936ac5d
-/
theorem pGroup_extensionClosed (p : ℕ) [Fact (Nat.Prime p)] :
    ExtensionClosed (pGroup p) := by
  intro E _ N _ hN hQ
  rcases hN with ⟨hNfin, hpN⟩
  rcases hQ with ⟨hQfin, hpQ⟩
  have hEfin : Finite E := finite_of_finite_normalSubgroup_and_quotient (N := N)
  have hker :
      IsPGroup p ((QuotientGroup.mk' N).ker : Subgroup E) := by
    exact hpN.of_equiv (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' N).symm)
  have hTopQ : IsPGroup p (⊤ : Subgroup (E ⧸ N)) := hpQ.to_subgroup ⊤
  have hTopE :
      IsPGroup p ((⊤ : Subgroup (E ⧸ N)).comap (QuotientGroup.mk' N)) :=
    hTopQ.comap_of_ker_isPGroup (QuotientGroup.mk' N) hker
  have hTop' : IsPGroup p (⊤ : Subgroup E) := by
    rw [Subgroup.comap_top] at hTopE
    exact hTopE
  have hEp : IsPGroup p E :=
    hTop'.of_surjective (⊤ : Subgroup E).subtype <| by
      intro x
      exact ⟨⟨x, by simp only [Subgroup.mem_top]⟩, rfl⟩
  exact ⟨hEfin, hEp⟩

/-- The class of finite \(p\)-groups is hereditary under subgroups.
@isnad1 id=heredita.0h1v.s3.aecd7dd4ea69 from=translated src=- shape=9ee3c16b vocab=dd688186
-/
theorem pGroup_hereditary (p : ℕ) [Fact (Nat.Prime p)] : Hereditary (pGroup p) :=
  Hereditary.of_subgroupClosed_isomClosed
    (pGroup_subgroupClosed p)
    (pGroup_formation p).isomClosed

end

section

variable {sigma : Set ℕ}

/-- `sigmaGroup` is closed under group isomorphism.
@isnad1 id=isomclos.0h1v.s2.c2d1fb045928 from=translated src=- shape=94c7f951 vocab=dee81195
-/
theorem sigmaGroup_isomClosed (sigma : Set ℕ) : IsomClosed (sigmaGroup sigma) := by
  intro G H _ _ hGH hG
  rcases hGH with ⟨e⟩
  rcases hG with ⟨hfin, hsigma⟩
  refine ⟨Finite.of_equiv G e.toEquiv, ?_⟩
  simpa [Nat.card_congr e.toEquiv] using hsigma

/-- `sigmaGroup` is closed under subgroups.
@isnad1 id=subgroup.0h1v.s2.0e25e424b085 from=translated src=- shape=94c7f951 vocab=08d9cf79
-/
theorem sigmaGroup_subgroupClosed (sigma : Set ℕ) : SubgroupClosed (sigmaGroup sigma) := by
  intro G _ H hG
  rcases hG with ⟨hfin, hsigma⟩
  refine ⟨Finite.of_injective ((↑) : H → G) Subtype.coe_injective, ?_⟩
  exact IsSigmaNumber.of_dvd (sigma := sigma) hsigma (Subgroup.card_subgroup_dvd_card H)

/-- `sigmaGroup` is closed under quotients.
@isnad1 id=quotient.0h1v.s2.bf22ed7bf51e from=translated src=- shape=94c7f951 vocab=9f8b4bcc
-/
theorem sigmaGroup_quotientClosed (sigma : Set ℕ) : QuotientClosed (sigmaGroup sigma) := by
  intro G _ N _ hG
  rcases hG with ⟨hfin, hsigma⟩
  refine ⟨?_, ?_⟩
  · infer_instance
  · exact IsSigmaNumber.of_dvd (sigma := sigma) hsigma (Subgroup.card_quotient_dvd_card N)

/-- `sigmaGroup` is closed under finite products.
@isnad1 id=finitepr.0h1v.s2.65420a948fbe from=translated src=- shape=94c7f951 vocab=6f68fd37
-/
theorem sigmaGroup_finiteProductClosed (sigma : Set ℕ) : FiniteProductClosed (sigmaGroup sigma)
    := by
  intro ι _ A _ hA
  refine ⟨?_, ?_⟩
  · let : ∀ i, Finite (A i) := fun i => (hA i).1
    infer_instance
  · simpa [Nat.card_pi] using
      IsSigmaNumber.prod (sigma := sigma) Finset.univ (fun i => Nat.card (A i))
        (fun i _ => (hA i).2)

/-- `sigmaGroup` is a finite-group variety.
@isnad1 id=variety.0h1v.s2.c2a2e72809f5 from=translated src=- shape=94c7f951 vocab=f4e025b4
-/
theorem sigmaGroup_variety (sigma : Set ℕ) : Variety (sigmaGroup sigma) := by
  refine ⟨sigmaGroup_subgroupClosed sigma, sigmaGroup_quotientClosed sigma,
    sigmaGroup_finiteProductClosed sigma⟩

/-- `sigmaGroup` is a formation of finite groups.
@isnad1 id=formatio.0h1v.s2.ae3d602b3a3d from=translated src=- shape=94c7f951 vocab=15e3648d
-/
theorem sigmaGroup_formation (sigma : Set ℕ) : Formation (sigmaGroup sigma) :=
  variety_formation (sigmaGroup_variety sigma) (sigmaGroup_isomClosed sigma)

/-- Finite `Σ`-groups are closed under extensions.
@isnad1 id=extensio.0h1v.s2.5975c90f7b0a from=translated src=- shape=94c7f951 vocab=81409cd6
-/
theorem sigmaGroup_extensionClosed (sigma : Set ℕ) :
    ExtensionClosed (sigmaGroup sigma) := by
  intro E _ N _ hN hQ
  rcases hN with ⟨hNfin, hsigmaN⟩
  rcases hQ with ⟨hQfin, hsigmaQ⟩
  have hEfin : Finite E := finite_of_finite_normalSubgroup_and_quotient (N := N)
  refine ⟨hEfin, ?_⟩
  have hcard :
      Nat.card E = Nat.card (E ⧸ N) * Nat.card N := by
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (α := E) N
  rw [hcard]
  exact IsSigmaNumber.mul hsigmaQ hsigmaN

/-- Finite `Σ`-groups form a Melnikov formation.
@isnad1 id=melnikov.0h1v.s2.2999cd8e9631 from=translated src=- shape=94c7f951 vocab=ca82b0c2
-/
theorem sigmaGroup_melnikovFormation (sigma : Set ℕ) :
    MelnikovFormation (sigmaGroup sigma) where
  formation := sigmaGroup_formation sigma
  normalSubgroupClosed := fun N _ hG => sigmaGroup_subgroupClosed sigma N hG
  extensionClosed := sigmaGroup_extensionClosed sigma

/-- Finite `Σ`-groups form a full formation.
@isnad1 id=fullform.0h1v.s2.06bc90657bd3 from=translated src=- shape=94c7f951 vocab=a2c8e8d8
-/
theorem sigmaGroup_fullFormation (sigma : Set ℕ) :
    FullFormation (sigmaGroup sigma) where
  melnikovFormation := sigmaGroup_melnikovFormation sigma
  subgroupClosed := sigmaGroup_subgroupClosed sigma

/-- A positive `Σ`-number gives an allowed finite cyclic `Σ`-group.
@isnad1 id=pred.2h2v.s5.a2c797abf9b8 from=translated src=- shape=7a85edd2 vocab=e2fe61d8
-/
theorem sigmaGroup_cyclicZMod
    {sigma : Set ℕ} {n : ℕ} (hn : 0 < n)
    (hsigma : IsSigmaNumber sigma n) :
    sigmaGroup sigma (ULift.{u} (Multiplicative (ZMod n))) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let A := ULift.{u} (Multiplicative (ZMod n))
  let e : A ≃* Multiplicative (ZMod n) := MulEquiv.ulift
  let : Finite A := Finite.of_equiv (Multiplicative (ZMod n)) e.symm.toEquiv
  refine ⟨inferInstance, ?_⟩
  have hcard : Nat.card A = n := by
    calc
      Nat.card A = Nat.card (Multiplicative (ZMod n)) := Nat.card_congr e.toEquiv
      _ = n := by simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  simpa [hcard] using hsigma

/-- A nonempty set of primes supplies a nontrivial finite cyclic `Σ`-group.
@isnad1 id=ex.1h1v.s5.9487e192b42c from=translated src=- shape=6a8bea40 vocab=8c8bc938
-/
theorem sigmaGroup_nontrivialCyclic
    {sigma : Set ℕ} (hsigma : ∃ p, p ∈ sigma ∧ Nat.Prime p) :
    ∃ (A : Type u) (_ : Group A) (_ : Finite A),
      sigmaGroup sigma A ∧ IsCyclic A ∧ Nontrivial A := by
  rcases hsigma with ⟨p, hpsigma, hp⟩
  let : Fact (1 < p) := ⟨hp.one_lt⟩
  let A := ULift.{u} (Multiplicative (ZMod p))
  let e : A ≃* Multiplicative (ZMod p) := MulEquiv.ulift
  let : Finite A := Finite.of_equiv (Multiplicative (ZMod p)) e.symm.toEquiv
  have hcyc : IsCyclic A :=
    isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hnon : Nontrivial A := e.toEquiv.nontrivial
  refine ⟨A, inferInstance, inferInstance, ?_, hcyc, hnon⟩
  exact sigmaGroup_cyclicZMod (sigma := sigma) hp.pos <| by
    simpa using
      (IsSigmaNumber.prime_pow_of_mem (sigma := sigma) (p := p) (k := 1) hpsigma hp)

/-- Product of a finite `Σ`-group with the concrete cyclic group `ZMod N`.
@isnad1 id=pred.2h4v.s5.5e7281339bcb from=translated src=- shape=609628b4 vocab=7ae7dfaa
-/
theorem sigmaGroup_prod_multiplicativeZMod
    {sigma : Set ℕ} {Q : Type u} [Group Q]
    (hQ : sigmaGroup sigma Q)
    {N : ℕ} (hNpos : 0 < N)
    (hNsigma : IsSigmaNumber sigma N) :
    sigmaGroup sigma (Q × Multiplicative (ZMod N)) := by
  rcases hQ with ⟨hQfin, hQsigma⟩
  let : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  let : Finite (Multiplicative (ZMod N)) :=
    Finite.of_equiv (ZMod N) Multiplicative.ofAdd
  refine ⟨inferInstance, ?_⟩
  have hcard : Nat.card (Multiplicative (ZMod N)) = N := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [Nat.card_prod, hcard]
  exact IsSigmaNumber.mul hQsigma hNsigma

/-- A nontrivial finite `Σ`-group power supplies a coefficient prime and depth.
@isnad1 id=ex.1h5v.s6.50070f5dc7af from=translated src=- shape=1b089f0a vocab=fe871118
-/
theorem exists_prime_power_orderOf_gt_padicValNat_of_zpow_ne_one
    {sigma : Set ℕ} {G : Type u} [Group G] [Finite G]
    (hG : sigmaGroup sigma G) {g : G} {n : ℤ} (hgn : g ^ n ≠ 1) :
    ∃ ℓ σ : ℕ,
      Nat.Prime ℓ ∧ 0 < σ ∧ ℓ ∈ sigma ∧
        padicValNat ℓ n.natAbs < σ ∧ ℓ ^ σ ∣ orderOf g := by
  have hnZ : g ^ ((n.natAbs : ℕ) : ℤ) ≠ 1 := by
    intro h
    apply hgn
    rcases Int.natAbs_eq n with hn | hn
    · rw [hn]
      simpa using h
    · rw [hn]
      have hinv : (g ^ ((n.natAbs : ℕ) : ℤ))⁻¹ = (1 : G) := by
        rw [h, inv_one]
      simpa [zpow_neg] using hinv
  have hnat : g ^ n.natAbs ≠ 1 := by
    intro hpow
    exact hnZ (by simpa using hpow)
  have hgfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  have horder_pos : 0 < orderOf g := (orderOf_pos_iff).2 hgfin
  have horder_ne : orderOf g ≠ 0 := Nat.ne_of_gt horder_pos
  have hnabs_ne : n.natAbs ≠ 0 := by
    intro hnabs
    apply hnat
    simp only [hnabs, pow_zero]
  have hnotdvd : ¬ orderOf g ∣ n.natAbs := by
    intro hdiv
    exact hnat ((orderOf_dvd_iff_pow_eq_one (x := g) (n := n.natAbs)).1 hdiv)
  rcases exists_factorization_lt_of_not_dvd horder_ne hnabs_ne hnotdvd with
    ⟨ℓ, hℓlt⟩
  have hℓ_fac_ne : (orderOf g).factorization ℓ ≠ 0 :=
    ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hℓlt)
  have hℓ_mem_support : ℓ ∈ (orderOf g).factorization.support :=
    Finsupp.mem_support_iff.mpr hℓ_fac_ne
  have hℓ_mem_primeFactors : ℓ ∈ (orderOf g).primeFactors := by
    simpa [Nat.support_factorization] using hℓ_mem_support
  have hℓprime : Nat.Prime ℓ :=
    Nat.prime_of_mem_primeFactors hℓ_mem_primeFactors
  have hℓdiv_order : ℓ ∣ orderOf g :=
    Nat.dvd_of_factorization_pos hℓ_fac_ne
  have hℓsigma : ℓ ∈ sigma := by
    by_contra hℓnot
    exact hG.2 ℓ hℓprime hℓnot
      (hℓdiv_order.trans (orderOf_dvd_natCard g))
  let σ : ℕ := padicValNat ℓ (orderOf g)
  have hltpadic : padicValNat ℓ n.natAbs < σ := by
    simpa [σ, Nat.factorization_def _ hℓprime] using hℓlt
  have hσpos : 0 < σ := lt_of_le_of_lt (Nat.zero_le _) hltpadic
  have hσdvd : ℓ ^ σ ∣ orderOf g := by
    simpa [σ] using (pow_padicValNat_dvd (p := ℓ) (n := orderOf g))
  exact ⟨ℓ, σ, hℓprime, hσpos, hℓsigma, hltpadic, hσdvd⟩

end

/-- Finite abelian groups are closed under subgroups.
@isnad1 id=subgroup.0h0v.s1.9803db04f5b1 from=translated src=- shape=49959d42 vocab=469e8f1f
-/
theorem abelian_subgroupClosed : SubgroupClosed abelian := by
  intro G _ H hG
  rcases hG with ⟨hfin, hcomm⟩
  refine ⟨Finite.of_injective ((↑) : H → G) Subtype.coe_injective, ?_⟩
  intro a b
  exact Subtype.ext (hcomm a.val b.val)

/-- Finite abelian groups are closed under quotients.
@isnad1 id=quotient.0h0v.s1.3a86d4605db9 from=translated src=- shape=49959d42 vocab=e8be67e3
-/
theorem abelian_quotientClosed : QuotientClosed abelian := by
  intro G _ N _ hG
  rcases hG with ⟨hfin, hcomm⟩
  refine ⟨?_, ?_⟩
  · infer_instance
  · intro a b
    rcases QuotientGroup.mk'_surjective N a with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective N b with ⟨y, rfl⟩
    exact ((QuotientGroup.mk' N).map_mul x y).symm.trans
      ((congrArg (QuotientGroup.mk' N) (hcomm x y)).trans
        ((QuotientGroup.mk' N).map_mul y x))

/-- Finite abelian groups are closed under finite direct products.
@isnad1 id=finitepr.0h0v.s1.dae64603085b from=translated src=- shape=49959d42 vocab=ea3924e9
-/
theorem abelian_finiteProductClosed : FiniteProductClosed abelian := by
  intro ι _ G _ hG
  change Finite ((i : ι) → G i) ∧ ∀ a b : ((i : ι) → G i), a * b = b * a
  constructor
  · let : ∀ i, Finite (G i) := fun i => (hG i).1
    infer_instance
  · intro a b
    funext i
    exact (hG i).2 (a i) (b i)

/-- Finite abelian groups form a variety.
@isnad1 id=variety.0h0v.s1.1c415a5d95ce from=translated src=- shape=49959d42 vocab=f1e6b7fc
-/
theorem abelian_variety : Variety abelian := by
  refine ⟨abelian_subgroupClosed, abelian_quotientClosed,
    abelian_finiteProductClosed⟩

/-- Finite abelian groups are closed under isomorphism.
@isnad1 id=isomclos.0h0v.s1.e363d0c48d2a from=translated src=- shape=49959d42 vocab=2c0fd910
-/
theorem abelian_isomClosed : IsomClosed abelian := by
  intro G H _ _ hGH hG
  rcases hGH with ⟨e⟩
  rcases hG with ⟨hfin, hcomm⟩
  refine ⟨Finite.of_equiv G e.toEquiv, ?_⟩
  intro a b
  have h := hcomm (e.symm a) (e.symm b)
  simpa using congrArg e h

/-- Finite abelian groups form a formation.
@isnad1 id=formatio.0h0v.s1.039606e59739 from=translated src=- shape=49959d42 vocab=4ab0cf02
-/
theorem abelian_formation : Formation abelian :=
  variety_formation abelian_variety abelian_isomClosed

/-- Subgroups of finite abelian groups of bounded exponent again have bounded exponent.
@isnad1 id=subgroup.0h1v.s2.7aedfee58d2b from=translated src=- shape=76a08d12 vocab=f9694589
-/
theorem abelianExponent_subgroupClosed (n : ℕ) : SubgroupClosed (abelianExponent n) := by
  intro G _ H hG
  rcases hG with ⟨hfin, hcomm, hexp⟩
  refine ⟨Finite.of_injective ((↑) : H → G) Subtype.coe_injective, ?_, ?_⟩
  · intro a b
    ext
    exact hcomm a.1 b.1
  · intro g
    ext
    exact hexp g.1

/-- Quotients of finite abelian groups of bounded exponent again have bounded exponent.
@isnad1 id=quotient.0h1v.s2.e2d7b39b30ad from=translated src=- shape=76a08d12 vocab=d6b84391
-/
theorem abelianExponent_quotientClosed (n : ℕ) : QuotientClosed (abelianExponent n) := by
  intro G _ N _ hG
  rcases hG with ⟨hfin, hcomm, hexp⟩
  have habelian : abelian (G ⧸ N) := abelian_quotientClosed N ⟨hfin, hcomm⟩
  refine ⟨habelian.1, habelian.2, ?_⟩
  intro g
  refine Quotient.inductionOn' g ?_
  intro x
  change QuotientGroup.mk' N (x ^ n) = 1
  rw [hexp x]
  exact (QuotientGroup.mk' N).map_one

/-- Finite products of finite abelian groups of bounded exponent again have bounded exponent.
@isnad1 id=finitepr.0h1v.s2.01d530e3bb8c from=translated src=- shape=76a08d12 vocab=34f72ca4
-/
theorem abelianExponent_finiteProductClosed (n : ℕ) :
    FiniteProductClosed (abelianExponent n) := by
  intro ι _ G _ hG
  refine ⟨?_, ?_, ?_⟩
  · let : ∀ i, Finite (G i) := fun i => (hG i).1
    infer_instance
  · intro a b
    funext i
    exact (hG i).2.1 (a i) (b i)
  · intro g
    funext i
    exact (hG i).2.2 (g i)

/-- abelianExponent is a finite-group variety.
@isnad1 id=variety.0h1v.s2.25f1c1974422 from=translated src=- shape=76a08d12 vocab=95fe8467
-/
theorem abelianExponent_variety (n : ℕ) : Variety (abelianExponent n) := by
  refine ⟨abelianExponent_subgroupClosed n,
    abelianExponent_quotientClosed n, abelianExponent_finiteProductClosed n⟩

/-- Finite abelian groups of exponent dividing \(n\) are closed under isomorphism.
@isnad1 id=isomclos.0h1v.s2.6f75d8a6b699 from=translated src=- shape=76a08d12 vocab=3e857920
-/
theorem abelianExponent_isomClosed (n : ℕ) : IsomClosed (abelianExponent n) := by
  intro G H _ _ hGH hG
  rcases hGH with ⟨e⟩
  rcases hG with ⟨hfin, hcomm, hexp⟩
  refine ⟨Finite.of_equiv G e.toEquiv, ?_, ?_⟩
  · intro a b
    have h := hcomm (e.symm a) (e.symm b)
    simpa using congrArg e h
  · intro a
    have h := hexp (e.symm a)
    simpa using congrArg e h

/-- Finite abelian groups of exponent dividing \(n\) form a formation.
@isnad1 id=formatio.0h1v.s2.af85b90bfd31 from=translated src=- shape=76a08d12 vocab=79840793
-/
theorem abelianExponent_formation (n : ℕ) : Formation (abelianExponent n) :=
  variety_formation (abelianExponent_variety n) (abelianExponent_isomClosed n)

/-- Finite cyclic groups are closed under isomorphism.
@isnad1 id=isomclos.0h0v.s1.b8db7462f58b from=translated src=- shape=49959d42 vocab=d06d802c
-/
theorem cyclic_isomClosed : IsomClosed cyclic := by
  intro G H _ _ hGH hG
  rcases hGH with ⟨e⟩
  rcases hG with ⟨hfin, hcyc⟩
  refine ⟨Finite.of_equiv G e.toEquiv, ?_⟩
  exact isCyclic_of_surjective e e.surjective

/-- Finite cyclic groups are closed under quotients.
@isnad1 id=quotient.0h0v.s1.dd7bcd6e963a from=translated src=- shape=49959d42 vocab=685f2707
-/
theorem cyclic_quotientClosed : QuotientClosed cyclic := by
  intro G _ N _ hG
  rcases hG with ⟨hfin, hcyc⟩
  refine ⟨?_, ?_⟩
  · infer_instance
  · exact isCyclic_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- Finite solvable groups are closed under isomorphism.
@isnad1 id=isomclos.0h0v.s1.6b2ee6c6c689 from=translated src=- shape=49959d42 vocab=543d4809
-/
theorem solvable_isomClosed : IsomClosed solvable := by
  intro G H _ _ hGH hG
  rcases hGH with ⟨e⟩
  rcases hG with ⟨hfin, hsolv⟩
  refine ⟨Finite.of_equiv G e.toEquiv, ?_⟩
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

/-- Finite solvable groups are closed under quotients.
@isnad1 id=quotient.0h0v.s1.25560505a161 from=translated src=- shape=49959d42 vocab=3a3c566a
-/
theorem solvable_quotientClosed : QuotientClosed solvable := by
  intro G _ N _ hG
  rcases hG with ⟨hfin, hsolv⟩
  refine ⟨?_, ?_⟩
  · infer_instance
  · infer_instance

/-- Finite nilpotent groups are closed under isomorphism.
@isnad1 id=isomclos.0h0v.s1.da8e342c8354 from=translated src=- shape=49959d42 vocab=65052031
-/
theorem nilpotent_isomClosed : IsomClosed nilpotent := by
  intro G H _ _ hGH hG
  rcases hGH with ⟨e⟩
  rcases hG with ⟨hfin, hnil⟩
  refine ⟨Finite.of_equiv G e.toEquiv, ?_⟩
  exact Group.nilpotent_of_mulEquiv e

/-- Finite nilpotent groups are closed under quotients.
@isnad1 id=quotient.0h0v.s1.45a8e89ad3e2 from=translated src=- shape=49959d42 vocab=8d0726a4
-/
theorem nilpotent_quotientClosed : QuotientClosed nilpotent := by
  intro G _ N _ hG
  rcases hG with ⟨hfin, hnil⟩
  refine ⟨?_, ?_⟩
  · infer_instance
  · infer_instance

/-- Every finite cyclic group is finite nilpotent.
@isnad1 id=pred.0h2v.s3.3267061f9a2e from=translated src=- shape=05c25b1e vocab=c0733b78
-/
theorem cyclic_to_nilpotent {G : Type u} [Group G] :
    cyclic G → nilpotent G := by
  rintro ⟨hfin, hcyc⟩
  refine ⟨hfin, ?_⟩
  exact ⟨⟨1, (Subgroup.upperCentralSeries_one_eq_top_iff (G := G)).mpr
    (IsCyclic.isMulCommutative (α := G))⟩⟩

/-- Every finite cyclic group belongs to the finite solvable class.
@isnad1 id=pred.0h2v.s3.95050a0b0ca9 from=translated src=- shape=05c25b1e vocab=2a2d6557
-/
theorem cyclic_to_solvable {G : Type u} [Group G] :
    cyclic G → solvable G := by
  rintro ⟨hfin, hcyc⟩
  have hnil : Group.IsNilpotent G := (cyclic_to_nilpotent ⟨hfin, hcyc⟩).2
  exact ⟨hfin, (inferInstance : Group.IsSolvable G)⟩

/-- Every finite \(p\)-group belongs to the finite nilpotent class.
@isnad1 id=pred.0h3v.s4.0e423a3856dc from=translated src=- shape=3b3d60e0 vocab=879fccdc
-/
theorem pGroup_to_nilpotent {p : ℕ} [Fact (Nat.Prime p)] {G : Type u} [Group G] :
    pGroup p G → nilpotent G := by
  rintro ⟨hfin, hpG⟩
  exact ⟨hfin, hpG.isNilpotent⟩

/-- Every finite \(p\)-group belongs to the finite solvable class.
@isnad1 id=pred.0h3v.s4.4c1d497fe2c6 from=translated src=- shape=3b3d60e0 vocab=69f288e7
-/
theorem pGroup_to_solvable {p : ℕ} [Fact (Nat.Prime p)] {G : Type u} [Group G] :
    pGroup p G → solvable G := by
  rintro ⟨hfin, hpG⟩
  refine ⟨hfin, ?_⟩
  let : Group.IsNilpotent G := hpG.isNilpotent
  infer_instance

end FiniteGroupClass

end ProCGroups
