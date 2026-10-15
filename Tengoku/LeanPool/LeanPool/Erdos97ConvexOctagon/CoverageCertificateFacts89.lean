/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData14
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 13).
@isnad1 id=eq.0h0v.s5.67d6cf931f86 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_13 :
    branchClaimRootValidB 4 13 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 28).
@isnad1 id=eq.0h0v.s5.31fddec5f4b8 from=translated src=- shape=e9e0773c vocab=a8942de9
-/
theorem coverageBranchRoot_6_28 :
    branchClaimRootValidB 6 28 (.search branchClaims6Row28) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 28), starting at 0.
@isnad1 id=eq.0h0v.s3.5d1d22b3e777 from=translated src=- shape=6f582f20 vocab=1f428a37
-/
theorem coverageBranchNodes_6_28_00000 :
    nodeClaimChunkValidB branchClaims6Row28 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 28), starting at 64.
@isnad1 id=eq.0h0v.s3.fe53b7b8186e from=translated src=- shape=6f582f20 vocab=1f428a37
-/
theorem coverageBranchNodes_6_28_00064 :
    nodeClaimChunkValidB branchClaims6Row28 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 28), starting at 128.
@isnad1 id=eq.0h0v.s3.f55fd3603d61 from=translated src=- shape=6f582f20 vocab=1f428a37
-/
theorem coverageBranchNodes_6_28_00128 :
    nodeClaimChunkValidB branchClaims6Row28 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 28), starting at 192.
@isnad1 id=eq.0h0v.s3.4f121353d9cd from=translated src=- shape=6f582f20 vocab=1f428a37
-/
theorem coverageBranchNodes_6_28_00192 :
    nodeClaimChunkValidB branchClaims6Row28 192 13 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
