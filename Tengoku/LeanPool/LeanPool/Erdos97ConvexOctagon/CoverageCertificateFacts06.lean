/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00
public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 6).
@isnad1 id=eq.0h0v.s5.eadefcc113b2 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_06 :
    branchClaimRootValidB 0 6 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 24).
@isnad1 id=eq.0h0v.s5.a746269d9680 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_24 :
    branchClaimRootValidB 4 24 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 27).
@isnad1 id=eq.0h0v.s5.ebdb8ce995b3 from=translated src=- shape=e9e0773c vocab=bbc91f75
-/
theorem coverageBranchRoot_1_27 :
    branchClaimRootValidB 1 27 (.search branchClaims1Row27) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 26), starting at 64.
@isnad1 id=eq.0h0v.s3.3a6754e4dc26 from=translated src=- shape=6f582f20 vocab=b8ef7906
-/
theorem coverageBranchNodes_1_26_00064 :
    nodeClaimChunkValidB branchClaims1Row26 64 53 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 27), starting at 0.
@isnad1 id=eq.0h0v.s3.56ef584a1926 from=translated src=- shape=6f582f20 vocab=b9cf6da7
-/
theorem coverageBranchNodes_1_27_00000 :
    nodeClaimChunkValidB branchClaims1Row27 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 27), starting at 64.
@isnad1 id=eq.0h0v.s3.16217f056262 from=translated src=- shape=6f582f20 vocab=b9cf6da7
-/
theorem coverageBranchNodes_1_27_00064 :
    nodeClaimChunkValidB branchClaims1Row27 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 27), starting at 128.
@isnad1 id=eq.0h0v.s3.3f89575e7198 from=translated src=- shape=6f582f20 vocab=b9cf6da7
-/
theorem coverageBranchNodes_1_27_00128 :
    nodeClaimChunkValidB branchClaims1Row27 128 36 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
