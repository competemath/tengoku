/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 5).
@isnad1 id=eq.0h0v.s5.f5fef4fe6822 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_05 :
    branchClaimRootValidB 0 5 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 23).
@isnad1 id=eq.0h0v.s5.34332894843f from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_23 :
    branchClaimRootValidB 4 23 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 19).
@isnad1 id=eq.0h0v.s5.78d06de09cca from=translated src=- shape=e9e0773c vocab=feb5aec9
-/
theorem coverageBranchRoot_1_19 :
    branchClaimRootValidB 1 19 (.search branchClaims1Row19) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 26).
@isnad1 id=eq.0h0v.s5.907934ed0426 from=translated src=- shape=e9e0773c vocab=0fdd60b0
-/
theorem coverageBranchRoot_1_26 :
    branchClaimRootValidB 1 26 (.search branchClaims1Row26) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 18), starting at 64.
@isnad1 id=eq.0h0v.s3.f8becc73990e from=translated src=- shape=6f582f20 vocab=fe9b8a3f
-/
theorem coverageBranchNodes_1_18_00064 :
    nodeClaimChunkValidB branchClaims1Row18 64 42 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 19), starting at 0.
@isnad1 id=eq.0h0v.s3.b03ec93b5376 from=translated src=- shape=6f582f20 vocab=a7ac00f5
-/
theorem coverageBranchNodes_1_19_00000 :
    nodeClaimChunkValidB branchClaims1Row19 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 19), starting at 64.
@isnad1 id=eq.0h0v.s3.f61fd64f7062 from=translated src=- shape=6f582f20 vocab=a7ac00f5
-/
theorem coverageBranchNodes_1_19_00064 :
    nodeClaimChunkValidB branchClaims1Row19 64 53 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 26), starting at 0.
@isnad1 id=eq.0h0v.s3.b17a2349d775 from=translated src=- shape=6f582f20 vocab=b8ef7906
-/
theorem coverageBranchNodes_1_26_00000 :
    nodeClaimChunkValidB branchClaims1Row26 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
