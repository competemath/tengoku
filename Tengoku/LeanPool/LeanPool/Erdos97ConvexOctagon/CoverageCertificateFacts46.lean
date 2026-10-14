/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 21).
@isnad1 id=eq.0h0v.s5.1f2b230bdb74 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_21 :
    branchClaimRootValidB 1 21 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 4).
@isnad1 id=eq.0h0v.s5.7a5b03ae7495 from=translated src=- shape=e9e0773c vocab=38ae8664
-/
theorem coverageBranchRoot_5_04 :
    branchClaimRootValidB 5 4 (.search branchClaims5Row4) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 5).
@isnad1 id=eq.0h0v.s5.788e45bc2175 from=translated src=- shape=e9e0773c vocab=1472ba91
-/
theorem coverageBranchRoot_5_05 :
    branchClaimRootValidB 5 5 (.search branchClaims5Row5) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 32), starting at 256.
@isnad1 id=eq.0h0v.s3.0a551d9ebf69 from=translated src=- shape=6f582f20 vocab=366eccd2
-/
theorem coverageBranchNodes_3_32_00256 :
    nodeClaimChunkValidB branchClaims3Row32 256 12 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 4), starting at 0.
@isnad1 id=eq.0h0v.s3.65d212546fd1 from=translated src=- shape=6f582f20 vocab=c43f40e9
-/
theorem coverageBranchNodes_5_04_00000 :
    nodeClaimChunkValidB branchClaims5Row4 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 4), starting at 64.
@isnad1 id=eq.0h0v.s3.730d2046146d from=translated src=- shape=6f582f20 vocab=c43f40e9
-/
theorem coverageBranchNodes_5_04_00064 :
    nodeClaimChunkValidB branchClaims5Row4 64 50 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 5), starting at 0.
@isnad1 id=eq.0h0v.s3.833c169d658e from=translated src=- shape=6f582f20 vocab=b557c68f
-/
theorem coverageBranchNodes_5_05_00000 :
    nodeClaimChunkValidB branchClaims5Row5 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
