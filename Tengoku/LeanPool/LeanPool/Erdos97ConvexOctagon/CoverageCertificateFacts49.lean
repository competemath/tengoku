/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07
public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData08
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 24).
@isnad1 id=eq.0h0v.s5.9aefd37480e6 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_24 :
    branchClaimRootValidB 1 24 (.patternThree 179) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 10).
@isnad1 id=eq.0h0v.s5.fb76db2630d1 from=translated src=- shape=e9e0773c vocab=7cc68e56
-/
theorem coverageBranchRoot_5_10 :
    branchClaimRootValidB 5 10 (.search branchClaims5Row10) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 9), starting at 64.
@isnad1 id=eq.0h0v.s3.c08b18fb6b3e from=translated src=- shape=6f582f20 vocab=683c499f
-/
theorem coverageBranchNodes_5_09_00064 :
    nodeClaimChunkValidB branchClaims5Row9 64 22 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 10), starting at 0.
@isnad1 id=eq.0h0v.s3.1d73f687c976 from=translated src=- shape=6f582f20 vocab=c08afbd3
-/
theorem coverageBranchNodes_5_10_00000 :
    nodeClaimChunkValidB branchClaims5Row10 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 10), starting at 64.
@isnad1 id=eq.0h0v.s3.74951c267c40 from=translated src=- shape=6f582f20 vocab=c08afbd3
-/
theorem coverageBranchNodes_5_10_00064 :
    nodeClaimChunkValidB branchClaims5Row10 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 10), starting at 128.
@isnad1 id=eq.0h0v.s3.2aa19e904629 from=translated src=- shape=6f582f20 vocab=c08afbd3
-/
theorem coverageBranchNodes_5_10_00128 :
    nodeClaimChunkValidB branchClaims5Row10 128 31 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
