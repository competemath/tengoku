/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 19).
@isnad1 id=eq.0h0v.s5.79004f00f6b2 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_19 :
    branchClaimRootValidB 0 19 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 2).
@isnad1 id=eq.0h0v.s5.1a67b73d6a8c from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_5_02 :
    branchClaimRootValidB 5 2 (.patternThree 180) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 15).
@isnad1 id=eq.0h0v.s5.d9ea90b046b1 from=translated src=- shape=e9e0773c vocab=30bf6ad8
-/
theorem coverageBranchRoot_2_15 :
    branchClaimRootValidB 2 15 (.search branchClaims2Row15) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 15), starting at 0.
@isnad1 id=eq.0h0v.s3.e637abf413f3 from=translated src=- shape=6f582f20 vocab=2341995b
-/
theorem coverageBranchNodes_2_15_00000 :
    nodeClaimChunkValidB branchClaims2Row15 0 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 15), starting at 32.
@isnad1 id=eq.0h0v.s3.ac4d1eaf00b7 from=translated src=- shape=6f582f20 vocab=2341995b
-/
theorem coverageBranchNodes_2_15_00032 :
    nodeClaimChunkValidB branchClaims2Row15 32 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 15), starting at 64.
@isnad1 id=eq.0h0v.s3.1604d67025a7 from=translated src=- shape=6f582f20 vocab=2341995b
-/
theorem coverageBranchNodes_2_15_00064 :
    nodeClaimChunkValidB branchClaims2Row15 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 15), starting at 128.
@isnad1 id=eq.0h0v.s3.08df04323011 from=translated src=- shape=6f582f20 vocab=2341995b
-/
theorem coverageBranchNodes_2_15_00128 :
    nodeClaimChunkValidB branchClaims2Row15 128 7 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
