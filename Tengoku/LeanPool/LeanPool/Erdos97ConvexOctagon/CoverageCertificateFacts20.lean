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

/-- Root audit for fixed branch (0, 20).
@isnad1 id=eq.0h0v.s5.ba64654a8ff5 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_20 :
    branchClaimRootValidB 0 20 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 3).
@isnad1 id=eq.0h0v.s5.accab5d4e336 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_5_03 :
    branchClaimRootValidB 5 3 (.patternThree 180) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 17).
@isnad1 id=eq.0h0v.s5.63f2bc2972ec from=translated src=- shape=e9e0773c vocab=2b68c0a0
-/
theorem coverageBranchRoot_2_17 :
    branchClaimRootValidB 2 17 (.search branchClaims2Row17) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 18).
@isnad1 id=eq.0h0v.s5.ae72d91bd500 from=translated src=- shape=e9e0773c vocab=9e056ca6
-/
theorem coverageBranchRoot_2_18 :
    branchClaimRootValidB 2 18 (.search branchClaims2Row18) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 17), starting at 0.
@isnad1 id=eq.0h0v.s3.c428e17be81e from=translated src=- shape=6f582f20 vocab=24e4ec77
-/
theorem coverageBranchNodes_2_17_00000 :
    nodeClaimChunkValidB branchClaims2Row17 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 17), starting at 64.
@isnad1 id=eq.0h0v.s3.3482504485cc from=translated src=- shape=6f582f20 vocab=24e4ec77
-/
theorem coverageBranchNodes_2_17_00064 :
    nodeClaimChunkValidB branchClaims2Row17 64 60 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 18), starting at 0.
@isnad1 id=eq.0h0v.s3.8bfba9419edc from=translated src=- shape=6f582f20 vocab=6056e36d
-/
theorem coverageBranchNodes_2_18_00000 :
    nodeClaimChunkValidB branchClaims2Row18 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 18), starting at 64.
@isnad1 id=eq.0h0v.s3.abc5c20160c5 from=translated src=- shape=6f582f20 vocab=6056e36d
-/
theorem coverageBranchNodes_2_18_00064 :
    nodeClaimChunkValidB branchClaims2Row18 64 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
