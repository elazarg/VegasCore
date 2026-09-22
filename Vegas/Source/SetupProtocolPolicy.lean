/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.SetupProtocol

/-! # One source policy across private setup draws

The extra setup position has exactly the inactive choice. All actual decisions
use the original source policy on its own view, uniformly across the setup law.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def toProtocolPolicy (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (who : Player)
    (policy : PurePolicy who setup.program) (permitted : policy.Admitted setup.program admission) :
    (setup.informationModel admission).Policy who
  | none => ⟨none, rfl⟩
  | some view => policy.toProtocol setup.program admission permitted view

/-- A playerwise equivalence; no initial draw is an input to the translation.
The inverse covers every information-local continuation deviation. -/
def purePolicyEquiv (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (who : Player) :
    {policy : PurePolicy who setup.program // policy.Admitted setup.program admission} ≃
      (setup.informationModel admission).Policy who where
  toFun policy := setup.toProtocolPolicy admission who policy.1 policy.2
  invFun policy :=
    ⟨PurePolicy.fromProtocol setup.program admission (fun view => policy (some view)),
      PurePolicy.admitted_fromProtocol setup.program admission (fun view => policy (some view))⟩
  left_inv policy :=
    Subtype.ext (PurePolicy.from_toProtocol setup.program admission policy.1 policy.2)
  right_inv policy := by
    funext view
    apply Subtype.ext
    cases view with
    | none => exact (policy none).2.symm
    | some view =>
        exact PurePolicy.protocolAction_fromProtocol setup.program admission
          (fun view => policy (some view)) view

end Vegas.SourceProgram.Setup
