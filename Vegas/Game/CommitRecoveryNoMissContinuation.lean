/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryNoMissRepresentative
import Vegas.Source.CommitRecoveryErasedModel

/-! # Original source continuation under the selected reduced-query prescription

The legal source profile reads its value law at the genuine no-new-omission
query with remembered private words erased. Its failed-attempt continuation
uses the original terminal runner, retaining all future failure and rescue
branches.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Read a source prescription at the genuine no-new-omission query, while
transporting the same underlying action back to the original legal menu. -/
def commitRecoveryNoMissProfile
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∀ who, setup.commitRecoveryModel.BehavioralPolicy who := fun who info =>
  (profile who (setup.commitRecoveryNoMissInformation who info)).map
    (setup.commitRecoveryNoMissChoice who info).symm

theorem commitRecoveryNoMissProfile_raw
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    (setup.commitRecoveryNoMissProfile profile who info).map Subtype.val =
      (profile who (setup.commitRecoveryNoMissInformation who info)).map Subtype.val := by
  rw [commitRecoveryNoMissProfile, PMF.map_comp]
  rfl

/-- This profile belongs to the original full-information source game. Its
query is the combined reduced label; its runner and observations are unchanged. -/
def commitRecoveryNoMissErasedProfile
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∀ who, setup.commitRecoveryModel.BehavioralPolicy who :=
  setup.commitRecoveryErasedProfile (setup.commitRecoveryNoMissProfile profile)

/-- The actual selected policy reads exactly the combined source query,
without assuming a raw-law equality or changing the legal action. -/
theorem commitRecoveryNoMissErasedProfile_raw
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    (setup.commitRecoveryNoMissErasedProfile profile who info).map Subtype.val =
      (profile who (setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who info))).map Subtype.val := by
  rw [commitRecoveryNoMissErasedProfile, setup.commitRecoveryErasedProfile_raw,
    setup.commitRecoveryNoMissProfile_raw, ← setup.commitRecoveryNoMissInformation_erased]

variable [Fintype Player]

end Vegas.SourceProgram.Setup
