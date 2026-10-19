/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalGenuineSupport
import Vegas.Game.PhaseProposalReferenceStrategy

/-! # Actual genuine reference class law and full support -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (complete : leaks = MessageNetwork.completePendingObservation)
  (covered : bounds.CoversOutputValues)
  (maximal : plan.phases.IsChain fun first last =>
    first.kind ≠ last.kind ∨ first.kind = .sample)
  (values : ∀ who (key : setup.ProposalRecoveryComponent who),
    PMF (setup.CommitRecoveryValueChoice who key.1))
  (fullValues : ∀ who key, FullSupport (values who key))
  (rates : PhaseProposalRates) (waitPositive : 0 < rates.waiting.val)
  (waitBelow : rates.waiting.val < 1) (slotPositive : 0 < rates.slots.val)
  (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds

include complete covered maximal fullValues waitPositive waitBelow slotPositive badPositive badBelow

/-- Genuine counted history itself removes the support fallback. There is no
clean-history or source-counterpart premise, even after focal deviations. -/
theorem phaseProposalReferenceClasses_eq_of_counted
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩)) :
    phaseProposalReferenceClasses setup mode runtime leaks bounds plan values rates owner
        (execution.recall owner) (execution.observe app owner) =
      phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates owner
        (execution.recall owner) (execution.observe app owner) :=
  phaseProposalReferenceClasses_eq setup mode runtime leaks bounds plan values rates owner
    (execution.recall owner) (execution.observe app owner)
    (phaseProposalBaseClasses_fullSupport_of_counted setup mode runtime leaks bounds plan complete
      covered maximal values fullValues rates waitPositive waitBelow slotPositive badPositive
        badBelow horizon scheduler remaining owner execution trace)

/-- Summing the actual raw preimages yields the BASE class law at every genuine
counted input; support totalization never changes the physical reference. -/
theorem phaseProposalReferenceResponses_project_of_counted
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩)) :
    (phaseProposalReferenceResponses setup mode runtime leaks bounds plan values rates owner
      (execution.recall owner) (execution.observe app owner)).map
        (PhaseProposal.projectResponse runtime leaks bounds owner (execution.recall owner)
          (execution.observe app owner)) =
      phaseProposalBaseClasses setup mode runtime leaks bounds plan values rates owner
        (execution.recall owner) (execution.observe app owner) := by
  rw [phaseProposalReferenceResponses_project]
  exact phaseProposalReferenceClasses_eq_of_counted setup mode runtime leaks bounds plan complete
    covered maximal values fullValues rates waitPositive waitBelow slotPositive badPositive badBelow
    horizon scheduler remaining owner execution trace

end Vegas
