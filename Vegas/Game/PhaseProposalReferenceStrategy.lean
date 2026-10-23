/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalReference

/-! # The actual reference profile is fully mixed in the counted protocol -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "model" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- Represent the same actual full-input response law in the counted (model).
The generic restriction introduces no new behavior because coverage is global. -/
def phaseProposalReferenceStrategy
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) : (model).BehavioralPolicy who :=
  (menu).restrictPolicy initial horizon scheduler who
    (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates who)

/-- Forgetting only proof witnesses recovers the full native response law. -/
theorem phaseProposalReferenceStrategy_map_val
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    ((phaseProposalReferenceStrategy setup mode runtime leaks bounds plan initial horizon scheduler
        values rates who) (some (past, view))).map Subtype.val =
      (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates who past
        view).map some :=
  (menu).restrictPolicy_map_val initial horizon scheduler who _ past view
    (fun response supported => phaseProposalReferencePolicy_covered setup mode runtime leaks bounds
      plan values rates who past view response supported)

/-- EVERY counted action has positive probability at EVERY genuine decision,
including publication inputs reached only after omission or unusable binding
histories. No clean-history or all-proper-preparation assumption is imposed. -/
theorem phaseProposalReferenceStrategy_fullSupport
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (aliases : 0 < rates.aliases.val) :
    ∀ who (site : (model).InformationSite who) (choice : (model).Choice who site.1),
      choice ∈ (phaseProposalReferenceStrategy setup mode runtime leaks bounds plan initial horizon
        scheduler values rates who site.1).support := by
  apply (menu).restrictProfile_fullSupport initial horizon scheduler
    (fun who => phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates who)
  · intro who control _trace _active response supported
    exact phaseProposalReferencePolicy_covered setup mode runtime leaks bounds plan values rates who
      (control.execution.recall who)
      (control.execution.observe (phaseApplication runtime leaks) who) response supported
  · intro who control _trace _active response permitted
    exact phaseProposalReferencePolicy_fullSupport setup mode runtime leaks bounds plan values rates
      aliases who (control.execution.recall who)
      (control.execution.observe (phaseApplication runtime leaks) who) response permitted

end Vegas
