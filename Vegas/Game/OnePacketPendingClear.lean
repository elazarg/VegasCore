/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketEventSuccess
import Vegas.Pending.ExclusionNativeFailure
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # Pending committed events retain public clarity -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "protocol" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup)
  horizon scheduler
local notation "model" => ReactiveApplication.ResponseMenu.information menu (initialLaw setup)
  horizon scheduler

/-- From a clear configuration with the acceptance invariant, every actual
continuation remains publicly clear while the committed event is still pending.
This is independent of service, timing and the later response policies. -/
theorem pending_publicClear_of_acceptanceInvariant
    (certificate : (protocol).WellFoundedHistories)
    (profile : ∀ who, (model).BehavioralPolicy who) (stopped : (protocol).History → Prop)
    (who : Player) (entry : (application setup runtime leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup)))
    (event : (graph setup).EventId) (sent : (graph setup).Config)
    (start : (protocol).History) (current : (application setup runtime leaks).Control)
    (state : start.state = some current)
    (clear : ExclusionEvidence 0 ∅
      (RecoveryState.mk current.execution.application ∅))
    (invariant : AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry
      message event
      sent (some current)) :
    ∀ final ∈ ((model).runBehavioralUntil certificate profile stopped start).support,
      ∀ control, final.state = some control →
        event ∉ control.execution.application.config.cut.completed →
          ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) := by
  let property := fun state : (application setup runtime leaks).ProtocolState =>
    AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry message event sent
      state ∧
      match state with
      | none => False
      | some control => event ∉ control.execution.application.config.cut.completed →
          ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅)
  have preserved : ∀ before joint (legal : (protocol).Legal before joint) after,
      property before → after ∈ ((protocol).step before ⟨joint, legal⟩).support → property after :=
      by
    intro before joint legal after holds reached
    have nextInvariant := acceptanceInvariant_transition (runtime := runtime) bounds horizon
      scheduler who entry
      message event sent before after joint legal holds.1 reached
    change after ∈ ((application setup runtime leaks).transition (initialLaw setup) horizon
      scheduler
      before joint).support at reached
    cases before with
    | none => exact holds.1.elim
    | some current =>
      cases after with
      | none => exact nextInvariant.elim
      | some next =>
        refine ⟨nextInvariant, fun pending => ?_⟩
        have step := (reactiveApplication_completionStep runtime leaks).transition
          (initialLaw setup) horizon scheduler current next joint reached
        have beforePending : event ∉ current.execution.application.config.cut.completed :=
          fun completed => pending (step.completed_mono completed)
        have beforeAt := holds.1.2.2.2.2.2.1 beforePending
        have nextAt := nextInvariant.2.2.2.2.2.1 pending
        exact (holds.2 beforePending).completionStep_sameConfig step (nextAt.trans beforeAt.symm)
  have initialProperty : property start.state := by
    rw [state]
    exact ⟨invariant, fun _ => clear⟩
  have remains := (model).runBehavioralUntil_support_closed certificate profile stopped property
    (fun history _ _ => preserved history.state) start initialProperty
  intro final supported control finalState pending
  have clearIfPending := (remains final supported).2
  rw [finalState] at clearIfPending
  exact clearIfPending pending

end Vegas
