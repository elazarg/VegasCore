/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourcePhaseClient
import Interaction.ReactiveResponseEvaluation
import Vegas.Pending.PhaseFirstResponseRecall
import Vegas.Game.SourcePhaseObservation

/-! # Actual laws of maximal-phase source clients

The arbitrary original source policies are compiled player by player. Their
actual raw runtime law retains the whole physical control, including private
catalogues, network, receipts and recall, when restricted to the one-packet
menu. This derives counted histories and zero count-audit charges for actual
client play; it does not assert an original source joint-law correspondence.
-/

noncomputable section

namespace Vegas.SourcePhaseClient

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (serviceGraph setup .sequential))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket (serviceGraph setup .sequential)))
  (bounds : MessageBounds (serviceGraph setup .sequential))

local notation "app" => phaseApplication runtime leaks
local notation "raw" => PhaseCount.rawMenu runtime leaks bounds
local notation "counted" => PhaseCount.onePacketMenu runtime leaks bounds

/-- The same actual client policies, represented in the one-packet menu. -/
def countedProfile (horizon : Nat) (scheduler : (app).Scheduler)
    (source : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∀ who, ((counted).information (initial setup runtime leaks) horizon scheduler).BehavioralPolicy
      who :=
  fun who => (counted).restrictPolicy (initial setup runtime leaks) horizon scheduler who
    (policy setup runtime leaks bounds who (source who))

/-- At every prefix length the whole physical control law agrees. Both sides
use the original actual transition and the same source policy at every player. -/
theorem raw_control_law_eq_counted (horizon : Nat) (scheduler : (app).Scheduler)
    (source : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (fuel : Nat) :
    (((raw).information (initial setup runtime leaks) horizon scheduler).runBehavioral
      (compileProfile setup runtime leaks bounds horizon scheduler source) fuel).map History.state =
      (((counted).information (initial setup runtime leaks) horizon scheduler).runBehavioral
        (countedProfile setup runtime leaks bounds horizon scheduler source) fuel).map
          History.state := by
  let clients := fun who => policy setup runtime leaks bounds who (source who)
  have rawLaw := (raw).run_restrict_control_steps (initial setup runtime leaks) horizon scheduler
    clients (fun who _ _ _ response supported => policy_raw_covered setup runtime leaks bounds
      who (source who) _ _ response supported) fuel
        ((raw).protocol (initial setup runtime leaks) horizon scheduler).initHistory
  have countedLaw := (counted).run_restrict_control_steps (initial setup runtime leaks) horizon
    scheduler clients (fun who _ _ _ response supported => policy_covered setup runtime leaks
      bounds who (source who) _ _ response supported) fuel
        ((counted).protocol (initial setup runtime leaks) horizon scheduler).initHistory
  exact rawLaw.trans countedLaw.symm

/-- Every actual raw client outcome has an actual counted history with exactly
that entire physical control. No desired source-history law is assumed. -/
theorem supported_counted_history (horizon : Nat) (scheduler : (app).Scheduler)
    (source : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (fuel : Nat)
    (history : ((raw).protocol (initial setup runtime leaks) horizon scheduler).History)
    (supported : history ∈ (((raw).information (initial setup runtime leaks) horizon
      scheduler).runBehavioral
        (compileProfile setup runtime leaks bounds horizon scheduler source) fuel).support) :
    ∃ countedHistory : ((counted).protocol (initial setup runtime leaks) horizon scheduler).History,
      history.state = countedHistory.state := by
  have stateSupported : history.state ∈
      ((((raw).information (initial setup runtime leaks) horizon scheduler).runBehavioral
        (compileProfile setup runtime leaks bounds horizon scheduler source) fuel).map
          History.state).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨history, supported, rfl⟩
  rw [raw_control_law_eq_counted setup runtime leaks bounds horizon scheduler source fuel]
    at stateSupported
  obtain ⟨countedHistory, _drawn, same⟩ := (PMF.mem_support_map_iff _ _ _).mp stateSupported
  exact ⟨countedHistory, same.symm⟩

theorem supported_counted_trace (horizon : Nat) (scheduler : (app).Scheduler)
    (source : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (fuel : Nat)
    (history : ((raw).protocol (initial setup runtime leaks) horizon scheduler).History)
    (supported : history ∈ (((raw).information (initial setup runtime leaks) horizon
      scheduler).runBehavioral
        (compileProfile setup runtime leaks bounds horizon scheduler source) fuel).support)
    (control : (app).Control) (atState : history.state = some control) :
    Nonempty (((counted).protocol (initial setup runtime leaks) horizon scheduler).Trace
      (some control)) := by
  obtain ⟨countedHistory, same⟩ := supported_counted_history setup runtime leaks bounds horizon
    scheduler source fuel history supported
  exact ⟨(same.symm.trans atState) ▸ countedHistory.trace⟩

/-- The authentic physical count audit charges nobody at any prefix of actual
source-client play, including intentional source omissions and later retries. -/
theorem supported_countCharge_zero (horizon : Nat) (scheduler : (app).Scheduler)
    (source : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (fuel : Nat)
    (history : ((raw).protocol (initial setup runtime leaks) horizon scheduler).History)
    (supported : history ∈ (((raw).information (initial setup runtime leaks) horizon
      scheduler).runBehavioral
        (compileProfile setup runtime leaks bounds horizon scheduler source) fuel).support)
    (service : EvidenceReportService (PhaseCount.Evidence (serviceGraph setup .sequential)))
    (who : Player) :
    TerminalAudit.charge (app).stateTraffic (PhaseCount.audit runtime leaks service.sample)
      history.state who = 0 := by
  obtain ⟨countedHistory, same⟩ := supported_counted_history setup runtime leaks bounds horizon
    scheduler source fuel history supported
  rw [same]
  exact PhaseCount.onePacketMenu_countCharge_zero runtime leaks bounds (initial setup runtime leaks)
    horizon scheduler service countedHistory who

/-- A first callback of any supported raw client prefix has no earlier emitted
packet for this attempt-event. This is derived from an actual counted trace. -/
theorem supported_first_unsent (horizon : Nat) (scheduler : (app).Scheduler)
    (source : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (fuel : Nat)
    (history : ((raw).protocol (initial setup runtime leaks) horizon scheduler).History)
    (supported : history ∈ (((raw).information (initial setup runtime leaks) horizon
      scheduler).runBehavioral
        (compileProfile setup runtime leaks bounds horizon scheduler source) fuel).support)
    (control : (app).Control) (atState : history.state = some control) (who : Player)
    (coordinate : CommitAttemptEvent (serviceGraph setup .sequential))
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks who coordinate
      (control.execution.recall who)) :
    ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some coordinate := by
  obtain ⟨countedTrace⟩ := supported_counted_trace setup runtime leaks bounds horizon scheduler
    source fuel history supported control atState
  have actualTrace : ((counted).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial (plan setup))) horizon
        scheduler).Trace (some control) := by
    rw [PMF.map_comp]
    exact countedTrace
  exact phase_unrecorded_request_unsent runtime leaks bounds (plan setup)
    (serviceGraph_revealRelaxedOrdered setup .sequential) (setup.initialLaw.map encodeInputs)
    horizon scheduler control actualTrace who coordinate first

end Vegas.SourcePhaseClient
