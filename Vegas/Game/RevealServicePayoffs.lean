/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.ResolutionProvenance
import Vegas.Game.RevealService
import Vegas.Game.ServiceSettledEvidence
import Vegas.Pending.ReactiveSelectionObservation
import Vegas.Game.RevealServiceWatcher
import Vegas.Pending.CompletionService
import Interaction.ReactiveRoundReachability
import Vegas.Compile.EventGraphReadout
import Vegas.Pending.RevealTranscript
import GameTheoryExtensions.Analysis.Enforcement

/-! # Net utilities for the monitored reveal service

One collectible deposit per ordinary player is charged at settlement when a
packet it signed, on the ledger or in the watcher's report, is forbidden by the
settled record. The utility and deposit are fixed before choosing an
equilibrium. Reporting has no separate payment here; the watcher retains its
declared base utility and must be indifferent for the watcher-extension theorem.

The comparison tolerates arbitrary outcomes after an extra response, including
communication that a recipient reads before the watcher reports. Its probability
bound concerns actual collection evidence, supplied by the monitored service.
The deduction models collection in utility units, not an implementation of escrow.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Configured

variable (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- Decode the existing typed terminal store, retaining initial private cells
jointly with the public results. An unfinished execution has no readout. -/
def serviceSourceReadout (state : (serviceApplication setup mode deadline leaks).ProtocolState) :
    Option (State L setup.program.terminalCtx) :=
  state.bind fun control =>
    let config := control.execution.application.config
    if config.cut.Terminal then
      Vegas.decodeState? (Vegas.terminalRefs setup.program) config.store
    else none

/-- Analysis utility of the actual terminal source readout, prior to a deposit
deduction. Initial private types may affect this utility. -/
def serviceBaseUtility (utility : State L setup.program.terminalCtx → Player → ℝ)
    (state : (serviceApplication setup mode deadline leaks).ProtocolState) (who : Player) : ℝ :=
  (serviceSourceReadout setup mode deadline leaks state).elim 0 (fun source => utility source who)

end Configured

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The terminal readout of the default runtime. -/
abbrev sourceReadout : (application setup leaks).ProtocolState →
    Option (State L setup.program.terminalCtx) :=
  serviceSourceReadout setup .sequential (rankDeadline setup .sequential) leaks

theorem sourceReadout_normalization (state : (application setup leaks).ProtocolState) :
    sourceReadout setup leaks (((runtime setup).reactiveNormalization leaks).state state) =
      sourceReadout setup leaks state := by
  cases state <;> rfl

theorem sourceReadout_eq_some (control : (application setup leaks).Control)
    (terminal : control.execution.application.config.cut.Terminal)
    (source : State L setup.program.terminalCtx)
    (agree : (Vegas.terminalRefs setup.program).Agrees source
      control.execution.application.config.store) :
    sourceReadout setup leaks (some control) = some source := by
  unfold sourceReadout serviceSourceReadout
  rw [Option.bind_some, ite_eq_left terminal]
  exact Vegas.decodeState?_eq_some _ source _ agree

/-- The base utility of the default runtime. -/
abbrev baseUtility : (State L setup.program.terminalCtx → Player → ℝ) →
    (application setup leaks).ProtocolState → Player → ℝ :=
  serviceBaseUtility setup .sequential (rankDeadline setup .sequential) leaks

theorem baseUtility_normalization (utility : State L setup.program.terminalCtx → Player → ℝ)
    (state : (application setup leaks).ProtocolState) :
    baseUtility setup leaks utility (((runtime setup).reactiveNormalization leaks).state state) =
      baseUtility setup leaks utility state := by
  unfold baseUtility serviceBaseUtility
  simp only [sourceReadout_normalization]

theorem baseUtility_watcher (utility : State L setup.program.terminalCtx → Player → ℝ)
    (watcher : Player) (indifferent : ∀ source, utility source watcher = 0)
    (state : (application setup leaks).ProtocolState) :
    baseUtility setup leaks utility state watcher = 0 := by
  unfold baseUtility serviceBaseUtility
  cases serviceSourceReadout setup .sequential (rankDeadline setup .sequential) leaks state <;>
    simp only [Option.elim_none, Option.elim_some, indifferent]

omit [DecidableEq Player] in
private theorem cast_option_map {α β : Type} (same : α = β) (value : Option α) :
    cast (congrArg Option same) value = value.map (cast same) := by
  cases same
  cases value <;> rfl

/-- Every entry of a canonical publication transcript is permitted by the
settled record of a reachable execution: the record accepted it, it carries
its exact certificate, and its value passes its event's checks on the settled
public store. -/
theorem publicationLedger_permitted (execution : (application setup leaks).Execution)
    (inputs : (graph setup).Inputs)
    (reachable : execution.application.config.Reachable inputs)
    (accepted : AcceptedHandles (graph setup))
    (ledger : execution.network.ledger =
      publicationLedger accepted ((graph setup).publicObserve execution.application.config))
    (receipts : execution.receipts =
      publicationReceipts accepted ((graph setup).publicObserve execution.application.config))
    (message : Message Player (WitnessedPacket (graph setup)))
    (member : message ∈ execution.network.ledger) :
    ((runtime setup).settledRecord leaks execution).permits message = true := by
  let config := execution.application.config
  have certified := publicationLedger_certified accepted _ message (ledger ▸ member)
  have decoded : (message.sender, message.payload) ∈
      publicationPackets accepted ((graph setup).publicObserve config) := by
    have inLedger : message ∈ publicationLedger accepted ((graph setup).publicObserve config) :=
      ledger ▸ member
    rw [← RevealTranscript.numberPackets_decode (fun _ : Player => 0)
      (publicationPackets accepted ((graph setup).publicObserve config))]
    exact List.mem_map_of_mem inLedger
  obtain ⟨event, _, encoded⟩ := List.mem_filterMap.mp decoded
  change publicationPacket? accepted ((graph setup).publicStore config.store) event = _ at encoded
  rw [publicationPacket?_publicStore] at encoded
  have acceptedId : ((runtime setup).settledRecord leaks execution).Accepts message.id := by
    change (message.id, true) ∈ execution.receipts
    rw [receipts]
    exact List.mem_map_of_mem (ledger ▸ member)
  unfold publicationPacket? at encoded
  split at encoded
  · cases encoded
  · cases encoded
  · rename_i owner payload binding checks outputEq codeEq node
    split at encoded
    · cases encoded
    · cases encoded
    · rename_i value stored
      obtain ⟨candidate, _, packet⟩ := Option.map_eq_some_iff.mp encoded
      rcases message with ⟨id, call, evidence, token⟩
      cases Prod.ext_iff.mp packet |>.2
      have published : (⟨.inr event, outputEq⟩ :
          EventGraph.FieldRef (graph setup).layout (.publication payload)).get?
            config.store = some (.success value) :=
        (cast_option_map (congrArg EventGraph.EventField.Value outputEq) _).trans stored
      have guards := EventGraph.Config.Reachable.publication_guards reachable event owner payload
        binding checks outputEq codeEq value published
      refine SettledRecord.permits_of_accepted _ _ event rfl acceptedId ⟨certified, ?_⟩
      refine (PublicView.openingGuardsAccepted_iff _ owner event payload binding checks outputEq
        codeEq node candidate _ _).mpr ⟨value, rfl, ?_⟩
      change EventGraph.GuardCheck.allAccepted? checks ((graph setup).publicStore config.store)
        (.success value) = some true
      rw [EventGraph.GuardCheck.allAccepted?_publicStore]
      exact guards

end Vegas
