/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalAdmissionStore
import Vegas.Examples.CommitSeedBroadcastNativeContinuation
import Vegas.Pending.ReactiveSeedBindingReadout

/-! # Terminal loss from an admitted unusable original declaration -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- An actual unusable preparation's admitted native result remains the failed
original cell when all original packets are admitted. No future strategy is restricted. -/
theorem admitted_unusable_original_binding_stays_failed
    (selected : app.Scheduler) (before after final : app.Control)
    (prior : (countedMenu.protocol initial horizon selected).Trace (some before))
    (original : before.execution.application.attempt = originalAttempt)
    (joint : Player → Option app.Action)
    (legal : (countedMenu.protocol initial horizon selected).Legal (some before) joint)
    (moved : some after ∈ (app.transition initial horizon selected (some before) joint).support)
    (finalTrace : (countedMenu.protocol initial horizon selected).Trace (some final))
    (retained : TracePrefix (prior.extend joint legal moved) finalTrace)
    (admitted : ∀ owner, PhaseService.BindingAccepted runtime leaks
      (originalCoordinate owner) owner final.execution)
    (owner : Player) (entry : app.PlayerEntry) (recorded : entry ∈ before.execution.recall owner)
    (serial : Nat) (opening : Option (Raw simpleExpr)) (evidence : EvidenceRequest graph)
    (declared : entry.action =
      ⟨some ⟨⟨.commitment (bindingEvent owner) (owner, .prepared serial), opening⟩, evidence⟩⟩)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (unusable : (opening.bind fun raw => raw.as? .bool) = none)
    (message : Message Player (CommitAttemptPacket graph)) (native : EventGraphRuntime.State graph)
    (call : message.payload.packet.call =
      .commitment (bindingEvent owner) (owner, .prepared serial))
    (handled : handle runtime before.execution.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native)
    (included : before.execution.application.handle runtime message =
      some after.execution.application) :
    final.execution.application.current.native.config.outputs (bindingEvent owner) = some
      (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.failure : PublicationResult Bool)) := by
  have meaning := recorded_unusable_binding_result selected before prior owner entry recorded
    (bindingEvent owner) serial opening evidence declared fresh unusable
  have codeEq : cast (congrArg (EventCode graph.layout) (bindingEvent_layout owner))
      (graph.nodes (bindingEvent owner)) =
        EventCode.bind (L := simpleExpr) (layout := graph.layout) owner BaseTy.bool := by
    fin_cases owner <;> rfl
  have node : nodeView graph (bindingEvent owner) =
      .bind owner .bool (bindingEvent_layout owner) codeEq := by
    fin_cases owner <;> rfl
  have rawHandled : handle runtime before.execution.application.current.native
      ⟨message.id, .commitment (bindingEvent owner) (owner, .prepared serial)⟩ = some native := by
    simpa only [call] using handled
  obtain ⟨_ready, configEq⟩ := runtime.handle_commitment_config_result
    before.execution.application.current.native native message.id (bindingEvent owner)
      (owner, .prepared serial) owner .bool (bindingEvent_layout owner) codeEq node rawHandled
  have failed : native.config.outputs (bindingEvent owner) = some
      (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.failure : PublicationResult Bool)) := by
    rw [configEq, Config.complete_output_same, meaning]
  exact all_original_admissions_keep_included_store selected before after final prior original
    joint legal moved finalTrace retained admitted message native handled included
      (.inr (bindingEvent owner)) _ failed

/-- The preceding actual admitted failure gives the fixed loss at any genuine
completed counted endpoint; other owners may be excluded during publication. -/
theorem counted_failed_cell_terminal_payoff
    (execution : app.Execution) (trace : countedProtocol.Trace (some ⟨0, none, execution⟩))
    (owner : Player)
    (failed : execution.application.current.native.config.outputs (bindingEvent owner) = some
      (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.failure : PublicationResult Bool))) :
    netPayoff (app.finished execution) owner = -(3 / 2) := by
  have raw := countedMenu.toRawTrace initial horizon scheduler trace
  have complete := scheduler_completesPlay ⟨0, none, execution⟩ raw ⟨rfl, rfl⟩
  have valid := raw_native_valid scheduler ⟨0, none, execution⟩ raw
  have compiled := raw
  rw [initial_eq_compiled] at compiled
  have coverage := phaseFailureCoverage_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon scheduler compiled
  have published := failed_binding_publication execution.application.current.native valid.active
    complete owner failed
  have excluded := coverage.active.covered (revealEvent owner) owner (reveal_actor owner)
    (Or.inr published)
  rw [counted_endpoint_payoff execution trace owner, ite_eq_left excluded]

/-- Joint original admissions turn an actually admitted unusable preparation
into the fixed terminal loss, even if other owners later fail publication. -/
theorem admitted_unusable_original_binding_terminal_payoff
    (before after final : app.Control)
    (prior : (countedMenu.protocol initial horizon scheduler).Trace (some before))
    (original : before.execution.application.attempt = originalAttempt)
    (joint : Player → Option app.Action)
    (legal : (countedMenu.protocol initial horizon scheduler).Legal (some before) joint)
    (moved : some after ∈ (app.transition initial horizon scheduler (some before) joint).support)
    (finalTrace : (countedMenu.protocol initial horizon scheduler).Trace (some final))
    (retained : TracePrefix (prior.extend joint legal moved) finalTrace)
    (admitted : ∀ owner, PhaseService.BindingAccepted runtime leaks
      (originalCoordinate owner) owner final.execution)
    (owner : Player) (entry : app.PlayerEntry) (recorded : entry ∈ before.execution.recall owner)
    (serial : Nat) (opening : Option (Raw simpleExpr)) (evidence : EvidenceRequest graph)
    (declared : entry.action =
      ⟨some ⟨⟨.commitment (bindingEvent owner) (owner, .prepared serial), opening⟩, evidence⟩⟩)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (unusable : (opening.bind fun raw => raw.as? .bool) = none)
    (message : Message Player (CommitAttemptPacket graph)) (native : EventGraphRuntime.State graph)
    (call : message.payload.packet.call =
      .commitment (bindingEvent owner) (owner, .prepared serial))
    (handled : handle runtime before.execution.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native)
    (included : before.execution.application.handle runtime message =
      some after.execution.application)
    (terminal : final.remaining = 0 ∧ final.actor = none) :
    netPayoff (app.finished final.execution) owner = -(3 / 2) := by
  rcases final with ⟨remaining, actor, execution⟩
  obtain ⟨rfl, rfl⟩ := terminal
  have failed := admitted_unusable_original_binding_stays_failed scheduler before after
    ⟨0, none, execution⟩ prior original joint legal moved finalTrace retained admitted owner entry
      recorded serial opening evidence declared fresh unusable message native call handled included
  exact counted_failed_cell_terminal_payoff execution finalTrace owner failed

end Vegas.Examples.CommitSeedBroadcast
