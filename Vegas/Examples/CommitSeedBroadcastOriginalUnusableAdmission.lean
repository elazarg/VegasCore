/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalAdmissionFailure
import Vegas.Examples.CommitSeedBroadcastOriginalAdmissionTrace
import Vegas.Pending.PhaseCountUniqueness
import Vegas.Pending.PhaseBindingFreshness

/-! # Joint original admission fixes the payoff of unusable original material -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem failed_binding_meaning_before_prefix (selected : app.Scheduler)
    (before final : app.Control)
    (prior : (countedMenu.protocol initial horizon selected).Trace (some before))
    (finalTrace : (countedMenu.protocol initial horizon selected).Trace (some final))
    (kept : TracePrefix prior finalTrace) (candidate : Handle graph)
    (failed : final.execution.application.current.native.bindingResult candidate .bool = .failure) :
    before.execution.application.current.native.bindingResult candidate .bool = .failure := by
  by_cases fresh : before.execution.application.current.native.candidates.lookup candidate = .fresh
  · simp only [EventGraphRuntime.State.bindingResult, fresh]
  · let result := before.execution.application.current.native.bindingResult candidate .bool
    have invariant : app.Invariant (fun state =>
        state.current.native.candidates.lookup candidate ≠ .fresh ∧
          state.current.native.bindingResult candidate .bool = result) := by
      let stable := phaseApplication_preservesFixedCandidates runtime leaks
      constructor
      · intro state owner material valid
        have fixed := stable.submit state owner material candidate valid.1
        exact ⟨by simpa only [fixed] using valid.1,
          by simpa only [State.bindingResult, fixed] using valid.2⟩
      · intro state message next valid handled
        have fixed := stable.handle state message next handled candidate valid.1
        exact ⟨by simpa only [fixed] using valid.1,
          by simpa only [State.bindingResult, fixed] using valid.2⟩
      · intro state command next valid reached
        have fixed := stable.environment state command next reached candidate valid.1
        exact ⟨by simpa only [fixed] using valid.1,
          by simpa only [State.bindingResult, fixed] using valid.2⟩
    have same := (invariant.tracePrefix countedMenu initial horizon selected before final prior
      finalTrace kept ⟨fresh, rfl⟩).2
    exact same.symm.trans failed

/-- Count permission identifies the admitted original envelope with the actual
unusable declaration. Its receipt, clean close and retained failure are derived. -/
theorem all_original_admissions_unusable_record_failed
    (seeds : Seeds) (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨0, none, execution⟩))
    (admitted : ∀ owner, PhaseService.BindingAccepted runtime leaks
      (originalCoordinate owner) owner execution)
    (owner : Player) (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall owner)
    (entryOriginal : entry.beforeView.application.2.attempt = originalAttempt)
    (serial : Nat) (opening : Option (Raw simpleExpr)) (evidence : EvidenceRequest graph)
    (declared : entry.action =
      ⟨some ⟨⟨.commitment (bindingEvent owner) (owner, .prepared serial), opening⟩, evidence⟩⟩)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (unusable : (opening.bind fun raw => raw.as? .bool) = none) :
    execution.application.current.native.config.outputs (bindingEvent owner) = some
      (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.failure : PublicationResult Bool)) := by
  classical
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  have meaning := recorded_unusable_binding_result (family seeds) ⟨0, none, execution⟩ trace
    owner entry recorded (bindingEvent owner) serial opening evidence declared fresh unusable
  obtain ⟨authored, emitted, author, call⟩ := PhaseCount.recalled_submission_emitted runtime leaks
    initial horizon (family seeds) raw owner entry recorded
      ⟨⟨.commitment (bindingEvent owner) (owner, .prepared serial), opening⟩, evidence⟩
        (by rw [declared])
  have tag := phase_recalled_emission_attempt runtime leaks initial horizon (family seeds) raw
    owner entry recorded authored emitted
  have authoredAttempt : authored.payload.attempt = originalAttempt := tag.trans entryOriginal
  have authoredInput : authored ∈ execution.network.inputs := by
    have output : authored ∈ app.outputs (execution.recall owner) :=
      List.mem_filterMap.mpr ⟨entry, recorded, emitted⟩
    rw [← app.history_inputRecall initial horizon (family seeds) raw owner] at output
    exact (List.mem_filter.mp output).1
  obtain ⟨before, after, prior, message, phaseNative, original, input, sender, attempt, event,
    included, afterState, joint, legal, moved, finalTrace, kept⟩ :=
    original_terminal_receipt_counted_prefix seeds execution trace owner (admitted owner)
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds (family seeds)).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have same : message = authored := PhaseCount.Permits.eq_of_same_event
    ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input))
    ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 authored authoredInput))
    input authoredInput (fun first firstInput second secondInput named =>
      app.input_identifier_injective_history initial horizon (family seeds)
        ⟨0, none, execution⟩ raw first second firstInput secondInput named)
    (sender.trans author.symm) (by
      unfold PhaseCount.event?
      rw [event, call, attempt, authoredAttempt]
      rfl)
  have selectedCall : message.payload.packet.call =
      .commitment (bindingEvent owner) (owner, .prepared serial) := by rw [same]; exact call
  have beforeMeaning := failed_binding_meaning_before_prefix (family seeds) before
    ⟨0, none, execution⟩ prior finalTrace
      ((TracePrefix.extend .refl joint legal moved).trans kept)
        (owner, .prepared serial) meaning
  have actual := included
  unfold PhaseRuntimeState.handle at actual
  split at actual
  · obtain ⟨native, handled, _normalized⟩ := Option.map_eq_some_iff.mp actual
    have rawHandled : handle runtime before.execution.application.current.native
        ⟨message.id, .commitment (bindingEvent owner) (owner, .prepared serial)⟩ = some native := by
      simpa only [selectedCall] using handled
    have codeEq : cast (congrArg (EventCode graph.layout) (bindingEvent_layout owner))
        (graph.nodes (bindingEvent owner)) =
          EventCode.bind (L := simpleExpr) (layout := graph.layout) owner BaseTy.bool := by
      fin_cases owner <;> rfl
    have node : nodeView graph (bindingEvent owner) =
        .bind owner .bool (bindingEvent_layout owner) codeEq := by
      fin_cases owner <;> rfl
    obtain ⟨_ready, configEq⟩ := runtime.handle_commitment_config_result
      before.execution.application.current.native native message.id (bindingEvent owner)
        (owner, .prepared serial) owner .bool (bindingEvent_layout owner) codeEq node rawHandled
    have failed : native.config.outputs (bindingEvent owner) = some
        (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
          (PublicationResult.failure : PublicationResult Bool)) := by
      rw [configEq, Config.complete_output_same, beforeMeaning]
    have accepted : before.execution.application.handle runtime message =
        some after.execution.application := by rw [afterState]; exact included
    exact all_original_admissions_keep_included_store (family seeds) before after
      ⟨0, none, execution⟩ prior original joint legal moved finalTrace kept admitted message native
        handled accepted (.inr (bindingEvent owner)) _ failed
  · cases actual

/-- The fixed terminal loss follows from the recorded unusable original
material and all actual final original receipts, without an inclusion premise. -/
theorem all_original_admissions_unusable_record_payoff
    (execution : app.Execution) (trace : countedProtocol.Trace (some ⟨0, none, execution⟩))
    (admitted : ∀ owner, PhaseService.BindingAccepted runtime leaks
      (originalCoordinate owner) owner execution)
    (owner : Player) (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall owner)
    (entryOriginal : entry.beforeView.application.2.attempt = originalAttempt)
    (serial : Nat) (opening : Option (Raw simpleExpr)) (evidence : EvidenceRequest graph)
    (declared : entry.action =
      ⟨some ⟨⟨.commitment (bindingEvent owner) (owner, .prepared serial), opening⟩, evidence⟩⟩)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (unusable : (opening.bind fun raw => raw.as? .bool) = none) :
    netPayoff (app.finished execution) owner = -(3 / 2) := by
  obtain ⟨seeds, ⟨fixed⟩⟩ := menu_trace_fixed_seed countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) ⟨0, none, execution⟩ trace
  have failed := all_original_admissions_unusable_record_failed seeds execution fixed admitted
    owner entry recorded entryOriginal serial opening evidence declared fresh unusable
  exact counted_failed_cell_terminal_payoff execution trace owner failed

end Vegas.Examples.CommitSeedBroadcast
