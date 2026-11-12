module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketDirectedRepairOpeningInclusion
public import Vegas.Pending.ReactiveBindingCountedInclusion

@[expose] public section

/-! # Actual complete pending inclusion through directed repair -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {memory : BindingMemory timeouts leaks} {owner : Player}
  {original repaired : (application setup timeouts leaks).Execution}

namespace EventGraphRuntime.BindingMemory.Frame

/-- Every actual pending-message inclusion between clear boundaries has a
repaired frame in clean one-packet traffic. Ready disclosures read successful
original bindings; all remaining memory, candidate, acceptance and rejection facts are derived
from actual signed inputs and the carried submission invariant. -/
theorem pending_inclusion
    (frame : Frame timeouts leaks memory owner original repaired)
    (clear : original.application.config.defaulted = ∅)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (recorded : memory.RecordsSubmittedBindings timeouts leaks owner original repaired)
    (clean : (CountClean timeouts) leaks original)
    (signed : (SignedCommitments timeouts) leaks original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (successfulReady : ∀ (event : (graph setup).EventId) (actor : Player) (payload : L.Ty)
      (binding : EventGraph.FieldRef (graph setup).layout (.binding actor payload))
      (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
      (outputEq : (graph setup).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .resolve actor payload binding checks),
      nodeView (graph setup) event = .resolve actor payload binding checks outputEq codeEq →
      original.application.config.cut.Ready event →
      ∃ value, binding.get? original.application.config.store = some (.success value))
    (id : MessageId Player)
    (endpointClear :
      (original.includePending (application setup timeouts leaks) id).application.config.defaulted =
        ∅) :
    let app := application setup timeouts leaks
    Frame timeouts leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  cases found : original.network.lookup id with
  | none => exact frame.include_missing id found
  | some message =>
      have identified : message.id = id := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      cases message with
      | mk messageId packet =>
          dsimp only at identified
          subst messageId
          rcases packet with ⟨call, evidence, token⟩
          have member := input_of_lookup clean.1 signed.provenance id _ found
          obtain ⟨valid, correct, _⟩ := (countPermits_eq_true_iff _ _).mp (clean.2 _ member)
          cases call with
          | malformed raw => cases correct
          | commitment event candidate =>
              exact frame.counted_binding_inclusion clear onlyBindings recorded clean signed id
                endpointClear event candidate evidence token found
          | opening event candidate raw =>
              obtain ⟨tokenEvent, named, tokenEq⟩ := (WitnessedPacket.tokenValid_iff _).mp valid
              change some event = some tokenEvent at named
              cases Option.some.inj named
              change token = some ⟨event⟩ at tokenEq
              subst token
              cases node : nodeView (graph setup) event with
              | sample payload law outputEq codeEq =>
                  simp only [CountCallCorrect, node, and_false] at correct
              | bind actor payload outputEq codeEq =>
                  simp only [CountCallCorrect, node, and_false] at correct
              | resolve actor payload binding checks outputEq codeEq =>
                  by_cases ready : original.application.config.cut.Ready event
                  · obtain ⟨value, successful⟩ := successfulReady event actor payload binding checks
                      outputEq codeEq node ready
                    exact frame.ready_opening_inclusion clear onlyBindings
                      leftBinding rightBinding
                      event actor payload binding checks outputEq codeEq node ready value successful
                      id candidate raw evidence found endpointClear
                  · have rightNotReady : ¬ repaired.application.config.cut.Ready event := by
                      rw [← State.publicView_eventReady, ← frame.publicView,
                        State.publicView_eventReady]
                      exact ready
                    have refused (state : EventGraphRuntime.State (graph setup))
                        (notReady : ¬ state.config.cut.Ready event) :
                        handle timeouts state ⟨id, .opening event candidate raw⟩ = none := by
                      simp only [handle, dite_eq_right notReady, ite_self]
                    exact frame.include_rejected id _ found
                      (reactiveHandle_none (timeouts := timeouts) (leaks := leaks)
                        (refused original.application ready))
                      (reactiveHandle_none (timeouts := timeouts) (leaks := leaks)
                        (refused repaired.application rightNotReady))

end EventGraphRuntime.BindingMemory.Frame

end Vegas
