/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDirectedRepairOpeningInclusion
import Vegas.Pending.ReactiveBindingCountedInclusion

/-! # Actual complete pending inclusion through directed repair -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {memory : BindingMemory (runtime setup) leaks} {owner : Player}
  {original repaired : (application setup leaks).Execution}

namespace EventGraphRuntime.BindingMemory.Frame

/-- Every actual pending-message inclusion has a repaired frame in clean
one-packet traffic. Ready disclosures read successful original bindings;
all remaining memory, candidate, acceptance and rejection facts are derived
from actual signed inputs and the carried submission invariant. -/
theorem pending_inclusion
    (frame : Frame (runtime setup) leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (recorded : memory.RecordsSubmittedBindings (runtime setup) leaks owner original repaired)
    (clean : (runtime setup).CountClean leaks original)
    (signed : (runtime setup).SignedCommitments leaks original)
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
    (id : MessageId Player) :
    let app := application setup leaks
    Frame (runtime setup) leaks memory owner
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
              exact frame.counted_binding_inclusion onlyBindings recorded clean signed id event
                candidate evidence token found
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
                    exact frame.ready_opening_inclusion onlyBindings leftBinding rightBinding
                      event actor payload binding checks outputEq codeEq node ready value successful
                      id candidate raw evidence found
                  · have rightNotReady : ¬ repaired.application.config.cut.Ready event := by
                      rw [← State.publicView_eventReady, ← frame.publicView,
                        State.publicView_eventReady]
                      exact ready
                    have refused (state : EventGraphRuntime.State (graph setup))
                        (notReady : ¬ state.config.cut.Ready event) :
                        handle (runtime setup) state ⟨id, .opening event candidate raw⟩ = none := by
                      simp only [handle, dite_eq_right notReady]
                    exact frame.include_rejected id _ found
                      (by simpa only [reactiveApplication_handle,
                        WitnessedPacket.tokenValid_opening, ite_true] using
                          refused original.application ready)
                      (by simpa only [reactiveApplication_handle,
                        WitnessedPacket.tokenValid_opening, ite_true] using
                          refused repaired.application rightNotReady)

end EventGraphRuntime.BindingMemory.Frame

end Vegas
