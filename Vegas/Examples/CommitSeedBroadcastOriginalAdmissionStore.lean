/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalAdmissionClear
import Vegas.Pending.PhaseClearSemanticProgress
import Vegas.Pending.PhaseSeedBudget
import Interaction.ReactiveInvariantPrefix

/-! # Original native cells retained by jointly admitted bindings -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- All three original admissions rule out rollback of any native cell already
written at an actual original prefix. Later publication exclusions are allowed. -/
theorem all_original_admissions_keep_store
    (selected : app.Scheduler) (before final : app.Control)
    (prior : (countedMenu.protocol initial horizon selected).Trace (some before))
    (position : before.execution.application.attempt = originalAttempt ∨
      before.execution.application.phases <:+ [publicationPhase])
    (finalTrace : (countedMenu.protocol initial horizon selected).Trace (some final))
    (retained : TracePrefix prior finalTrace)
    (admitted : ∀ owner, PhaseService.BindingAccepted runtime leaks
      (originalCoordinate owner) owner final.execution) :
    KeepsStore before.execution.application.current.native
      final.execution.application.current.native := by
  classical
  have along : ∀ {target}
      (targetTrace : (countedMenu.protocol initial horizon selected).Trace target),
      TracePrefix prior targetTrace → TracePrefix targetTrace finalTrace →
      ∃ next : app.Control, target = some next ∧
        (next.execution.application.attempt = originalAttempt ∨
          next.execution.application.phases <:+ [publicationPhase]) ∧
        KeepsStore before.execution.application.current.native
          next.execution.application.current.native := by
    intro target targetTrace kept
    induction kept with
    | refl =>
      intro _later
      exact ⟨before, rfl, position, fun _ _ stored => stored⟩
    | @extend source target earlier kept joint legal reached ih =>
      intro later
      obtain ⟨middle, rfl, position, stored⟩ :=
        ih ((TracePrefix.extend .refl joint legal reached).trans later)
      obtain ⟨next, rfl, _recall⟩ := app.transition_recall_prefix initial horizon selected
        middle target joint reached
      rcases position with atOriginal | publications
      · have clear := original_transition_clear_of_all_final_receipts selected middle next final
          earlier atOriginal joint legal reached finalTrace later admitted
        have preserved := (phaseApplication_clear_semantic_extension runtime leaks).transition
          initial horizon selected middle next joint reached clear
        have nextPosition : next.execution.application.attempt = originalAttempt ∨
            next.execution.application.phases <:+ [publicationPhase] := by
          have rawNext := countedMenu.toRawTrace initial horizon selected
            (earlier.extend joint legal reached)
          rcases raw_phases_cases selected next rawNext with phases | phases | phases
          · have budget := (phaseApplication_seedBudget runtime leaks).history initial horizon
              selected (by
                intro state supported
                rw [initial, PMF.mem_support_pure_iff] at supported
                subst state
                exact PhaseRuntimeState.initial_seedBudget plan _) rawNext
            have generation : next.execution.application.generation = 0 := by
              have bound := budget.current_generation
              rw [clear, Finset.card_empty] at bound
              omega
            left
            change ⟨(next.execution.application.phases.head?.map RuntimePhase.low).getD
              graph.order.eventCount, next.execution.application.generation⟩ = originalAttempt
            rw [phases, generation]
            rfl
          · exact Or.inr (by rw [phases])
          · exact Or.inr (by rw [phases]; exact List.nil_suffix)
        exact ⟨next, rfl, nextPosition,
          fun field value member => preserved field value (stored field value member)⟩
      · have extension :=  (publication_tail_store_invariant
          before.execution.application.current.native).tracePrefix countedMenu initial horizon
            selected middle next earlier (earlier.extend joint legal reached)
              (TracePrefix.extend .refl joint legal reached) ⟨publications, stored⟩
        exact ⟨next, rfl, Or.inr extension.1, extension.2⟩
  obtain ⟨next, equality, _position, stored⟩ := along finalTrace retained .refl
  cases Option.some.inj equality
  exact stored

/-- A genuine admitted original packet's entire native result is retained
when all original bindings are admitted. Publication failures may follow. -/
theorem all_original_admissions_keep_included_store
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
    (message : Message Player (CommitAttemptPacket graph)) (native : EventGraphRuntime.State graph)
    (handled : handle runtime before.execution.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native)
    (included : before.execution.application.handle runtime message =
      some after.execution.application) :
    KeepsStore native final.execution.application.current.native := by
  have clear := original_transition_clear_of_all_final_receipts selected before after final prior
    original joint legal moved finalTrace retained admitted
  have normalization := phase_handle_keeps_result_of_clear runtime before.execution.application
    after.execution.application message native handled included clear
  let afterTrace := prior.extend joint legal moved
  have rawAfter := countedMenu.toRawTrace initial horizon selected afterTrace
  have position : after.execution.application.attempt = originalAttempt ∨
      after.execution.application.phases <:+ [publicationPhase] := by
    rcases raw_phases_cases selected after rawAfter with phases | phases | phases
    · have budget := (phaseApplication_seedBudget runtime leaks).history initial horizon selected
        (by
          intro state supported
          rw [initial, PMF.mem_support_pure_iff] at supported
          subst state
          exact PhaseRuntimeState.initial_seedBudget plan _) rawAfter
      have generation : after.execution.application.generation = 0 := by
        have bound := budget.current_generation
        rw [clear, Finset.card_empty] at bound
        omega
      left
      change ⟨(after.execution.application.phases.head?.map RuntimePhase.low).getD
        graph.order.eventCount, after.execution.application.generation⟩ = originalAttempt
      rw [phases, generation]
      rfl
    · exact Or.inr (by rw [phases])
    · exact Or.inr (by rw [phases]; exact List.nil_suffix)
  have future := all_original_admissions_keep_store selected after final afterTrace position
    finalTrace retained admitted
  exact fun field value stored => future field value (normalization field value stored)

end Vegas.Examples.CommitSeedBroadcast
