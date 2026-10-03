/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceResolutionComplement
import Vegas.Pending.ReactiveBindingContinuation
import Vegas.Pending.ReactiveBindingFrameStep

/-! # Uncharged owner waiting before an actual pending decision settles

An actual recorded call excludes every further unclassified transmission while
its event remains ready. This uses the emitted token and sequential ready order,
not a promise that the original continuation follows the risk menu. Neither
clear risk nor timely inclusion is required while the event is still ready.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Before a recorded ready event settles, every original owner response
outside the real public-packet and duplicate classes is silence. The history
may follow an arbitrary RAW policy and the response need not be risk supported. -/
theorem sourceServiceRecorded_ready_unclassified_silent
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (execution : (application setup leaks).Execution) (who : Player)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (event : (graph setup).EventId)
    (ready : execution.application.config.cut.Ready event)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall who) event = true)
    (response : (application setup leaks).Action)
    (notPacket : ¬ auditableServiceResponse setup leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) response)
    (notRecorded : ¬ recordedServiceResponse setup leaks (execution.recall who) response) :
    response = ⟨none⟩ := by
  cases response with
  | mk transmission =>
      cases transmission with
      | none => rfl
      | some material =>
          obtain ⟨other, _, _, otherReady, _, unrecorded⟩ :=
            unclassifiedSubmission_ready execution who trace material notPacket notRecorded
          have same : other = event := ready_unique _ otherReady ready
          subst other
          rw [recorded] at unrecorded
          cases unrecorded

variable [Fintype Player]

/-- One actual original policy draw gives both exact owner-invocation marginals.
Before the recorded ready event settles, its unclassified support is common
silence with unchanged shadow; every other draw has a real charged-class exit.
Neither original risk-menu support nor completed pending memory is assumed. -/
theorem sourceServiceRecorded_ready_invoke_coupling
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, original⟩))
    (event : (graph setup).EventId)
    (ready : original.application.config.cut.Ready event)
    (recorded : (runtime setup).eventRecorded leaks (original.recall who) event = true)
    (players : Player → (application setup leaks).Policy)
    (reference : List (application setup leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall who).length) :
    let app := application setup leaks
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (bounds.riskMenu (runtime setup) leaks bound) who reference (players who)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.invoke players who original ∧
      coupling.map Prod.snd = strategy.resume who players (some who) repaired memory ∧
      ∀ next ∈ coupling.support,
        (∃ response ∈ (players who (original.recall who) (original.observe app who)).support,
          next.1 = original.respond app who response ∧
            (auditableServiceResponse setup leaks who (original.recall who)
                (original.observe app who) response ∨
              recordedServiceResponse setup leaks (original.recall who) response)) ∨
        (next.2.2.shadow = memory.shadow ∧
          next.2.2.Frame (runtime setup) leaks who next.1 next.2.1) := by
  classical
  let app := application setup leaks
  let menu := bounds.riskMenu (runtime setup) leaks bound
  let input := (repaired.recall who, repaired.observe app who)
  let law := players who (original.recall who) (original.observe app who)
  let changed (response : app.Action) :=
    BindingMemory.retainedResponse (runtime setup) leaks menu who memory input response
  let updated (response : app.Action) : BindingMemory (runtime setup) leaks :=
    ⟨(changed response).2, memory.responses ++
      [(memory.shadow.inputView (runtime setup) leaks input.2, response)]⟩
  let coupling := law.map fun response =>
    (original.respond app who response, repaired.respond app who (changed response).1,
      updated response)
  refine ⟨coupling, ?_, ?_, ?_⟩
  · simp only [coupling, PMF.map_comp]
    rfl
  · simp only [coupling, PMF.map_comp, ReactiveApplication.Implementation.resume, ite_true]
    change law.map _ =
      ((BindingMemory.retainedImplementation (runtime setup) leaks menu who reference
        (players who)).respond memory input).map _
    rw [BindingMemory.retainedImplementation_respond (runtime setup) leaks menu who reference
      (players who) memory input.1 input.2 started, frame.past, frame.observed, PMF.map_comp]
    dsimp only [updated, changed, input, law, Function.comp_def]
    rw [frame.observed]
  · intro next supported
    obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ supported
    by_cases packet : auditableServiceResponse setup leaks who (original.recall who)
        (original.observe app who) response
    · exact Or.inl ⟨response, chosen, rfl, Or.inl packet⟩
    by_cases duplicate : recordedServiceResponse setup leaks (original.recall who) response
    · exact Or.inl ⟨response, chosen, rfl, Or.inr duplicate⟩
    have silent := sourceServiceRecorded_ready_unclassified_silent original who trace
      event ready recorded response packet duplicate
    subst response
    have retained := bounds.canonicalActions_subset_risk (runtime setup) leaks bound who input.1
      input.2 (bounds.silence_canonical (runtime setup) leaks who input.1 input.2)
    have actual : changed ⟨none⟩ = (⟨none⟩, memory.shadow) := by
      simp only [changed, BindingMemory.retainedResponse, menu, MessageBounds.riskMenu,
        retained, ite_true]
      rfl
    have related := frame.transport_response (⟨none⟩ : app.Action) (by simp)
    right
    refine ⟨congrArg Prod.snd actual, ?_⟩
    simpa only [updated, actual, BindingMemory.record] using related

end Vegas
