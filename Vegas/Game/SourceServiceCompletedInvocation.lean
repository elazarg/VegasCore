/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCompletedResponse
import Vegas.Game.SourceServiceUnclassifiedPendingCommands
import Vegas.Game.SourceServiceRiskSlots
import Interaction.ReactiveRawRoundTrace

/-! # One actual full-effective draw at a completed repair boundary

The original native full-effective policy is sampled once. The same draw
drives the retained implementation, with real RAW successors and local owner
slots. Every draw is either actually charged-classified, a completed frame
copy, or a typed default with its derived one-event pending exception. A risk
expansion copies unclassified full-effective responses without calling it
a charge; their actual unconditional owner slots persist. Foreign
policies are arbitrary physical policies; there is no global risk trace.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A full-effective native owner policy yields both exact invocation marginals
and the actual copy/default/charged partition. Its current admissibility is
derived from the ambient menu decoder, rather than future risk support. -/
theorem sourceService_completed_invoke_coupling
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (values : bounds.CoversBindingValues)
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (onlyBindings : memory.shadow.OwnBindings who)
    (past : memory.shadow.CompletedAt original.application.config)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, some who, original⟩))
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨rightRemaining, some who, repaired⟩))
    (rightAtTurn : OwnSubmissionsAtTurn setup leaks repaired who)
    (rightSlots : CanonicalSlotsUsed setup leaks repaired who)
    (owner : ((bounds.menu (runtime setup) leaks).information (initialLaw setup) horizon
      scheduler).BehavioralPolicy who)
    (foreign : Player → (application setup leaks).Policy)
    (reference : List (application setup leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall who).length) :
    let app := application setup leaks
    let effectiveMenu := bounds.menu (runtime setup) leaks
    let players := Function.update foreign who
      (app.decodePolicy (effectiveMenu.embedPolicy (initialLaw setup) horizon scheduler who owner))
    let menu := bounds.riskMenu (runtime setup) leaks bound
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks menu who reference
      (players who)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.invoke players who original ∧
      coupling.map Prod.snd = strategy.resume who players (some who) repaired memory ∧
      ∀ next ∈ coupling.support,
        ∃ response ∈ (players who (original.recall who) (original.observe app who)).support,
          let input := (repaired.recall who, repaired.observe app who)
          let selected := BindingMemory.retainedResponse (runtime setup) leaks menu who memory
            input response
          next.1 = original.respond app who response ∧
          next.2.1 = repaired.respond app who selected.1 ∧
          next.2.2 = ⟨selected.2, memory.responses ++
            [(memory.shadow.inputView (runtime setup) leaks input.2, response)]⟩ ∧
          Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
            (some ⟨leftRemaining, none, next.1⟩)) ∧
          Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
            (some ⟨rightRemaining, none, next.2.1⟩)) ∧
          ((runtime setup).persistentServiceRisk leaks bound who (next.2.1.recall who)
              (next.2.1.observe app who) = false →
            OwnSubmissionsAtTurn setup leaks next.2.1 who ∧
              CanonicalSlotsUsed setup leaks next.2.1 who) ∧
          ((auditableServiceResponse setup leaks who (original.recall who)
              (original.observe app who) response ∨
                recordedServiceResponse setup leaks (original.recall who) response) ∨
            (next.2.2.Frame (runtime setup) leaks who next.1 next.2.1 ∧
              next.2.2.shadow.OwnBindings who ∧
              OwnSubmissionsAtTurn setup leaks next.2.1 who ∧
              CanonicalSlotsUsed setup leaks next.2.1 who ∧
              (next.2.2.shadow.CompletedAt next.1.application.config ∨
                ∃ event,
                  unusableServiceBindingResponse setup leaks who input.1 input.2 response ∧
                  (runtime setup).submittedEvent? leaks response = some event ∧
                  next.2.2.shadow.CompletedExcept next.1.application.config event))) := by
  classical
  let app := application setup leaks
  let effectiveMenu := bounds.menu (runtime setup) leaks
  let players := Function.update foreign who
    (app.decodePolicy (effectiveMenu.embedPolicy (initialLaw setup) horizon scheduler who owner))
  let menu := bounds.riskMenu (runtime setup) leaks bound
  let strategy := BindingMemory.retainedImplementation (runtime setup) leaks menu who reference
    (players who)
  let input := (repaired.recall who, repaired.observe app who)
  let selected := fun response : app.Action => BindingMemory.retainedResponse (runtime setup)
    leaks menu who memory input response
  let remembered := fun response : app.Action =>
    (⟨(selected response).2, memory.responses ++
      [(memory.shadow.inputView (runtime setup) leaks input.2, response)]⟩ :
        BindingMemory (runtime setup) leaks)
  let law := players who (original.recall who) (original.observe app who)
  let result := fun response : app.Action =>
    (original.respond app who response, repaired.respond app who (selected response).1,
      remembered response)
  let coupling := law.map result
  have responds := BindingMemory.retainedImplementation_respond (runtime setup) leaks menu who
    reference (players who) memory (repaired.recall who) (repaired.observe app who) started
  rw [frame.past, frame.observed] at responds
  have reconstructed : memory.shadow.inputView (runtime setup) leaks (repaired.observe app who) =
      original.observe app who := frame.observed
  have sampled : strategy.respond memory input =
      law.map (fun response => ((selected response).1, remembered response)) := by
    simpa only [strategy, input, law, selected, remembered, reconstructed] using responds
  have effective (response : app.Action) (chosen : response ∈ law.support) :
      response ∈ effectiveMenu.actions who (original.recall who) (original.observe app who) := by
    change response ∈ (players who (original.recall who) (original.observe app who)).support
      at chosen
    rw [show players who = app.decodePolicy
      (effectiveMenu.embedPolicy (initialLaw setup) horizon scheduler who owner) from
        Function.update_self ..] at chosen
    exact effectiveMenu.decode_embedPolicy_covered (initialLaw setup) horizon scheduler who owner
      _ _ response chosen
  have selectedSupport (response : app.Action) (chosen : response ∈ law.support) :
      ((selected response).1, remembered response) ∈
        (strategy.respond memory input).support := by
    rw [sampled, PMF.support_map]
    exact ⟨response, chosen, rfl⟩
  refine ⟨coupling, ?_, ?_, ?_⟩
  · simp only [coupling, PMF.map_comp]
    rfl
  · change coupling.map Prod.snd =
      strategy.resume who players (some who) repaired memory
    simp only [ReactiveApplication.Implementation.resume, ite_true]
    change coupling.map Prod.snd = (strategy.respond memory input).map (fun pair =>
      (repaired.respond app who pair.1, pair.2))
    rw [sampled]
    simp only [coupling, PMF.map_comp]
    rfl
  · intro next reached
    obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ reached
    have admitted := BindingMemory.retainedImplementation_response_available (runtime setup)
      leaks menu who reference (players who) memory input
        ((selected response).1, remembered response) (selectedSupport response chosen)
    refine ⟨response, chosen, rfl, rfl, rfl,
      app.raw_trace_respond (initialLaw setup) horizon scheduler leftRemaining original who
        response leftTrace,
      app.raw_trace_respond (initialLaw setup) horizon scheduler rightRemaining repaired who
        (selected response).1 rightTrace, ?_, ?_⟩
    · intro persistent
      exact riskCanonicalSlots_respond bounds bound repaired who who (selected response).1
        rightTrace (fun _ => ⟨rightAtTurn, rightSlots⟩) (fun _ => admitted) persistent
    · by_cases packet : auditableServiceResponse setup leaks who (original.recall who)
          (original.observe app who) response
      · exact Or.inl (Or.inl packet)
      by_cases recorded : recordedServiceResponse setup leaks (original.recall who) response
      · exact Or.inl (Or.inr recorded)
      have available := effective response chosen
      by_cases clear : (runtime setup).serviceRisk leaks bound who (repaired.recall who)
          (repaired.observe app who) = false
      · have canonical := admitted
        change (selected response).1 ∈ bounds.riskActions (runtime setup) leaks bound who
          (repaired.recall who) (repaired.observe app who) at canonical
        rw [bounds.riskActions_of_clear (runtime setup) leaks bound who _ _ clear] at canonical
        have targetSlots :=
          And.intro (retainedOwnSubmissionsAtTurn_respond bounds repaired who
            (selected response).1 canonical rightAtTurn)
            (retainedCanonicalSlots_respond bounds rightTrace canonical rightAtTurn rightSlots)
        have split := sourceServiceUnclassified_response_selection bounds bound values original
          repaired who memory frame leftTrace rightTrace rightAtTurn rightSlots clear response
            available packet recorded
        rcases split with copied | defaulted
        · have resources := sourceServiceUnclassified_copied_response_frame bounds bound original
            repaired who memory frame onlyBindings past leftTrace rightTrace rightAtTurn
              rightSlots response available
              packet recorded copied.1
          exact Or.inr ⟨resources.2.1, resources.2.2.1, targetSlots.1, targetSlots.2,
            Or.inl resources.2.2.2.1⟩
        · have resources := sourceServiceMissing_unusable_default_frame bounds bound values original
            repaired who memory frame onlyBindings past leftTrace rightTrace rightAtTurn rightSlots
              clear response available defaulted.1
          obtain ⟨event, payload, outputEq, codeEq, node, turn, unrecorded, opening, responseEq,
            missing⟩ := defaulted.1
          have named : (runtime setup).submittedEvent? leaks response = some event := by
            rw [responseEq]
            rfl
          have unusable : unusableServiceBindingResponse setup leaks who input.1 input.2 response :=
            ⟨event, payload, outputEq, codeEq, node, turn, unrecorded, opening, responseEq, missing⟩
          have pending := sourceServiceMissing_unusable_default_completedExcept bounds bound values
            original repaired who memory frame past rightTrace rightAtTurn rightSlots clear response
              available unusable event named
          exact Or.inr ⟨resources.1, resources.2.1, targetSlots.1, targetSlots.2,
            Or.inr ⟨event, unusable, named, pending⟩⟩
      · have expanded : (runtime setup).serviceRisk leaks bound who (repaired.recall who)
            (repaired.observe app who) = true := Bool.eq_true_of_not_eq_false clear
        have physical := sourceServiceUnclassified_response_transport bounds original repaired
          who memory frame leftTrace rightTrace response available packet recorded
        have member : response ∈ bounds.riskActions (runtime setup) leaks bound who
            (repaired.recall who) (repaired.observe app who) := by
          rw [bounds.riskActions_of_risk (runtime setup) leaks bound who _ _ expanded]
          exact physical.1
        have resources := sourceServiceUnclassified_copied_response_frame bounds bound original
          repaired who memory frame onlyBindings past leftTrace rightTrace rightAtTurn rightSlots
            response available packet recorded member
        exact Or.inr ⟨resources.2.1, resources.2.2.1, resources.2.2.2.2.1,
          resources.2.2.2.2.2, Or.inl resources.2.2.2.1⟩

end Vegas
