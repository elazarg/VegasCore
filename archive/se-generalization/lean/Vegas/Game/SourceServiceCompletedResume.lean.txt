/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCompletedInvocation
import Vegas.Pending.ReactiveBindingCommitmentProvenance
import Vegas.Pending.ReactiveBindingForeignWindow
import Interaction.ReactiveRawRoundTrace

/-! # Actual owner and foreign resumption at a completed repair boundary

The full-effective owner draw and arbitrary raw foreign draws use the same
physical and private implementation laws. A copied response keeps the actual
commitment ledger and unconditional counted slots. A typed default exposes
its real clear input and response identity for the pending-segment consumer.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Real inactive and foreign constructor transitions compose with the actual
owner invocation. Every marginal remains a RAW history; the pending alternative
names the actual sampled response, rather than promising future support. -/
theorem sourceService_completed_resume_coupling
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (values : bounds.CoversBindingValues)
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (onlyBindings : memory.shadow.OwnBindings who)
    (past : memory.shadow.CompletedAt original.application.config)
    (ledger : OwnerCommitmentsInertOrMatching who original repaired)
    (actor : Option Player)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, actor, original⟩))
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨rightRemaining, actor, repaired⟩))
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
      coupling.map Prod.fst = app.resume players actor original ∧
      coupling.map Prod.snd = strategy.resume who players actor repaired memory ∧
      ∀ next ∈ coupling.support,
        Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
          (some ⟨leftRemaining, none, next.1⟩)) ∧
        Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
          (some ⟨rightRemaining, none, next.2.1⟩)) ∧
        ((actor = some who ∧
          ∃ response ∈ (players who (original.recall who) (original.observe app who)).support,
            next.1 = original.respond app who response ∧
            (auditableServiceResponse setup leaks who (original.recall who)
              (original.observe app who) response ∨
              recordedServiceResponse setup leaks (original.recall who) response)) ∨
          (next.2.2.Frame (runtime setup) leaks who next.1 next.2.1 ∧
            next.2.2.shadow.OwnBindings who ∧
            OwnSubmissionsAtTurn setup leaks next.2.1 who ∧
            CanonicalSlotsUsed setup leaks next.2.1 who ∧
            ((next.2.2.shadow.CompletedAt next.1.application.config ∧
              OwnerCommitmentsInertOrMatching who next.1 next.2.1) ∨
              (actor = some who ∧
                ∃ response ∈ (players who (original.recall who) (original.observe app who)).support,
                  response ∈ effectiveMenu.actions who (original.recall who)
                    (original.observe app who) ∧
                  let input := (repaired.recall who, repaired.observe app who)
                  let selected := BindingMemory.retainedResponse (runtime setup) leaks menu who
                    memory input response
                  next.1 = original.respond app who response ∧
                  next.2.1 = repaired.respond app who selected.1 ∧
                  next.2.2 = ⟨selected.2, memory.responses ++
                    [(memory.shadow.inputView (runtime setup) leaks input.2, response)]⟩ ∧
                  ∃ event, (runtime setup).serviceRisk leaks bound who input.1 input.2 = false ∧
                    unusableServiceBindingResponse setup leaks who input.1 input.2 response ∧
                    (runtime setup).submittedEvent? leaks response = some event ∧
                    next.2.2.shadow.CompletedExcept next.1.application.config event)))) := by
  classical
  let app := application setup leaks
  let effectiveMenu := bounds.menu (runtime setup) leaks
  let players := Function.update foreign who
    (app.decodePolicy (effectiveMenu.embedPolicy (initialLaw setup) horizon scheduler who owner))
  let menu := bounds.riskMenu (runtime setup) leaks bound
  let strategy := BindingMemory.retainedImplementation (runtime setup) leaks menu who reference
    (players who)
  cases actor with
  | none =>
      refine ⟨PMF.pure (original, repaired, memory), PMF.pure_map .., PMF.pure_map .., ?_⟩
      intro next supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ⟨⟨leftTrace⟩, ⟨rightTrace⟩,
        Or.inr ⟨frame, onlyBindings, rightAtTurn, rightSlots, Or.inl ⟨past, ledger⟩⟩⟩
  | some actor =>
      by_cases own : actor = who
      · subst actor
        obtain ⟨coupling, first, second, supported⟩ := sourceService_completed_invoke_coupling
          bounds bound values original repaired who memory frame onlyBindings past ledger leftTrace
            rightTrace rightAtTurn rightSlots owner foreign reference started
        refine ⟨coupling, first, second, ?_⟩
        intro next member
        obtain ⟨response, chosen, actualLeft, actualRight, actualMemory, nextLeftTrace,
          nextRightTrace, _conditional, classified⟩ := supported next member
        refine ⟨nextLeftTrace, nextRightTrace, ?_⟩
        rcases classified with charged | good
        · exact Or.inl ⟨rfl, response, chosen, actualLeft, charged⟩
        · obtain ⟨afterFrame, afterOwn, afterAtTurn, afterSlots, completed | pending⟩ := good
          · exact Or.inr ⟨afterFrame, afterOwn, afterAtTurn, afterSlots, Or.inl completed⟩
          · right
            refine ⟨afterFrame, afterOwn, afterAtTurn, afterSlots, Or.inr ?_⟩
            have available : response ∈ effectiveMenu.actions who (original.recall who)
                (original.observe app who) := by
              change response ∈ (players who (original.recall who)
                (original.observe app who)).support at chosen
              rw [show players who = app.decodePolicy (effectiveMenu.embedPolicy (initialLaw setup)
                horizon scheduler who owner) from Function.update_self ..] at chosen
              exact effectiveMenu.decode_embedPolicy_covered (initialLaw setup) horizon scheduler
                who owner _ _ response chosen
            exact ⟨rfl, response, chosen, available, actualLeft, actualRight, actualMemory, pending⟩
      · obtain ⟨coupling, first, second, related⟩ := frame.foreign_invoke_coupling players actor own
        let augmented := coupling.map fun pair => (pair.1, pair.2, memory)
        refine ⟨augmented, ?_, ?_, ?_⟩
        · simp only [augmented, PMF.map_comp]
          exact first
        · simp only [augmented, PMF.map_comp, ReactiveApplication.Implementation.resume,
            own, ↓reduceIte]
          simpa only [PMF.map_comp, Function.comp_def] using
            congrArg (PMF.map (fun execution => (execution, memory))) second
        · intro next member
          obtain ⟨pair, chosen, rfl⟩ := PMF.support_map .. ▸ member
          have leftChosen : pair.1 ∈ (app.invoke players actor original).support := by
            rw [← first, PMF.support_map]
            exact ⟨pair, chosen, rfl⟩
          have rightChosen : pair.2 ∈ (app.invoke players actor repaired).support := by
            rw [← second, PMF.support_map]
            exact ⟨pair, chosen, rfl⟩
          obtain ⟨leftResponse, _leftSelected, leftActual⟩ := PMF.support_map .. ▸ leftChosen
          obtain ⟨rightResponse, _rightSelected, rightActual⟩ := PMF.support_map .. ▸ rightChosen
          have leftFacts := legalFacts setup leaks horizon scheduler _ leftTrace
          have afterLedger := ledger.respond_noncommitment leftFacts.binding actor leftResponse
            rightResponse (fun same => False.elim (own same))
          have afterPast : memory.shadow.CompletedAt pair.1.application.config := by
            rw [← leftActual,
              (runtime setup).reactive_respond_application leaks original actor leftResponse |>.1]
            exact past
          have afterAtTurn : OwnSubmissionsAtTurn setup leaks pair.2 who := by
            rw [← rightActual]
            unfold OwnSubmissionsAtTurn
            rwa [app.respond_recall_other repaired actor who (Ne.symm own) rightResponse]
          have afterSlots := canonicalSlotsUsed_respond_other repaired (Ne.symm own) rightResponse
            rightSlots
          refine ⟨?_, ?_, Or.inr ⟨related pair chosen, onlyBindings, afterAtTurn, ?_,
            Or.inl ⟨afterPast, ?_⟩⟩⟩
          · rw [← leftActual]
            exact app.raw_trace_respond (initialLaw setup) horizon scheduler leftRemaining original
              actor leftResponse leftTrace
          · change Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
              (some ⟨rightRemaining, none, pair.2⟩))
            rw [← rightActual]
            exact app.raw_trace_respond (initialLaw setup) horizon scheduler rightRemaining repaired
              actor rightResponse rightTrace
          · rwa [rightActual] at afterSlots
          · rwa [leftActual, rightActual] at afterLedger

end Vegas
