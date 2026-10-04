/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRiskSlots
import Vegas.Pending.ReactiveBindingContinuation
import Interaction.ReactiveRawRoundTrace

/-! # Actual owner-local slots of the retained implementation

The focal implementation admits each sampled response by construction. Its
conditional slot invariant therefore follows the actual RAW continuation even
when foreign players use arbitrary physical policies. No global repaired risk
trace or future policy coverage callback is needed.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Actual resumption has a RAW successor trace and retains the focal owner's
conditional slot resources. Its own local admission follows from the selected
implementation result; every foreign response is unrestricted. -/
theorem sourceServiceRetained_resume_slots
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (execution : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks) (actor : Option Player)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, actor, execution⟩))
    (prior : (runtime setup).persistentServiceRisk leaks bound who (execution.recall who)
        (execution.observe (application setup leaks) who) = false →
      OwnSubmissionsAtTurn setup leaks execution who ∧ CanonicalSlotsUsed setup leaks execution who)
    (players : Player → (application setup leaks).Policy)
    (reference : List (application setup leaks).PlayerEntry)
    (next : (application setup leaks).Execution × BindingMemory (runtime setup) leaks)
    (supported : next ∈ ((BindingMemory.retainedImplementation (runtime setup) leaks
      (bounds.riskMenu (runtime setup) leaks bound) who reference (players who)).resume who players
        actor execution memory).support) :
    Nonempty (((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, next.1⟩)) ∧
      ((runtime setup).persistentServiceRisk leaks bound who (next.1.recall who)
          (next.1.observe (application setup leaks) who) = false →
        OwnSubmissionsAtTurn setup leaks next.1 who ∧
          CanonicalSlotsUsed setup leaks next.1 who) := by
  classical
  let app := application setup leaks
  let menu := bounds.riskMenu (runtime setup) leaks bound
  cases actor with
  | none =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ⟨⟨trace⟩, prior⟩
  | some responder =>
      by_cases own : responder = who
      · subst responder
        simp only [ReactiveApplication.Implementation.resume, ite_true, PMF.support_map]
          at supported
        obtain ⟨selected, selectedSupport, rfl⟩ := supported
        have member := BindingMemory.retainedImplementation_response_available (runtime setup) leaks
          menu who reference (players who) memory _ selected selectedSupport
        refine ⟨app.raw_trace_respond (initialLaw setup) horizon scheduler remaining execution who
          selected.1 trace, ?_⟩
        intro clear
        exact riskCanonicalSlots_respond bounds bound execution who who selected.1 trace prior
          (fun _ => member) clear
      · simp only [ReactiveApplication.Implementation.resume, own, ite_false, PMF.support_map]
          at supported
        obtain ⟨responded, selected, rfl⟩ := supported
        obtain ⟨response, _chosen, rfl⟩ := PMF.support_map .. ▸ selected
        refine ⟨app.raw_trace_respond (initialLaw setup) horizon scheduler remaining execution
          responder response trace, ?_⟩
        intro clear
        exact riskCanonicalSlots_respond bounds bound execution who responder response trace prior
          (fun same => (own same).elim) clear

/-- The real retained round accounts for its scheduler command and selected
response. Arbitrary foreign responses preserve the focal conditional slots. -/
theorem sourceServiceRetained_round_slots
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (execution : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (prior : (runtime setup).persistentServiceRisk leaks bound who (execution.recall who)
        (execution.observe (application setup leaks) who) = false →
      OwnSubmissionsAtTurn setup leaks execution who ∧ CanonicalSlotsUsed setup leaks execution who)
    (players : Player → (application setup leaks).Policy)
    (reference : List (application setup leaks).PlayerEntry)
    (next : (application setup leaks).Execution × BindingMemory (runtime setup) leaks)
    (supported : next ∈ ((BindingMemory.retainedImplementation (runtime setup) leaks
      (bounds.riskMenu (runtime setup) leaks bound) who reference (players who)).round who players
        scheduler execution memory).support) :
    Nonempty (((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, next.1⟩)) ∧
      ((runtime setup).persistentServiceRisk leaks bound who (next.1.recall who)
          (next.1.observe (application setup leaks) who) = false →
        OwnSubmissionsAtTurn setup leaks next.1 who ∧
          CanonicalSlotsUsed setup leaks next.1 who) := by
  let app := application setup leaks
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler remaining
    execution middle command trace selected moved
  exact sourceServiceRetained_resume_slots bounds bound middle who memory (command.actor? app)
    middleTrace (fun clear => riskCanonicalSlots_environment bound execution middle who command
      prior clear moved) players reference next resumed

/-- Every actual supported retained continuation has a RAW trace and the
focal conditional slots. This tracks resources of the existing joint evaluator
and does not restrict foreign policies or choose a new continuation law. -/
theorem sourceServiceRetained_runJoint_slots
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (count : Nat) (execution : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + count, none, execution⟩))
    (prior : (runtime setup).persistentServiceRisk leaks bound who (execution.recall who)
        (execution.observe (application setup leaks) who) = false →
      OwnSubmissionsAtTurn setup leaks execution who ∧ CanonicalSlotsUsed setup leaks execution who)
    (players : Player → (application setup leaks).Policy)
    (reference : List (application setup leaks).PlayerEntry)
    (next : (application setup leaks).Execution × BindingMemory (runtime setup) leaks)
    (supported : next ∈ ((BindingMemory.retainedImplementation (runtime setup) leaks
      (bounds.riskMenu (runtime setup) leaks bound) who reference (players who)).runJoint who
        players scheduler count execution memory).support) :
    Nonempty (((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, next.1⟩)) ∧
      ((runtime setup).persistentServiceRisk leaks bound who (next.1.recall who)
          (next.1.observe (application setup leaks) who) = false →
        OwnSubmissionsAtTurn setup leaks next.1 who ∧
          CanonicalSlotsUsed setup leaks next.1 who) := by
  induction count generalizing execution memory with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ⟨⟨trace⟩, prior⟩
  | succ count ih =>
      obtain ⟨middle, stepped, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      obtain ⟨⟨middleTrace⟩, middleSlots⟩ := sourceServiceRetained_round_slots bounds bound
        execution who memory trace prior players reference middle stepped
      exact ih middle.1 middle.2 middleTrace middleSlots continued

end Vegas
