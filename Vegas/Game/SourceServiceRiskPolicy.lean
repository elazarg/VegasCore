/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRetainedPolicy
import Vegas.Game.SourceServiceRiskSlots

/-! # Prescribed policy admission at clear risk-menu histories

A clear owner has canonical slot resources even when other owners have used
expanded raw responses. Bounded record invariants then admit its protected
source decisions, together with every prescribed deferral.

These are local support statements for arbitrary turn timing. They do not
prescribe source policies at risky sites, identify source continuations after
misses, or assert sequential rationality or zero audit charge.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- At a clear legal risk-menu history, the actual record and the owner's
canonical slot admit every timely unsent source decision. -/
theorem sourceServiceCanonicalPolicy_risk_retained
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
        bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    (bound : (serviceGraph setup mode).EventId → Nat) (profile : BehavioralProfile setup.program)
    (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).protocol
        (serviceInitialLaw setup mode) horizon
      scheduler).Trace (some control))
    (clear : (serviceRuntime setup mode deadline).serviceRisk leaks bound who
        (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) = false)
    (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (timely : control.execution.application.publicView.WithinDeadline
        (serviceRuntime setup mode deadline) event)
    (unsent : (serviceRuntime setup mode deadline).eventRecorded leaks
        (control.execution.recall who) event = false)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (supported : response ∈ (serviceCanonicalPolicy setup mode deadline leaks profile who
      (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who)).support) :
    response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
        (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) := by
  have persistentClear :=
      ((serviceRuntime setup mode deadline).serviceRisk_clear_iff leaks bound who _ _).mp clear |>.1
  obtain ⟨counted, _, selected⟩ := riskCanonicalSlot_resources bounds bound capacity control trace
    who persistentClear event turn unsent
  have rawTrace := (bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).toRawTrace
      (serviceInitialLaw setup mode)
    horizon scheduler trace
  have facts := legalFacts setup leaks horizon scheduler control rawTrace
  have boundedTrace := (bounds.riskMenu_in_raw
      (serviceRuntime setup mode deadline) leaks bound).trace
    (serviceInitialLaw setup mode) horizon scheduler trace
  have values := bounds.candidateValues_raw_history (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode)
    horizon scheduler initialCovered boundedTrace
  rw [serviceInitialLaw_eq_inputs] at boundedTrace
  have handles := bounds.executionHandles_raw_history (serviceRuntime setup mode deadline) leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler boundedTrace
  exact sourceServiceCanonicalPolicy_retained_of_resources bounds covered profile who permitted
    control.execution facts.binding values handles.1 event turn timely unsent counted selected
    response supported

/-- A guarded source opportunity at a clear risk-menu history is silence or
an admitted canonical decision. Its protection gate implies the deadline gate. -/
theorem sourceServiceCanonicalOpportunity_risk_retained
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
        bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    (bound : (serviceGraph setup mode).EventId → Nat) (profile : BehavioralProfile setup.program)
    (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).protocol
        (serviceInitialLaw setup mode) horizon
      scheduler).Trace (some control))
    (clear : (serviceRuntime setup mode deadline).serviceRisk leaks bound who
        (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) = false)
    (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (supported : response ∈ (serviceCanonicalOpportunity setup mode deadline leaks bound profile who
      event (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who)).support) :
    response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
        (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) := by
  have silent : ∀ action ∈ ((serviceApplication setup mode deadline leaks).silentPolicy
      (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who)).support,
      action ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
          (control.execution.recall who)
        (control.execution.observe (serviceApplication setup mode deadline leaks) who) := by
    intro action chosen
    cases (PMF.mem_support_pure_iff _ _).mp chosen
    exact bounds.silence_canonical (serviceRuntime setup mode deadline) leaks who _ _
  unfold serviceCanonicalOpportunity at supported
  split at supported
  · exact silent response supported
  · rename_i unrecorded
    split at supported
    · rename_i fits
      rw [PMF.support_bind] at supported
      obtain ⟨decided, decisionSupported, member⟩ := Set.mem_iUnion₂.mp supported
      split at member
      · exact silent response member
      · have same : response = decided := (PMF.mem_support_pure_iff _ _).mp member
        rw [same]
        exact sourceServiceCanonicalPolicy_risk_retained bounds covered initialCovered capacity
          bound profile who permitted control trace clear event turn fits.withinDeadline
          (by simpa using unrecorded) decided decisionSupported
    · exact silent response supported

/-- Every prescribed deferral timing is locally admitted while this owner's
full risk flag is clear, regardless of other owners' legal raw branches. -/
theorem sourceServiceTurnPolicy_risk_retained
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
        bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
        (timing : TurnTiming setup turns mode)
    (profile : BehavioralProfile setup.program) (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).protocol
        (serviceInitialLaw setup mode) horizon
      scheduler).Trace (some control))
    (clear : (serviceRuntime setup mode deadline).serviceRisk leaks bound who
        (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) = false)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (supported : response ∈
        (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who
      (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who)).support) :
    response ∈ bounds.riskActions (serviceRuntime setup mode deadline) leaks bound who
        (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) := by
  rw [bounds.riskActions_of_clear (serviceRuntime setup mode deadline) leaks bound who _ _ clear]
  apply bounds.canonicalActions_subset_clear (serviceRuntime setup mode deadline) leaks who
  have silent : ∀ action ∈ ((serviceApplication setup mode deadline leaks).silentPolicy
      (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who)).support,
      action ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
          (control.execution.recall who)
        (control.execution.observe (serviceApplication setup mode deadline leaks) who) := by
    intro action chosen
    cases (PMF.mem_support_pure_iff _ _).mp chosen
    exact bounds.silence_canonical (serviceRuntime setup mode deadline) leaks who _ _
  unfold serviceTurnPolicy at supported
  split at supported
  · exact silent response supported
  · rename_i event turn
    split at supported
    · rw [ReactiveApplication.policyMixture_policy, PMF.support_bind] at supported
      obtain ⟨slot, _, member⟩ := Set.mem_iUnion₂.mp supported
      unfold serviceTurnFamily ReactiveApplication.turnScheduledPolicy at member
      dsimp only at member
      split at member
      · exact sourceServiceCanonicalOpportunity_risk_retained bounds covered initialCovered
          capacity bound profile who permitted control trace clear event turn response member
      · exact silent response member
    · exact silent response supported

end Vegas
