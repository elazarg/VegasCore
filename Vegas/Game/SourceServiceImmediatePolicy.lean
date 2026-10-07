/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRiskPolicy
import Vegas.Game.SourceServiceFirstTurnBinding

/-! # Immediate source decisions from actual clear recall

At a clear service-risk view, the owner takes the current canonical opportunity
immediately, regardless of earlier silent turns. Its actual submission recall
still suppresses repeated calls, and the opportunity still gates transmission
on protected inclusion. Without an own turn, or when risk is present, the policy
is silent.

The local results admit the policy at legal risk-menu histories and derive its
actual first binding call, fresh conformance and slot preservation. They neither
reset private recall nor prescribe a rational continuation at risky sites.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Configured

variable (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- Take the protected current source opportunity whenever the owner's actual
local risk flag is clear, without testing an earlier turn count. -/
def serviceImmediatePolicy (bound : (serviceGraph setup mode).EventId → Nat)
    (profile : BehavioralProfile setup.program) (who : Player) :
    (serviceApplication setup mode deadline leaks).Policy := fun past view =>
  if (serviceRuntime setup mode deadline).serviceRisk leaks bound who past view = false then
    match view.application.publicView.ownTurn? who with
    | none => (serviceApplication setup mode deadline leaks).silentPolicy past view
    | some event =>
        serviceCanonicalOpportunity setup mode deadline leaks bound profile who event past view
  else (serviceApplication setup mode deadline leaks).silentPolicy past view

end Configured

section Sequential

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The immediate policy on the default runtime. -/
abbrev sourceServiceImmediatePolicy : ((graph setup).EventId → Nat) →
    BehavioralProfile setup.program → Player → (application setup leaks).Policy :=
  serviceImmediatePolicy setup .sequential (rankDeadline setup .sequential) leaks

end Sequential

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}


/-- At a clear own turn, the immediate policy is the current canonical
opportunity even if earlier silent responses already saw that event. -/
theorem sourceServiceImmediatePolicy_at_event
    {bound : (serviceGraph setup mode).EventId → Nat} {profile : BehavioralProfile setup.program}
    {who : Player} {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView} {event :
        (serviceGraph setup mode).EventId}
    (clear : (serviceRuntime setup mode deadline).serviceRisk leaks bound who past view = false)
    (turn : view.application.publicView.ownTurn? who = some event) :
    serviceImmediatePolicy setup mode deadline leaks bound profile who past view =
      serviceCanonicalOpportunity setup mode deadline leaks bound profile who event past view := by
  simp only [serviceImmediatePolicy, clear, ↓reduceIte, turn]

/-- Every supported response is silence or a current opportunity at clear risk. -/
theorem sourceServiceImmediatePolicy_cases
    {bound : (serviceGraph setup mode).EventId → Nat} {profile : BehavioralProfile setup.program}
    {who : Player} {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView} {response :
        (serviceApplication setup mode deadline leaks).Action}
    (chosen : response ∈ (serviceImmediatePolicy setup mode deadline leaks bound profile who
      past view).support) :
    response = ⟨none⟩ ∨ ∃ event,
      (serviceRuntime setup mode deadline).serviceRisk leaks bound who past view = false ∧
      view.application.publicView.ownTurn? who = some event ∧
      response ∈ (serviceCanonicalOpportunity setup mode deadline leaks bound profile who event
        past view).support := by
  unfold serviceImmediatePolicy at chosen
  split at chosen
  · rename_i clear
    split at chosen
    · exact Or.inl
        ((serviceApplication setup mode deadline leaks).silentPolicy_cases past view response
            chosen)
    · rename_i event turn
      exact Or.inr ⟨event, clear, turn, chosen⟩
  · exact Or.inl
      ((serviceApplication setup mode deadline leaks).silentPolicy_cases past view response chosen)

/-- Every actual immediate submission is an unsent protected canonical source
decision at the current own turn. -/
theorem sourceServiceImmediatePolicy_submission
    {bound : (serviceGraph setup mode).EventId → Nat} {profile : BehavioralProfile setup.program}
    {who : Player} {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView} {response :
        (serviceApplication setup mode deadline leaks).Action}
    (chosen : response ∈ (serviceImmediatePolicy setup mode deadline leaks bound profile who
      past view).support)
    {material : (serviceApplication setup mode deadline leaks).Submission}
    (submits : response.transmission = some material) :
    ∃ event action, view.application.publicView.ownTurn? who = some event ∧
      (serviceRuntime setup mode deadline).eventRecorded leaks past event = false ∧
      view.application.publicView.InclusionFitsDeadline
          (serviceRuntime setup mode deadline) bound event ∧
      response =
          (serviceRuntime setup mode deadline).canonicalServiceDecision leaks who past view event
              action := by
  rcases sourceServiceImmediatePolicy_cases chosen with silent | ⟨event, _, turn, member⟩
  · rw [silent] at submits
    cases submits
  · obtain ⟨unrecorded, fits, other, action, otherTurn, decision⟩ :=
      sourceServiceCanonicalOpportunity_submission member submits
    have same : other = event := Option.some.inj (otherTurn.symm.trans turn)
    subst same
    exact ⟨other, action, turn, unrecorded, fits, decision⟩

/-- An immediate response names only the current own event. -/
theorem sourceServiceImmediatePolicy_submitsAtTurn
    (bound : (serviceGraph setup mode).EventId → Nat) (profile : BehavioralProfile setup.program)
    (who : Player) :
    SubmitsAtTurn setup leaks (serviceImmediatePolicy setup mode deadline leaks bound profile who)
      who := by
  intro past view response chosen event named
  rcases sourceServiceImmediatePolicy_cases chosen with silent | ⟨other, _, _, member⟩
  · rw [silent] at named
    cases named
  · exact sourceServiceCanonicalOpportunity_submitsAtTurn setup leaks bound profile who other
      past view response member event named

/-- Every supported immediate response satisfies the first-submission discipline. -/
theorem sourceServiceImmediatePolicy_firstSubmission
    {bound : (serviceGraph setup mode).EventId → Nat} {profile : BehavioralProfile setup.program}
    {who : Player} {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView} {response :
        (serviceApplication setup mode deadline leaks).Action}
    (chosen : response ∈ (serviceImmediatePolicy setup mode deadline leaks bound profile who
      past view).support) :
    (serviceRuntime setup mode deadline).firstSubmission leaks past response = true := by
  cases transmission : response.transmission with
  | none =>
      simp only [EventGraphRuntime.firstSubmission, EventGraphRuntime.submittedEvent?,
        transmission]
  | some material =>
      obtain ⟨event, action, _, unrecorded, _, decision⟩ :=
        sourceServiceImmediatePolicy_submission chosen transmission
      rw [decision]
      exact (serviceRuntime setup mode deadline).canonicalServiceDecision_firstSubmission leaks
          who past view event
        action unrecorded

/-- Every named immediate submission passes its protected inclusion gate. -/
theorem sourceServiceImmediatePolicy_submissionFits
    {bound : (serviceGraph setup mode).EventId → Nat} {profile : BehavioralProfile setup.program}
    {who : Player} {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView} {response :
        (serviceApplication setup mode deadline leaks).Action}
    (chosen : response ∈ (serviceImmediatePolicy setup mode deadline leaks bound profile who
      past view).support)
    (event : (serviceGraph setup mode).EventId)
    (named : (serviceRuntime setup mode deadline).submittedEvent? leaks response = some event) :
    view.application.publicView.InclusionFitsDeadline
        (serviceRuntime setup mode deadline) bound event := by
  obtain ⟨material, transmission⟩ : ∃ material, response.transmission = some material := by
    cases sent : response.transmission with
    | none => simp only [EventGraphRuntime.submittedEvent?, sent] at named; cases named
    | some material => exact ⟨material, rfl⟩
  obtain ⟨chosenEvent, action, _, _, fits, decision⟩ :=
    sourceServiceImmediatePolicy_submission chosen transmission
  rw [decision] at named
  rw [submittedEvent_canonicalServiceDecision setup leaks who past view chosenEvent action event
    named]
  exact fits

/-- An actual fresh immediate envelope conforms on its actual before-view. -/
theorem sourceServiceImmediatePolicy_freshServiceEnvelope {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat} {profile : BehavioralProfile setup.program}
    {middle : (serviceApplication setup mode deadline leaks).Execution} {who : Player}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining, some who, middle⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks middle who)
    (slots : CanonicalSlotsUsed setup leaks middle who)
    {response : (serviceApplication setup mode deadline leaks).Action}
    (chosen : response ∈ (serviceImmediatePolicy setup mode deadline leaks bound profile who
      (middle.recall who) (middle.observe
          (serviceApplication setup mode deadline leaks) who)).support)
    (material : (serviceApplication setup mode deadline leaks).Submission)
    (submits : response.transmission = some material) :
    (serviceRuntime setup mode deadline).freshServiceEnvelope middle.application.publicView
      ⟨(who, middle.network.nextSerial who), (serviceApplication setup mode deadline leaks).packet
        ((serviceApplication setup mode deadline leaks).submit middle.application who material) who
        (middle.network.known who) material⟩ := by
  obtain ⟨event, action, turn, unrecorded, fits, decision⟩ :=
    sourceServiceImmediatePolicy_submission chosen submits
  have fresh := canonicalSlot_fresh_of_used trace who atTurn slots event turn unrecorded
  exact canonicalServiceDecision_freshServiceEnvelope trace event turn fits.withinDeadline fresh
    action material (by rw [← decision]; exact submits)

/-- At a clear unrecorded binding turn, the immediate response emits and records
its actual protected commitment, regardless of the number of earlier deferrals. -/
theorem sourceServiceImmediatePolicy_binding_call {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat} {profile : BehavioralProfile setup.program}
    {middle : (serviceApplication setup mode deadline leaks).Execution} {who : Player}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining, some who, middle⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks middle who)
    (slots : CanonicalSlotsUsed setup leaks middle who)
    (clear : (serviceRuntime setup mode deadline).serviceRisk leaks bound who (middle.recall who)
      (middle.observe (serviceApplication setup mode deadline leaks) who) = false)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .bind who payload)
    (node : nodeView (serviceGraph setup mode) event = .bind who payload outputEq codeEq)
    (turn : middle.application.publicView.ownTurn? who = some event)
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (middle.recall who) event = false)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (chosen : response ∈ (serviceImmediatePolicy setup mode deadline leaks bound profile who
      (middle.recall who) (middle.observe
          (serviceApplication setup mode deadline leaks) who)).support) :
    ∃ material, response = ⟨some material⟩ ∧
      let app := serviceApplication setup mode deadline leaks
      let message : Message Player (WitnessedPacket (serviceGraph setup mode)) :=
        ⟨(who, middle.network.nextSerial who), app.packet
          (app.submit middle.application who material) who (middle.network.known who) material⟩
      let entry : app.PlayerEntry := ⟨middle.observe app who, response, some message⟩
      FreshCall setup leaks who event bound entry message ∧
        message.payload.call = .commitment event
          (who, .prepared (middle.application.publicView.bindingCount who)) ∧
        (serviceRuntime setup mode deadline).eventRecorded leaks
            ((middle.respond app who response).recall who)
          event = true := by
  have fits : middle.application.publicView.InclusionFitsDeadline
      (serviceRuntime setup mode deadline) bound
      event := by
    by_contra unprotected
    have currentClear :=
        ((serviceRuntime setup mode deadline).serviceRisk_clear_iff leaks bound who _ _).mp clear
            |>.2
    have risky :=
        ((serviceRuntime setup mode deadline).firstUnprotectedBindingOpportunity_iff leaks bound who
      (middle.recall who) (middle.observe (serviceApplication setup mode deadline leaks) who)).mpr
        ⟨rfl, event, who, payload, turn, outputEq, unrecorded, unprotected⟩
    rw [currentClear] at risky
    cases risky
  rw [sourceServiceImmediatePolicy_at_event clear turn] at chosen
  exact sourceServiceCanonicalOpportunity_binding_call trace atTurn slots event payload outputEq
    codeEq node turn unrecorded fits response chosen

/-- One immediate response preserves the owner's submission turns and used
canonical slots. Environment and foreign response closures require no policy
restriction and are supplied separately. -/
theorem sourceServiceImmediatePolicy_canonicalSlots_respond {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat} {profile : BehavioralProfile setup.program}
    {middle : (serviceApplication setup mode deadline leaks).Execution} {who : Player}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining, some who, middle⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks middle who)
    (slots : CanonicalSlotsUsed setup leaks middle who)
    {response : (serviceApplication setup mode deadline leaks).Action}
    (chosen : response ∈ (serviceImmediatePolicy setup mode deadline leaks bound profile who
      (middle.recall who) (middle.observe
          (serviceApplication setup mode deadline leaks) who)).support) :
    OwnSubmissionsAtTurn setup leaks (middle.respond
        (serviceApplication setup mode deadline leaks) who response) who ∧
      CanonicalSlotsUsed setup leaks (middle.respond
          (serviceApplication setup mode deadline leaks) who response)
        who := by
  let app := serviceApplication setup mode deadline leaks
  have appEq :=
      (serviceRuntime setup mode deadline).reactive_respond_application leaks middle who response
  obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
  refine ⟨?_, ?_⟩
  · intro entry member event named
    rw [recalled] at member
    rcases List.mem_append.mp member with old | new
    · exact atTurn entry old event named
    · cases List.mem_singleton.mp new
      exact sourceServiceImmediatePolicy_submitsAtTurn _ _ who _ _ response chosen event named
  · intro serial used
    rw [(serviceRuntime setup mode deadline).submittedCandidateSlots_respond leaks middle who
        response] at used
    rw [appEq.2]
    rcases List.mem_append.mp used with old | new
    · rcases slots serial old with lower | ⟨equal, other, payload, layout, unfinished, recorded⟩
      · exact Or.inl lower
      · refine Or.inr ⟨equal, other, payload, layout, ?_, ?_⟩
        · rw [appEq.1]
          exact unfinished
        · exact (serviceRuntime setup mode deadline).eventRecorded_respond_of_recorded leaks
            middle who who response
            other recorded
    · have slot : (serviceRuntime setup mode deadline).responseCandidateSlot leaks response =
        some serial :=
        Option.mem_toList.mp new
      obtain ⟨material, submits⟩ : ∃ material, response.transmission = some material := by
        unfold EventGraphRuntime.responseCandidateSlot at slot
        split at slot
        · exact ⟨_, ‹_›⟩
        · cases slot
      obtain ⟨event, action, turn, unrecorded, _, rfl⟩ :=
        sourceServiceImmediatePolicy_submission chosen submits
      have owned := (PublicView.ownTurn?_spec _ who event turn).2
      have fresh := canonicalSlot_fresh_of_used trace who atTurn slots event turn unrecorded
      have canonical := canonicalFreshSlot_canonical who (middle.observe app who).application
        fresh
      obtain ⟨selected, ⟨payload, layout⟩, named⟩ := canonicalServiceDecision_candidateSlot who
        (middle.recall who) (middle.observe app who) event owned action serial slot
      rw [canonical] at selected
      cases Option.some.inj selected
      have ready := (middle.application.publicView_eventReady event).mp
        (PublicView.ownTurn?_spec _ who event turn).1
      refine Or.inr ⟨rfl, event, payload, layout, ?_, ?_⟩
      · rw [appEq.1]
        exact ready.1
      · rw [recalled]
        unfold EventGraphRuntime.eventRecorded
        rw [List.any_append]
        simp only [List.any_cons, List.any_nil, Bool.or_false]
        rw [named]
        simp

section Menu

variable [Fintype Player]

/-- The immediate policy is locally admitted at every actual legal risk-menu
history, including histories with earlier deferrals or foreign raw responses. -/
theorem sourceServiceImmediatePolicy_risk_retained
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
    (response : (serviceApplication setup mode deadline leaks).Action)
    (chosen : response ∈ (serviceImmediatePolicy setup mode deadline leaks bound profile who
      (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who)).support) :
    response ∈ bounds.riskActions (serviceRuntime setup mode deadline) leaks bound who
        (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) := by
  rcases sourceServiceImmediatePolicy_cases chosen with rfl | ⟨event, clear, turn, member⟩
  · exact bounds.canonicalActions_subset_risk
      (serviceRuntime setup mode deadline) leaks bound who _ _
      (bounds.silence_canonical (serviceRuntime setup mode deadline) leaks who _ _)
  · rw [bounds.riskActions_of_clear (serviceRuntime setup mode deadline) leaks bound who _ _ clear]
    exact sourceServiceCanonicalOpportunity_risk_retained bounds covered initialCovered capacity
      bound profile who permitted control trace clear event turn response member

/-- The local coverage gives a policy admission certificate on every legal
decision history of the finite risk menu. -/
theorem sourceServiceImmediatePolicy_risk_admissible
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
        bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    (bound : (serviceGraph setup mode).EventId → Nat) (profile : BehavioralProfile setup.program)
    (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler) :
    (bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).Admissible
        (serviceInitialLaw setup mode) horizon scheduler
      who (serviceImmediatePolicy setup mode deadline leaks bound profile who) := by
  intro control trace _ response chosen
  exact sourceServiceImmediatePolicy_risk_retained bounds covered initialCovered capacity bound
    profile who permitted control trace response chosen

end Menu

end Vegas
