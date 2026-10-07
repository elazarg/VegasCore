/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCanonicalConformance
import Interaction.ScheduledOpening

/-! # Actual binding calls at the first prescribed turn

The exact first-turn timing selects the canonical source opportunity. At an
owner's first ready binding turn with a protected inclusion window, every
supported response emits an acceptable fresh commitment and records its event.
The recall and slot premises concern this owner alone.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

variable {setup leaks}

/-- A pure first-turn timing retains its selection after every own transcript. -/
theorem sourceServiceTurnPolicy_firstTurn {bound : (serviceGraph setup mode).EventId → Nat}
    {turns : Nat} {profile : BehavioralProfile setup.program} {who : Player}
    {past : List (serviceApplication setup mode deadline leaks).PlayerEntry}
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    {event : (serviceGraph setup mode).EventId}
    (owned : (serviceGraph setup mode).actor? event = some who)
    (first : serviceTurn setup mode deadline leaks who event past view = some 0) :
    serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
        profile who past view =
      serviceCanonicalOpportunity setup mode deadline leaks bound profile who event past view := by
  let app := serviceApplication setup mode deadline leaks
  let family := serviceTurnFamily setup mode deadline leaks bound profile who event turns
  have pin : (app.policyMixture (PMF.pure (0 : Fin (turns + 1))) family).posterior past =
      PMF.pure 0 := by
    simpa only [List.nil_append] using app.policyMixture_posterior_pure_append
      (PMF.pure (0 : Fin (turns + 1))) family [] past 0 rfl
  rw [sourceServiceTurnPolicy_turn setup leaks bound turns _ profile who past view event owned
    (sourceServiceTurn_first first).1]
  change (app.policyMixture (PMF.pure (0 : Fin (turns + 1))) family).policy past view = _
  rw [app.policyMixture_policy, pin, PMF.pure_bind]
  exact app.turnScheduledPolicy_selected _ (0 : Fin (turns + 1)) _ _ past view first

/-- No earlier own submission named an event before its first turn. -/
theorem sourceServiceFirstTurn_unrecorded
    {execution : (serviceApplication setup mode deadline leaks).Execution} {who : Player}
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    {event : (serviceGraph setup mode).EventId}
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    (first : serviceTurn setup mode deadline leaks who event (execution.recall who) view = some 0) :
    (serviceRuntime setup mode deadline).eventRecorded leaks (execution.recall who) event =
    false := by
  apply Bool.eq_false_of_not_eq_true
  intro recorded
  obtain ⟨entry, member, submitted⟩ := List.any_eq_true.mp recorded
  exact (sourceServiceTurn_first first).2 entry member
    (atTurn entry member event (of_decide_eq_true submitted))

/-- Every protected unsent canonical binding opportunity emits its actual call,
including after earlier silent turns or when private opening material is absent. -/
theorem sourceServiceCanonicalOpportunity_binding_call {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    {profile : BehavioralProfile setup.program} {who : Player}
    {middle : (serviceApplication setup mode deadline leaks).Execution}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining, some who, middle⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks middle who)
    (slots : CanonicalSlotsUsed setup leaks middle who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .bind who payload)
    (node : nodeView (serviceGraph setup mode) event = .bind who payload outputEq codeEq)
    (turn : middle.application.publicView.ownTurn? who = some event)
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks (middle.recall who)
        event = false)
    (fits : middle.application.publicView.InclusionFitsDeadline (serviceRuntime setup mode deadline)
        bound event)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (chosen : response ∈
        (serviceCanonicalOpportunity setup mode deadline leaks bound profile who event
        (middle.recall who)
        (middle.observe (serviceApplication setup mode deadline leaks) who)).support) :
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
  let app := serviceApplication setup mode deadline leaks
  have owned := nodeView_bind_actor outputEq codeEq
  have fitsView : PublicView.InclusionFitsDeadline (serviceRuntime setup mode deadline) bound
      (middle.observe (serviceApplication setup mode deadline leaks) who).application.publicView
      event := fits
  have fresh := canonicalSlot_fresh_of_used trace who atTurn slots event turn unrecorded
  have canonical := canonicalFreshSlot_canonical who (middle.observe app who).application fresh
  unfold serviceCanonicalOpportunity at chosen
  simp only [unrecorded, Bool.false_eq_true, ↓reduceIte] at chosen
  rw [ite_eq_left fitsView] at chosen
  rw [PMF.support_bind] at chosen
  obtain ⟨decided, sampled, after⟩ := Set.mem_iUnion₂.mp chosen
  simp only [sourceServiceCanonicalPolicy_at_event setup leaks profile who middle event turn owned,
    PMF.support_map] at sampled
  obtain ⟨action, _, rfl⟩ := sampled
  let choice : PublicationResult (L.Val payload) :=
    cast (congrArg EventGraph.EventField.Action outputEq) action
  let material : app.Submission :=
    ⟨⟨.commitment event (who, .prepared (middle.application.publicView.bindingCount who)),
      (PublicationResult.equivOption choice).map (fun value => ⟨payload, value⟩)⟩, .none⟩
  have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
      choice := by simp only [choice, cast_cast, cast_eq]
  have decision := (serviceRuntime setup mode deadline).canonicalServiceDecision_binding leaks who
    (middle.recall who) (middle.observe app who) event payload outputEq codeEq node
    (middle.application.publicView.bindingCount who) canonical choice
  rw [← actionEq] at decision
  have submits :
      ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks who (middle.recall who)
      (middle.observe app who) event action).transmission = some material := by
    rw [decision]
    dsimp only [material]
    cases choice <;> rfl
  have notSilent :
      ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks who (middle.recall who)
      (middle.observe (serviceApplication setup mode deadline leaks) who) event
      action).transmission ≠ none := by
    rw [submits]
    exact Option.some_ne_none _
  rw [ite_eq_right notSilent, PMF.mem_support_pure_iff] at after
  subst response
  have responseEq : (serviceRuntime setup mode deadline).canonicalServiceDecision leaks who
      (middle.recall who)
      (middle.observe app who) event action = ⟨some material⟩ := by
    cases response : (serviceRuntime setup mode deadline).canonicalServiceDecision leaks who
        (middle.recall who)
      (middle.observe app who) event action with
    | mk transmission =>
        rw [response] at submits
        change transmission = some material at submits
        cases submits
        rfl
  refine ⟨material, responseEq, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨material, submits⟩, rfl, rfl, ?_, ?_, fits, ?_⟩
    · rw [reactiveApplication_packet_none]
      rfl
    · exact (PublicView.ownTurn?_spec _ who event turn).1
    · exact EventGraphRuntime.freshServiceEnvelope.acceptable (serviceRuntime setup mode deadline)
        (canonicalServiceDecision_freshServiceEnvelope trace event turn fits.withinDeadline
          fresh action material submits)
  · rw [reactiveApplication_packet_none]
  · rw [responseEq, respond_submit_recall]
    unfold EventGraphRuntime.eventRecorded
    rw [List.any_append]
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    have named : (serviceRuntime setup mode deadline).submittedEvent? leaks ⟨some material⟩ = some
        event := rfl
    rw [named]
    simp only [decide_true, Bool.or_true]

/-- Every supported first-turn binding response emits its actual protected call,
including when its private opening material is absent. -/
theorem sourceServiceFirstTurn_binding_call {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat} {turns : Nat}
    {profile : BehavioralProfile setup.program} {who : Player}
    {middle : (serviceApplication setup mode deadline leaks).Execution}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining, some who, middle⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks middle who)
    (slots : CanonicalSlotsUsed setup leaks middle who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .bind who payload)
    (node : nodeView (serviceGraph setup mode) event = .bind who payload outputEq codeEq)
    (first : serviceTurn setup mode deadline leaks who event (middle.recall who)
      (middle.observe (serviceApplication setup mode deadline leaks) who) = some 0)
    (fits : middle.application.publicView.InclusionFitsDeadline (serviceRuntime setup mode deadline)
        bound event)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (chosen : response ∈ (serviceTurnPolicy setup mode deadline leaks bound turns
      (firstTurnTiming setup turns mode) profile who (middle.recall who)
        (middle.observe (serviceApplication setup mode deadline leaks) who)).support) :
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
  rw [sourceServiceTurnPolicy_firstTurn (nodeView_bind_actor outputEq codeEq) first] at chosen
  exact sourceServiceCanonicalOpportunity_binding_call trace atTurn slots event payload outputEq
    codeEq node (sourceServiceTurn_first first).1 (sourceServiceFirstTurn_unrecorded atTurn first)
    fits response chosen

end Vegas
