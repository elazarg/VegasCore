module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealServiceTimely
public import Vegas.Pending.EffectiveOpening

@[expose] public section

/-! # Honest accepted openings never expire

A first-turn client of a reference that opens a publication exactly when the
opening would be accepted sends a fresh opening at its first turn at each ready
publication whose opening is accepted, and stays silent at a rejected one. A
rejected opening stays rejected while the stored fields are kept. So an honest
owner's ready publication with an accepted opening is always within its
deadline at a scheduler boundary, on every execution mode.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- A publication's opening is rejected: its read footprint is stored and the
opening would not be accepted. -/
def OpeningRejected (config : (serviceGraph setup mode).Config)
    (event : (serviceGraph setup mode).EventId) : Prop :=
  (∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
    (config.store field).isSome) ∧ openingAccepted event config.store = false

/-- Every publication at which the owner has had a turn has a recorded fresh
call of the owner, unless its opening is rejected. -/
def PublicationsSettledEffective (bound : (serviceGraph setup mode).EventId → Nat)
    (execution : (serviceApplication setup mode duration leaks).Execution) (owner : Player) :
    Prop :=
  ∀ event, ((serviceGraph setup mode).outputLayout event).IsPublication →
    (∃ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event) →
    (∃ entry ∈ execution.logs owner, ∃ message,
      FreshCall setup leaks owner event bound entry message) ∨
    OpeningRejected setup execution.application.config event

variable {setup leaks}

/-- A rejected opening stays rejected while stored fields are kept. -/
theorem OpeningRejected.keep {before after : (serviceGraph setup mode).Config}
    {event : (serviceGraph setup mode).EventId}
    (kept : ∀ field value, before.store field = some value → after.store field = some value)
    (rejected : OpeningRejected setup before event) : OpeningRejected setup after event := by
  obtain ⟨available, notAccepted⟩ := rejected
  have agree : Store.AgreeOn after.store before.store
      ((serviceGraph setup mode).nodes event).readFields := by
    intro field read
    obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp (available field read)
    rw [kept field value stored, stored]
  refine ⟨fun field read => ?_, by rw [openingAccepted_congr event agree, notAccepted]⟩
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp (available field read)
  rw [kept field value stored]
  rfl

/-- An accepted opening's binding holds a value. -/
theorem bindingHolds_of_openingAccepted (config : (serviceGraph setup mode).Config)
    (event : (serviceGraph setup mode).EventId)
    (accepted : openingAccepted event config.store = true) : BindingHolds config event := by
  unfold BindingHolds
  unfold openingAccepted at accepted
  cases view : nodeView (serviceGraph setup mode) event with
  | resolve owner payload binding checks outputEq codeEq =>
      rw [view] at accepted
      dsimp only at accepted ⊢
      cases bound : binding.get? config.store with
      | none => simp [EventCode.resolveOutput?, bound] at accepted
      | some result =>
          cases result with
          | success value => exact ⟨value, rfl⟩
          | failure =>
              exfalso
              cases checked : GuardCheck.allAccepted? checks config.store .failure with
              | none => simp [EventCode.resolveOutput?, bound, checked] at accepted
              | some passed =>
                  cases passed <;>
                    simp [EventCode.resolveOutput?, bound, checked] at accepted
  | bind => trivial
  | sample => trivial

private theorem first_of_never
    (execution : (serviceApplication setup mode duration leaks).Execution)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (turn : execution.application.publicView.ownTurn? owner = some event)
    (never : ∀ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event) :
    serviceTurn setup mode duration leaks owner event (execution.logs owner)
      (execution.observe (serviceApplication setup mode duration leaks) owner) = some 0 := by
  change (if execution.application.publicView.ownTurn? owner = some event then
    some ((execution.logs owner).countP fun entry =>
      decide (entry.beforeView.application.publicView.ownTurn? owner = some event)) else none) =
        some 0
  simp only [turn, ↓reduceIte, Option.some.injEq]
  rw [List.countP_eq_zero]
  intro entry member
  simpa only [Bool.not_eq_true, decide_eq_false_iff_not] using never entry member

private theorem publicationsSettledEffective_round {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup mode duration) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup mode duration) delay bound)
    (players : Player → (serviceApplication setup mode duration leaks).Policy) (owner : Player)
    {turns : Nat} (reference : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        reference owner event actor ((serviceGraph setup mode).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (follows : players owner = serviceReferenceTurnPolicy setup mode duration leaks bound turns
      (firstTurnTiming setup turns mode) reference owner)
    (count : Nat) (within : count + 1 ≤ horizon)
    (execution next : (serviceApplication setup mode duration leaks).Execution)
    (supported : execution ∈ ((serviceApplication setup mode duration leaks).roundsFrom
      (serviceInitialLaw setup mode) scheduler players count).support)
    (called : PublicationsSettledEffective setup leaks bound execution owner)
    (reached : next ∈ ((serviceApplication setup mode duration leaks).round scheduler players
      execution).support) :
    PublicationsSettledEffective setup leaks bound next owner := by
  let app := serviceApplication setup mode duration leaks
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
    players count (by omega) execution supported
  rw [show horizon - count = (horizon - (count + 1)) + 1 by omega] at trace
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have answered := roundsFrom_activationsAnswered count execution supported
  have atTurn := SubmitsAtTurn.roundsFrom setup leaks (players := players) (who := owner)
    (follows ▸ sourceServiceTurnPolicy_submitsAtTurn_reference setup leaks bound turns
      (firstTurnTiming setup turns mode) reference owner) (serviceInitialLaw setup mode) count
    execution supported
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  have keptMiddle := (keepsStore_step (serviceTimeouts setup mode duration) leaks).environmentStep
    execution middle command moved
  have calledMiddle : PublicationsSettledEffective setup leaks bound middle owner := by
    intro event publication turned
    rw [recallEq] at turned
    rcases called event publication turned with ⟨entry, member, message, call⟩ | failed
    · exact Or.inl ⟨entry, by rw [recallEq]; exact member, message, call⟩
    · exact Or.inr (OpeningRejected.keep keptMiddle failed)
  rcases cases with ⟨_, rfl⟩ | ⟨who, active, response, chosen, rfl⟩
  · exact calledMiddle
  by_cases same : who = owner
  swap
  · have recallSame := app.respond_recall_other middle who owner (Ne.symm same) response
    have kept := (keepsStore_step (serviceTimeouts setup mode duration) leaks).respond middle who
      response
    intro event publication turned
    rw [recallSame] at turned
    rcases calledMiddle event publication turned with ⟨entry, member, message, call⟩ | failed
    · exact Or.inl ⟨entry, by rw [recallSame]; exact member, message, call⟩
    · exact Or.inr (OpeningRejected.keep kept failed)
  subst who
  obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle owner response
  have kept := (keepsStore_step (serviceTimeouts setup mode duration) leaks).respond middle owner
    response
  intro event publication ⟨entry, member, turn⟩
  have old (prior : ∃ entry ∈ middle.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event) :
      (∃ entry ∈ (middle.respond app owner response).logs owner, ∃ message,
        FreshCall setup leaks owner event bound entry message) ∨
      OpeningRejected setup (middle.respond app owner response).application.config event := by
    rcases calledMiddle event publication prior with ⟨call, callMember, message, isCall⟩ | failed
    · exact Or.inl
        ⟨call, by rw [recalled]; exact List.mem_append_left _ callMember, message, isCall⟩
    · exact Or.inr (OpeningRejected.keep kept failed)
  rw [recalled] at member
  rcases List.mem_append.mp member with present | fresh
  · exact old ⟨entry, present, turn⟩
  obtain rfl := List.mem_singleton.mp fresh
  by_cases prior : ∃ entry ∈ middle.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event
  · exact old prior
  have never : ∀ entry ∈ middle.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event :=
    fun entry present equal => prior ⟨entry, present, equal⟩
  have commandEq : command = .activate owner := by
    cases command <;> simp_all [ReactiveApplication.Command.actor?]
  subst commandEq
  have appEq := activation_application setup leaks execution middle owner moved
  have turnNow : middle.application.publicView.ownTurn? owner = some event := turn
  obtain ⟨readyView, owned⟩ := middle.application.publicView.ownTurn?_spec owner event turnNow
  have ready := (middle.application.publicView_eventReady event).mp readyView
  have readyBefore : execution.application.config.cut.Ready event := by
    rw [← appEq]
    exact ready
  have activeBefore := execution.application.active_of_ready_owned facts.quiescent readyBefore
    owned
  have first := first_of_never middle owner event turnNow never
  have firstBefore : serviceTurn setup mode duration leaks owner event (execution.logs owner)
      (middle.observe app owner) = some 0 := by
    rw [← recallEq]
    exact first
  have fits := firstTurn_inclusionFits contract timely trace answered owned readyBefore
    firstBefore
  have fitsMiddle : middle.application.publicView.InclusionFitsDeadline
      (serviceTimeouts setup mode duration) bound event := by
    rw [appEq]
    exact fits
  obtain ⟨middleTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon
    scheduler (horizon - (count + 1)) execution middle (.activate owner) trace selected moved
  rw [active] at middleTrace
  obtain ⟨actorName, payload, binding, checks, outputEq, codeEq, node⟩ :=
    exists_resolve_of_publication publication
  have actorSame : actorName = owner :=
    Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
  subst actorName
  cases acceptedEq : openingAccepted event middle.application.config.store
  · exact Or.inr (OpeningRejected.keep kept ⟨fun field read =>
      middle.application.config.read_available ready read, acceptedEq⟩)
  have holds := bindingHolds_of_openingAccepted middle.application.config event acceptedEq
  have effectiveMiddle : EffectiveAction middle.application.config event
      (EventField.openAction _ publication) :=
    effectiveAction_of_bindingHolds middle.application.config event publication holds
  have activeMiddle : owner ∉ middle.application.config.defaulted := by
    rw [appEq]
    exact activeBefore
  obtain ⟨material, submits⟩ := canonicalServiceDecision_opening_transmits
    ⟨horizon - (count + 1), some owner, middle⟩ middleTrace owner event turnNow publication
    effectiveMiddle
  have unrecorded : (eventRecorded (serviceTimeouts setup mode duration)) leaks (middle.logs owner)
      event = false := by
    apply Bool.eq_false_of_not_eq_true
    intro recorded
    obtain ⟨earlier, present, named⟩ :=
      ((eventRecorded_iff (serviceTimeouts setup mode duration)) leaks _ event).mp recorded
    have presentBefore : earlier ∈ execution.logs owner := by
      rw [← recallEq]
      exact present
    exact never earlier present (atTurn earlier presentBefore event named)
  rw [follows, sourceServiceTurnPolicy_firstTurn_reference owned first] at chosen
  unfold serviceReferenceOpportunity at chosen
  have fitsView : (middle.observe app owner).application.publicView.InclusionFitsDeadline
      (serviceTimeouts setup mode duration) bound event := fitsMiddle
  rw [ite_eq_right (by rw [unrecorded]; exact Bool.false_ne_true), ite_eq_left fitsView,
    sourceServiceCanonicalPolicy_at_event_reference setup leaks reference owner middle event
      turnNow owned, dite_eq_right activeMiddle] at chosen
  have opened : reference owner event owned ((serviceGraph setup mode).playerObserve owner
      middle.application.config) activeMiddle = PMF.pure (EventField.openAction _ publication) := by
    rw [decides middle.application.config event owner payload binding checks outputEq codeEq
      node owned activeMiddle, acceptedEq, openAction_eq_cast_true outputEq publication]
  simp only [id] at chosen
  rw [opened, PMF.pure_map, PMF.pure_bind, submits, ite_eq_right (by simp),
    PMF.mem_support_pure_iff] at chosen
  subst chosen
  have shape : (canonicalServiceDecision (serviceTimeouts setup mode duration)) leaks owner
      (middle.logs owner) (middle.observe app owner) event (EventField.openAction _ publication) =
        (⟨some material⟩ : app.Action) := by
    rw [← submits]
  have call := canonical_freshCall middleTrace bound owner event turnNow fitsMiddle
    (EventField.openAction _ publication) material submits
  rw [shape] at call ⊢
  have recalledExact : (middle.respond app owner ⟨some material⟩).logs owner =
      middle.logs owner ++ [⟨middle.observe app owner, ⟨some material⟩,
        some ⟨(owner, middle.network.nextSerial owner), app.packet
          (app.submit middle.application owner material) owner (middle.network.known owner)
          material⟩⟩] := by
    simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
    rfl
  rw [recalledExact]
  exact Or.inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), _, call⟩

theorem publicationsSettledEffective_roundsFrom {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup mode duration) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup mode duration) delay bound)
    (players : Player → (serviceApplication setup mode duration leaks).Policy) (owner : Player)
    {turns : Nat} (reference : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        reference owner event actor ((serviceGraph setup mode).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (follows : players owner = serviceReferenceTurnPolicy setup mode duration leaks bound turns
      (firstTurnTiming setup turns mode) reference owner) :
    ∀ count execution, count ≤ horizon →
      execution ∈ ((serviceApplication setup mode duration leaks).roundsFrom
        (serviceInitialLaw setup mode) scheduler players count).support →
      PublicationsSettledEffective setup leaks bound execution owner := by
  let app := serviceApplication setup mode duration leaks
  intro count
  induction count with
  | zero =>
      intro execution _ reached
      obtain ⟨state, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      intro event _ ⟨entry, member, _⟩
      cases member
  | succ count ih =>
      intro execution within reached
      rw [app.roundsFrom_succ] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact publicationsSettledEffective_round contract timely players owner reference decides
        follows count
        within prior execution priorMem (ih prior (by omega) priorMem) moved

theorem effectivePublication_withinDeadline {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup mode duration) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup mode duration) delay bound)
    (players : Player → (serviceApplication setup mode duration leaks).Policy) (owner : Player)
    {turns : Nat} (reference : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        reference owner event actor ((serviceGraph setup mode).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (follows : players owner = serviceReferenceTurnPolicy setup mode duration leaks bound turns
      (firstTurnTiming setup turns mode) reference owner)
    (count : Nat) (within : count ≤ horizon)
    (execution : (serviceApplication setup mode duration leaks).Execution)
    (supported : execution ∈ ((serviceApplication setup mode duration leaks).roundsFrom
      (serviceInitialLaw setup mode) scheduler players count).support)
    (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (publication : ((serviceGraph setup mode).outputLayout event).IsPublication)
    (accepted : openingAccepted event execution.application.config.store = true) :
    execution.application.WithinDeadline (serviceTimeouts setup mode duration) event := by
  let app := serviceApplication setup mode duration leaks
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
    players count within execution supported
  by_cases turned : ∃ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event
  · obtain ⟨entry, member, message, call⟩ | failed :=
      publicationsSettledEffective_roundsFrom contract
      timely players owner reference decides follows count execution within supported event
      publication turned
    swap
    · rw [failed.2] at accepted
      cases accepted
    obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp member
    have once := (sourceServiceTurnPolicy_freshCalls_reference scheduler players owner
      (firstTurnTiming setup turns mode) reference follows count execution supported).2
    have sole := FreshCall.sole trace owner event once earlier entry later message split call
    have settled := settlesFreshCalls_history setup leaks contract.inclusion owner event owned
      trace earlier entry later message split call sole
    exact FreshCall.withinDeadline setup leaks owner event owned trace
      (ProtectedInclusion.at (serviceTimeouts setup mode duration) leaks contract.inclusion _ trace)
      earlier entry later message split call sole settled ready.1
  · have never : ∀ entry ∈ execution.logs owner,
        entry.beforeView.application.publicView.ownTurn? owner ≠ some event :=
      fun entry present equal => turned ⟨entry, present, equal⟩
    have first := first_of_never execution owner event
      (serviceOwnTurn?_of_ready setup execution.application ready owned) never
    exact (firstTurn_inclusionFits contract timely trace
      (roundsFrom_activationsAnswered count execution supported) owned ready
      first).withinDeadline

end Vegas
