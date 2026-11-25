module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceAsyncTimeliness
public import Vegas.Game.SourceServiceFirstTurnOpportunity
public import Vegas.Game.SourceServiceCanonicalAcceptance
public import Vegas.Game.SourceServiceCanonicalSlots
public import Vegas.Game.SourceServiceTurnSubmissions
public import Vegas.Game.SourceServiceFirstTurnMixture
public import Vegas.Pending.CanonicalOutcomePublication

@[expose] public section

/-! # Honest publications never expire

A first-turn client of a reference that opens every publication sends a fresh
opening at its first turn at each ready publication whose binding holds a
value. Before that turn the reaction contract keeps the event
inside its protected window; after it, protected inclusion settles the call
before the deadline. So an honest owner's ready publication is always within its
deadline at a scheduler boundary when the event is its actor's unique ready turn.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))

/-- Every publication at which the owner has had a turn has a recorded fresh
call of the owner, unless its binding holds a failure. -/
private def PublicationSettled (bound : (serviceGraph setup deps).EventId → Nat)
    (execution : (serviceApplication setup deps duration leaks).Execution) (owner : Player)
    (event : (serviceGraph setup deps).EventId) :
    Prop :=
  ((serviceGraph setup deps).outputLayout event).IsPublication →
    (∃ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event) →
    (∃ entry ∈ execution.logs owner, ∃ message,
      FreshCall (serviceTimeouts setup deps duration) leaks owner event bound entry message) ∨
    BindingFails execution.application.config event

variable {setup leaks}

/-- A publication whose binding holds a value can be opened. -/
theorem effectiveAction_of_bindingHolds (config : (serviceGraph setup deps).Config)
    (event : (serviceGraph setup deps).EventId)
    (publication : ((serviceGraph setup deps).outputLayout event).IsPublication)
    (holds : BindingHolds config event) :
    EffectiveAction config event (EventField.openAction _ publication) := by
  unfold BindingHolds at holds
  unfold EffectiveAction
  cases view : nodeView (serviceGraph setup deps) event with
  | resolve owner payload binding checks outputEq codeEq =>
      rw [view] at holds
      exact fun _ => holds
  | bind owner payload outputEq codeEq => trivial
  | sample payload law outputEq codeEq => trivial

/-- The canonical opening of an effective publication transmits. -/
theorem canonicalServiceDecision_opening_transmits {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    (control : (serviceApplication setup deps duration leaks).Control)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace (some control))
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (turn : control.execution.application.publicView.ownTurn? owner = some event)
    (publication : ((serviceGraph setup deps).outputLayout event).IsPublication)
    (effective : EffectiveAction control.execution.application.config event
      (EventField.openAction _ publication)) :
    ∃ material, ((canonicalServiceDecision (serviceTimeouts setup deps duration)) leaks owner
      (control.execution.logs owner)
      (control.execution.observe (serviceApplication setup deps duration leaks) owner) event
        (EventField.openAction _ publication)).transmission = some material := by
  let app := serviceApplication setup deps duration leaks
  have facts := legalFacts setup leaks horizon scheduler control trace
  obtain ⟨readyView, owned⟩ :=
    control.execution.application.publicView.ownTurn?_spec owner event turn
  have ready := (control.execution.application.publicView_eventReady event).mp readyView
  have active := control.execution.application.active_of_ready_owned facts.quiescent ready owned
  cases node : nodeView (serviceGraph setup deps) event with
  | sample payload law outputEq codeEq =>
      have impossible := publication
      rw [outputEq] at impossible
      exact impossible.elim
  | bind actor payload outputEq codeEq =>
      have impossible := publication
      rw [outputEq] at impossible
      exact impossible.elim
  | resolve actor payload binding checks outputEq codeEq =>
      have sameActor : actor = owner :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst actor
      have actionEq := openAction_eq_cast_true outputEq publication
      have successful : ∃ value, binding.get? control.execution.application.config.store =
          some (.success value) := by
        have possible : cast (congrArg EventGraph.EventField.Action outputEq)
            (EventField.openAction _ publication) = true →
            ∃ value, binding.get? control.execution.application.config.store =
              some (.success value) := by
          simpa only [EffectiveAction, node] using effective
        apply possible
        rw [actionEq]
        simp only [cast_cast, cast_eq]
      obtain ⟨value, stored⟩ := successful
      obtain ⟨candidate, accepted, candidateOwner, _⟩ :=
        facts.binding.success_provenance binding value stored
      have observedStored : binding.get?
          (control.execution.observe app owner).application.observation.store =
            some (.success value) := by
        change binding.get? ((serviceGraph setup deps).playerStore owner
          control.execution.application.config.store) = _
        rw [binding.get?_playerStore owner _ rfl, stored]
      have transmits := (canonicalServiceDecision_openable (serviceTimeouts setup deps duration))
        leaks owner (control.execution.logs owner) (control.execution.observe app owner) event
        owner payload binding checks outputEq codeEq node active value observedStored candidate
        accepted candidateOwner
      rw [actionEq]
      cases sent : ((canonicalServiceDecision (serviceTimeouts setup deps duration)) leaks owner
          (control.execution.logs owner) (control.execution.observe app owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).transmission with
      | none => exact (transmits sent).elim
      | some material => exact ⟨material, rfl⟩

private theorem first_of_never
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (turn : execution.application.publicView.ownTurn? owner = some event)
    (never : ∀ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event) :
    turnIndex (serviceTimeouts setup deps duration) leaks owner event (execution.logs owner)
      (execution.observe (serviceApplication setup deps duration leaks) owner) = some 0 := by
  change (if execution.application.publicView.ownTurn? owner = some event then
    some ((execution.logs owner).countP fun entry =>
      decide (entry.beforeView.application.publicView.ownTurn? owner = some event)) else none) =
        some 0
  simp only [turn, ↓reduceIte, Option.some.injEq]
  rw [List.countP_eq_zero]
  intro entry member
  simpa only [Bool.not_eq_true, decide_eq_false_iff_not] using never entry member


private theorem publicationSettled_round {event : (serviceGraph setup deps).EventId}
    (unique : (serviceGraph setup deps).OwnerSolitary event) {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
        (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (players : Player → (serviceApplication setup deps duration leaks).Policy) (owner : Player)
    {turns : Nat} (reference : (serviceGraph setup deps).BehavioralProfile)
    (opens : OpensPublications reference)
    (follows : players owner = turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) reference owner)
    (count : Nat) (within : count + 1 ≤ horizon)
    (execution next : (serviceApplication setup deps duration leaks).Execution)
    (supported : execution ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler players count).support)
    (called : PublicationSettled setup leaks bound execution owner event)
    (reached : next ∈ ((serviceApplication setup deps duration leaks).round scheduler players
      execution).support) :
    PublicationSettled setup leaks bound next owner event := by
  let app := serviceApplication setup deps duration leaks
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup deps) horizon scheduler
    players count (by omega) execution supported
  rw [show horizon - count = (horizon - (count + 1)) + 1 by omega] at trace
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have answered := roundsFrom_activationsAnswered count execution supported
  have atTurn := SubmitsAtTurn.roundsFrom setup leaks (players := players) (who := owner)
    (follows ▸ sourceServiceTurnPolicy_submitsAtTurn_reference setup leaks bound turns
      (firstTurnTiming setup turns deps) reference owner) (serviceInitialLaw setup deps) count
    execution supported
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  have keptMiddle := (keepsStore_step (serviceTimeouts setup deps duration) leaks).environmentStep
    execution middle command moved
  have calledMiddle : PublicationSettled setup leaks bound middle owner event := by
    intro publication turned
    rw [recallEq] at turned
    rcases called publication turned with ⟨entry, member, message, call⟩ | failed
    · exact Or.inl ⟨entry, by rw [recallEq]; exact member, message, call⟩
    · exact Or.inr (BindingFails.keep keptMiddle failed)
  rcases cases with ⟨_, rfl⟩ | ⟨who, active, response, chosen, rfl⟩
  · exact calledMiddle
  by_cases same : who = owner
  swap
  · have recallSame := app.respond_recall_other middle who owner (Ne.symm same) response
    have kept := (keepsStore_step (serviceTimeouts setup deps duration) leaks).respond middle who
      response
    intro publication turned
    rw [recallSame] at turned
    rcases calledMiddle publication turned with ⟨entry, member, message, call⟩ | failed
    · exact Or.inl ⟨entry, by rw [recallSame]; exact member, message, call⟩
    · exact Or.inr (BindingFails.keep kept failed)
  subst who
  obtain ⟨emitted, recalled, _⟩ := respond_recall_self _ leaks middle owner response
  have kept := (keepsStore_step (serviceTimeouts setup deps duration) leaks).respond middle owner
    response
  intro publication ⟨entry, member, turn⟩
  have old (prior : ∃ entry ∈ middle.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event) :
      (∃ entry ∈ (middle.respond app owner response).logs owner, ∃ message,
        FreshCall (serviceTimeouts setup deps duration) leaks owner event bound entry message) ∨
      BindingFails (middle.respond app owner response).application.config event := by
    rcases calledMiddle publication prior with ⟨call, callMember, message, isCall⟩ | failed
    · exact Or.inl
        ⟨call, by rw [recalled]; exact List.mem_append_left _ callMember, message, isCall⟩
    · exact Or.inr (BindingFails.keep kept failed)
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
  have firstBefore : turnIndex (serviceTimeouts setup deps duration)
    leaks owner event (execution.logs owner)
      (middle.observe app owner) = some 0 := by
    rw [← recallEq]
    exact first
  have fits := firstTurn_inclusionFits unique contract timely trace answered owned readyBefore
    firstBefore
  have fitsMiddle : middle.application.publicView.InclusionFitsDeadline
      (serviceTimeouts setup deps duration) bound event := by
    rw [appEq]
    exact fits
  obtain ⟨middleTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup deps) horizon
    scheduler (horizon - (count + 1)) execution middle (.activate owner) trace selected moved
  rw [active] at middleTrace
  rcases bindingHolds_or_fails middle.application.config event ready publication with
    holds | failed
  swap
  · exact Or.inr (BindingFails.keep kept failed)
  have effectiveMiddle : EffectiveAction middle.application.config event
      (EventField.openAction _ publication) :=
    effectiveAction_of_bindingHolds middle.application.config event publication holds
  have activeMiddle : owner ∉ middle.application.config.defaulted := by
    rw [appEq]
    exact activeBefore
  obtain ⟨material, submits⟩ := canonicalServiceDecision_opening_transmits
    ⟨horizon - (count + 1), some owner, middle⟩ middleTrace owner event turnNow publication
    effectiveMiddle
  have unrecorded : (eventRecorded (serviceTimeouts setup deps duration)) leaks (middle.logs owner)
      event = false := by
    apply Bool.eq_false_of_not_eq_true
    intro recorded
    obtain ⟨earlier, present, named⟩ :=
      ((eventRecorded_iff (serviceTimeouts setup deps duration)) leaks _ event).mp recorded
    have presentBefore : earlier ∈ execution.logs owner := by
      rw [← recallEq]
      exact present
    exact never earlier present (atTurn earlier presentBefore event named)
  rw [follows, sourceServiceTurnPolicy_firstTurn_reference owned first] at chosen
  unfold EventGraphRuntime.referenceOpportunity at chosen
  have fitsView : (middle.observe app owner).application.publicView.InclusionFitsDeadline
      (serviceTimeouts setup deps duration) bound event := fitsMiddle
  rw [ite_eq_right (by rw [unrecorded]; exact Bool.false_ne_true), ite_eq_left fitsView,
    sourceServiceCanonicalPolicy_at_event_reference setup leaks reference owner middle event
      turnNow owned, dite_eq_right activeMiddle] at chosen
  have opened := opens middle.application.config event owner owned publication activeMiddle
  simp only [id] at chosen
  rw [opened, PMF.pure_map, PMF.pure_bind, submits, ite_eq_right (by simp),
    PMF.mem_support_pure_iff] at chosen
  subst chosen
  have shape : (canonicalServiceDecision (serviceTimeouts setup deps duration)) leaks owner
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

/-- An actor-solitary publication at which a first-turn owner has had a turn carries a
recorded fresh call, unless its binding holds a failure. -/
private theorem publicationSettled_roundsFrom {event : (serviceGraph setup deps).EventId}
    (unique : (serviceGraph setup deps).OwnerSolitary event) {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
        (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (players : Player → (serviceApplication setup deps duration leaks).Policy) (owner : Player)
    {turns : Nat} (reference : (serviceGraph setup deps).BehavioralProfile)
    (opens : OpensPublications reference)
    (follows : players owner = turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) reference owner) :
    ∀ count execution, count ≤ horizon →
      execution ∈ ((serviceApplication setup deps duration leaks).roundsFrom
        (serviceInitialLaw setup deps) scheduler players count).support →
      PublicationSettled setup leaks bound execution owner event := by
  let app := serviceApplication setup deps duration leaks
  intro count
  induction count with
  | zero =>
      intro execution _ reached
      obtain ⟨state, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      cases (PMF.mem_support_pure_iff _ _).mp supported
      intro _ ⟨entry, member, _⟩
      cases member
  | succ count ih =>
      intro execution within reached
      rw [app.roundsFrom_succ] at reached
      obtain ⟨prior, priorMem, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact publicationSettled_round unique contract timely players owner reference opens follows
        count
        within prior execution priorMem (ih prior (by omega) priorMem) moved

/-- **Honest publications never expire.** Under the asynchronous contract and
its timing budget, a ready publication of a first-turn owner of an opening
reference whose binding holds a value is within its deadline at every scheduler
boundary, whatever the other players and the scheduler do. -/
theorem honestPublication_withinDeadline {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
        (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (players : Player → (serviceApplication setup deps duration leaks).Policy) (owner : Player)
    {turns : Nat} (reference : (serviceGraph setup deps).BehavioralProfile)
    (opens : OpensPublications reference)
    (follows : players owner = turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) reference owner)
    (count : Nat) (within : count ≤ horizon)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (supported : execution ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler players count).support)
    (event : (serviceGraph setup deps).EventId)
    (unique : (serviceGraph setup deps).OwnerSolitary event)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (publication : ((serviceGraph setup deps).outputLayout event).IsPublication)
    (holds : BindingHolds execution.application.config event) :
    execution.application.WithinDeadline (serviceTimeouts setup deps duration) event := by
  let app := serviceApplication setup deps duration leaks
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup deps) horizon scheduler
    players count within execution supported
  by_cases turned : ∃ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event
  · obtain ⟨entry, member, message, call⟩ | failed := publicationSettled_roundsFrom unique contract
      timely players owner reference opens follows count execution within supported
      publication turned
    swap
    · exact (holds.not_fails failed).elim
    obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp member
    have once := (sourceServiceTurnPolicy_freshCalls_reference scheduler players owner
      (firstTurnTiming setup turns deps) reference follows count execution supported).2
    have sole := FreshCall.sole trace owner event once earlier entry later message split call
    have settled := settlesFreshCalls_history setup leaks contract.inclusion owner event unique
      owned
      trace earlier entry later message split call sole
    exact FreshCall.withinDeadline setup leaks owner event owned trace
      (ProtectedInclusion.at (serviceTimeouts setup deps duration) leaks contract.inclusion _ trace)
      earlier entry later message split call sole settled ready.1
  · have never : ∀ entry ∈ execution.logs owner,
        entry.beforeView.application.publicView.ownTurn? owner ≠ some event :=
      fun entry present equal => turned ⟨entry, present, equal⟩
    have first := first_of_never execution owner event
      (execution.application.ownTurn?_of_ready unique ready owned) never
    exact (firstTurn_inclusionFits unique contract timely trace
      (roundsFrom_activationsAnswered count execution supported) owned ready
      first).withinDeadline

end Vegas
