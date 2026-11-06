/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceAsyncTimeliness
import Vegas.Game.SourceServiceFirstTurnOpportunity
import Vegas.Game.SourceServiceCanonicalAcceptance
import Vegas.Game.SourceServiceCanonicalSlots
import Vegas.Game.SourceServiceTurnSubmissions
import Vegas.Game.SourceServiceFirstTurnMixture
import Vegas.Pending.CanonicalKeyPublication

/-! # Honest publications never expire

A first-turn client of a reference that opens every publication sends a fresh
opening at its first turn at each ready publication, provided the publication's
binding holds a value. Before that turn the reaction contract keeps the event
inside its protected window; after it, protected inclusion settles the call
before the deadline. So an honest owner's ready publication is always within its
deadline at a scheduler boundary, on every execution mode.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- Every ready publication of an active owner holds an openable binding. -/
def PublicationsEffective (config : (serviceGraph setup mode).Config) : Prop :=
  ∀ event owner, config.cut.Ready event → (serviceGraph setup mode).actor? event = some owner →
    owner ∉ config.defaulted →
    ∀ publication : ((serviceGraph setup mode).outputLayout event).IsPublication,
      EffectiveAction config event (EventField.openAction _ publication)

/-- Every publication at which the owner has had a turn has a recorded fresh
call of the owner. -/
def PublicationsCalled (bound : (serviceGraph setup mode).EventId → Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution) (owner : Player) :
    Prop :=
  ∀ event, ((serviceGraph setup mode).outputLayout event).IsPublication →
    (∃ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event) →
    ∃ entry ∈ execution.logs owner, ∃ message, FreshCall setup leaks owner event bound entry message

variable {setup leaks}

/-- The canonical opening of an effective publication transmits. -/
theorem canonicalServiceDecision_opening_transmits {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? owner = some event)
    (publication : ((serviceGraph setup mode).outputLayout event).IsPublication)
    (effective : EffectiveAction control.execution.application.config event
      (EventField.openAction _ publication)) :
    ∃ material, ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner
      (control.execution.logs owner)
      (control.execution.observe (serviceApplication setup mode deadline leaks) owner) event
        (EventField.openAction _ publication)).transmission = some material := by
  let app := serviceApplication setup mode deadline leaks
  have facts := legalFacts setup leaks horizon scheduler control trace
  obtain ⟨readyView, owned⟩ :=
    control.execution.application.publicView.ownTurn?_spec owner event turn
  have ready := (control.execution.application.publicView_eventReady event).mp readyView
  have active := control.execution.application.active_of_ready_owned facts.quiescent ready owned
  cases node : nodeView (serviceGraph setup mode) event with
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
        change binding.get? ((serviceGraph setup mode).playerStore owner
          control.execution.application.config.store) = _
        rw [binding.get?_playerStore owner _ rfl, stored]
      have transmits := (serviceRuntime setup mode deadline).canonicalServiceDecision_openable
        leaks owner (control.execution.logs owner) (control.execution.observe app owner) event
        owner payload binding checks outputEq codeEq node active value observedStored candidate
        accepted candidateOwner
      rw [actionEq]
      cases sent : ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner
          (control.execution.logs owner) (control.execution.observe app owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).transmission with
      | none => exact (transmits sent).elim
      | some material => exact ⟨material, rfl⟩

private theorem first_of_never
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (turn : execution.application.publicView.ownTurn? owner = some event)
    (never : ∀ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event) :
    serviceTurn setup mode deadline leaks owner event (execution.logs owner)
      (execution.observe (serviceApplication setup mode deadline leaks) owner) = some 0 := by
  change (if execution.application.publicView.ownTurn? owner = some event then
    some ((execution.logs owner).countP fun entry =>
      decide (entry.beforeView.application.publicView.ownTurn? owner = some event)) else none) =
        some 0
  simp only [turn, ↓reduceIte, Option.some.injEq]
  rw [List.countP_eq_zero]
  intro entry member
  simpa only [Bool.not_eq_true, decide_eq_false_iff_not] using never entry member

/-- A recorded fresh call is the owner's only identifier for its event when the
owner calls once per event. -/
theorem FreshCall.sole {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (once : OneCallPerEvent setup leaks control.execution owner)
    (earlier : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (later : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (split : control.execution.logs owner = earlier ++ entry :: later)
    (call : FreshCall setup leaks owner event bound entry message) :
    ∀ other ∈ earlier ++ later, ¬ EmitsOtherFor (serviceRuntime setup mode deadline) leaks
      other event message.id := by
  have signed := signedCommitments_history (serviceRuntime setup mode deadline) leaks
    (serviceInitialLaw setup mode) (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨_, rfl⟩) horizon scheduler trace
  have submitted (current : (serviceApplication setup mode deadline leaks).PlayerEntry)
      (recorded : current ∈ control.execution.logs owner)
      (sent : Message Player (WitnessedPacket (serviceGraph setup mode)))
      (emitted : current.emitted = some sent)
      (named : sent.payload.call.event? (serviceGraph setup mode) = some event) :
      (serviceRuntime setup mode deadline).submittedEvent? leaks current.action = some event := by
    obtain ⟨_sender, material, transmitted, packet⟩ :=
      signed.emissions owner current recorded sent emitted
    simp only [EventGraphRuntime.submittedEvent?, transmitted]
    rw [← packet]
    exact named
  have entryMember : entry ∈ control.execution.logs owner := by rw [split]; simp
  intro other otherMember ⟨second, emittedOther, _, secondAddressed, differentId⟩
  have otherRecall : other ∈ control.execution.logs owner := by
    rw [split]
    rcases List.mem_append.mp otherMember with inside | inside
    · exact List.mem_append_left _ inside
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ inside)
  exact differentId (once other otherRecall entry entryMember event second message
    (submitted other otherRecall second emittedOther secondAddressed)
    (submitted entry entryMember message call.emitted call.addressed) emittedOther call.emitted)

private theorem publicationsCalled_round {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (owner : Player)
    {turns : Nat} (reference : (serviceGraph setup mode).BehavioralProfile)
    (opens : OpensPublications reference)
    (follows : players owner = serviceReferenceTurnPolicy setup mode deadline leaks bound turns
      (firstTurnTiming setup turns mode) reference owner)
    (count : Nat) (within : count + 1 ≤ horizon)
    (execution next : (serviceApplication setup mode deadline leaks).Execution)
    (supported : execution ∈ ((serviceApplication setup mode deadline leaks).roundsFrom
      (serviceInitialLaw setup mode) scheduler players count).support)
    (effective : PublicationsEffective setup execution.application.config)
    (called : PublicationsCalled setup leaks bound execution owner)
    (reached : next ∈ ((serviceApplication setup mode deadline leaks).round scheduler players
      execution).support) :
    PublicationsCalled setup leaks bound next owner := by
  let app := serviceApplication setup mode deadline leaks
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
  have calledMiddle : PublicationsCalled setup leaks bound middle owner := by
    unfold PublicationsCalled
    rw [recallEq]
    exact called
  rcases cases with ⟨_, rfl⟩ | ⟨who, active, response, chosen, rfl⟩
  · exact calledMiddle
  by_cases same : who = owner
  swap
  · have recallSame := app.respond_recall_other middle who owner (Ne.symm same) response
    unfold PublicationsCalled
    rw [recallSame]
    exact calledMiddle
  subst who
  obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle owner response
  intro event publication ⟨entry, member, turn⟩
  have old (prior : ∃ entry ∈ middle.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event) :
      ∃ entry ∈ (middle.respond app owner response).logs owner, ∃ message,
        FreshCall setup leaks owner event bound entry message := by
    obtain ⟨call, callMember, message, isCall⟩ := calledMiddle event publication prior
    exact ⟨call, by rw [recalled]; exact List.mem_append_left _ callMember, message, isCall⟩
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
  have firstBefore : serviceTurn setup mode deadline leaks owner event (execution.logs owner)
      (middle.observe app owner) = some 0 := by
    rw [← recallEq]
    exact first
  have fits := firstTurn_inclusionFits contract timely trace answered owned readyBefore
    firstBefore
  have fitsMiddle : middle.application.publicView.InclusionFitsDeadline
      (serviceRuntime setup mode deadline) bound event := by
    rw [appEq]
    exact fits
  obtain ⟨middleTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon
    scheduler (horizon - (count + 1)) execution middle (.activate owner) trace selected moved
  rw [active] at middleTrace
  have effectiveMiddle : EffectiveAction middle.application.config event
      (EventField.openAction _ publication) := by
    rw [appEq]
    exact effective event owner readyBefore owned activeBefore publication
  have activeMiddle : owner ∉ middle.application.config.defaulted := by
    rw [appEq]
    exact activeBefore
  obtain ⟨material, submits⟩ := canonicalServiceDecision_opening_transmits
    ⟨horizon - (count + 1), some owner, middle⟩ middleTrace owner event turnNow publication
    effectiveMiddle
  have unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks (middle.logs owner)
      event = false := by
    apply Bool.eq_false_of_not_eq_true
    intro recorded
    obtain ⟨earlier, present, named⟩ :=
      ((serviceRuntime setup mode deadline).eventRecorded_iff leaks _ event).mp recorded
    have presentBefore : earlier ∈ execution.logs owner := by
      rw [← recallEq]
      exact present
    exact never earlier present (atTurn earlier presentBefore event named)
  rw [follows, sourceServiceTurnPolicy_firstTurn_reference owned first] at chosen
  unfold serviceReferenceOpportunity at chosen
  have fitsView : (middle.observe app owner).application.publicView.InclusionFitsDeadline
      (serviceRuntime setup mode deadline) bound event := fitsMiddle
  rw [ite_eq_right (by rw [unrecorded]; exact Bool.false_ne_true), ite_eq_left fitsView,
    sourceServiceCanonicalPolicy_at_event_reference setup leaks reference owner middle event
      turnNow owned, dite_eq_right activeMiddle] at chosen
  have opened := opens middle.application.config event owner owned publication activeMiddle
  simp only [id] at chosen
  rw [opened, PMF.pure_map, PMF.pure_bind, submits, ite_eq_right (by simp),
    PMF.mem_support_pure_iff] at chosen
  subst chosen
  have shape : (serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner
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
  exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), _, call⟩

/-- Every publication at which a first-turn owner has had a turn carries a
recorded fresh call, when publications are effective along the run. -/
theorem publicationsCalled_roundsFrom {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (owner : Player)
    {turns : Nat} (reference : (serviceGraph setup mode).BehavioralProfile)
    (opens : OpensPublications reference)
    (follows : players owner = serviceReferenceTurnPolicy setup mode deadline leaks bound turns
      (firstTurnTiming setup turns mode) reference owner)
    (effective : ∀ count execution, count ≤ horizon →
      execution ∈ ((serviceApplication setup mode deadline leaks).roundsFrom
        (serviceInitialLaw setup mode) scheduler players count).support →
      PublicationsEffective setup execution.application.config) :
    ∀ count execution, count ≤ horizon →
      execution ∈ ((serviceApplication setup mode deadline leaks).roundsFrom
        (serviceInitialLaw setup mode) scheduler players count).support →
      PublicationsCalled setup leaks bound execution owner := by
  let app := serviceApplication setup mode deadline leaks
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
      exact publicationsCalled_round contract timely players owner reference opens follows count
        within prior execution priorMem (effective count prior (by omega) priorMem)
        (ih prior (by omega) priorMem) moved

/-- **Honest publications never expire.** Under the asynchronous contract and
its timing budget, a ready publication of a first-turn owner of an opening
reference is within its deadline at every scheduler boundary, whatever the other
players and the scheduler do, when publications are effective along the run. -/
theorem honestPublication_withinDeadline {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (owner : Player)
    {turns : Nat} (reference : (serviceGraph setup mode).BehavioralProfile)
    (opens : OpensPublications reference)
    (follows : players owner = serviceReferenceTurnPolicy setup mode deadline leaks bound turns
      (firstTurnTiming setup turns mode) reference owner)
    (effective : ∀ count execution, count ≤ horizon →
      execution ∈ ((serviceApplication setup mode deadline leaks).roundsFrom
        (serviceInitialLaw setup mode) scheduler players count).support →
      PublicationsEffective setup execution.application.config)
    (count : Nat) (within : count ≤ horizon)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (supported : execution ∈ ((serviceApplication setup mode deadline leaks).roundsFrom
      (serviceInitialLaw setup mode) scheduler players count).support)
    (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (publication : ((serviceGraph setup mode).outputLayout event).IsPublication) :
    execution.application.WithinDeadline (serviceRuntime setup mode deadline) event := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
    players count within execution supported
  by_cases turned : ∃ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event
  · obtain ⟨entry, member, message, call⟩ := publicationsCalled_roundsFrom contract timely
      players owner reference opens follows effective count execution within supported event
      publication turned
    obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp member
    have once := (sourceServiceTurnPolicy_freshCalls_reference scheduler players owner
      (firstTurnTiming setup turns mode) reference follows count execution supported).2
    have sole := FreshCall.sole trace owner event once earlier entry later message split call
    have settled := settlesFreshCalls_history setup leaks contract.inclusion owner event owned
      trace earlier entry later message split call sole
    exact FreshCall.withinDeadline setup leaks owner event owned trace
      (ProtectedInclusion.at (serviceRuntime setup mode deadline) leaks contract.inclusion _ trace)
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
