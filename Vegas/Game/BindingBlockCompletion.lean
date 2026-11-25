module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceAsyncTimeliness
public import Vegas.Game.SourceServiceFirstTurnOpportunity
public import Vegas.Game.SourceServiceCanonicalAcceptance
public import Vegas.Game.SourceServiceCanonicalSlots
public import Vegas.Game.SourceServiceTurnSubmissions
public import Vegas.Game.SourceServiceFirstTurnMixture
public import Vegas.Game.NativeBindingRecord
public import Vegas.Game.NativeBindingTableSampling
public import Vegas.EventGraph.BarrierBlocks
public import Vegas.EventGraph.BindingPrefixObservation
public import Vegas.Pending.ReactiveGraphSteps
public import Vegas.Pending.CanonicalOutcomePublication

@[expose] public section

/-! # Exact native completion of a private binding block

A fixed submitted binding stays within its protected inclusion window. Fixed
binding clients therefore finish a private interval without defaults and recover
the complete sampled graph key, even when physical completions have another order.
The original raw anchor may come from a different reference profile. A selected
compiled subfamily can finish the interval after the remaining owners' records
are complete; its service facts are retained from that same original anchor.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

private def BindingCalled (setup : Setup (Player := Player) (L := L))
    {deps : setup.dataflowGraph.Dependencies}
    {duration : (serviceGraph setup deps).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (bound : (serviceGraph setup deps).EventId → Nat)
    (execution : (serviceApplication setup deps duration leaks).Execution) (owner : Player)
    (event : (serviceGraph setup deps).EventId) : Prop :=
  (∃ entry ∈ execution.logs owner,
    entry.beforeView.application.publicView.ownTurn? owner = some event) →
  ∃ entry ∈ execution.logs owner, ∃ message,
    FreshCall (serviceTimeouts setup deps duration) leaks owner event bound entry message

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

private theorem bindingCalled_round {event : (serviceGraph setup deps).EventId}
    (unique : (serviceGraph setup deps).OwnerSolitary event) {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
        (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (players : Player → (serviceApplication setup deps duration leaks).Policy) (owner : Player)
    {turns : Nat} (reference : (serviceGraph setup deps).BehavioralProfile)
    (payload : L.Ty)
    (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (result : PublicationResult (L.Val payload))
    (fixed : ∀ view active, reference owner event
      (EventCode.actor_eq_of_binding ((serviceGraph setup deps).nodes event) binding) view active =
      PMF.pure (cast (congrArg EventField.Action binding.symm) (some result)))
    (follows : players owner = turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) reference owner)
    (remaining : Nat)
    (execution next : (serviceApplication setup deps duration leaks).Execution)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution)
    (atTurn : OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks execution owner)
    (called : BindingCalled setup leaks bound execution owner event)
    (reached : next ∈ ((serviceApplication setup deps duration leaks).round scheduler players
      execution).support) :
    BindingCalled setup leaks bound next owner event := by
  let app := serviceApplication setup deps duration leaks
  have facts := legalFacts setup leaks horizon scheduler _ trace
  obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall execution middle command moved
  have calledMiddle : BindingCalled setup leaks bound middle owner event := by
    intro turned
    rw [recallEq] at turned
    obtain ⟨entry, member, message, call⟩ := called turned
    exact ⟨entry, by rw [recallEq]; exact member, message, call⟩
  rcases cases with ⟨_, rfl⟩ | ⟨who, active, response, chosen, rfl⟩
  · exact calledMiddle
  by_cases same : who = owner
  swap
  · have recallSame := app.respond_recall_other middle who owner (Ne.symm same) response
    intro turned
    rw [recallSame] at turned
    obtain ⟨entry, member, message, call⟩ := calledMiddle turned
    exact ⟨entry, by rw [recallSame]; exact member, message, call⟩
  subst who
  obtain ⟨emitted, recalled, _⟩ := respond_recall_self _ leaks middle owner response
  intro ⟨entry, member, turn⟩
  have old (prior : ∃ entry ∈ middle.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event) :
      ∃ entry ∈ (middle.respond app owner response).logs owner, ∃ message,
        FreshCall (serviceTimeouts setup deps duration) leaks owner event bound entry message := by
    obtain ⟨call, callMember, message, isCall⟩ := calledMiddle prior
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
  obtain ⟨middleTrace⟩ := app.raw_trace_environment (serviceInitialDistribution setup deps) horizon
    scheduler remaining execution middle (.activate owner) trace selected moved
  rw [active] at middleTrace
  let action := cast (congrArg EventField.Action binding.symm) (some result)
  have code : cast (congrArg (EventCode (serviceGraph setup deps).layout) binding)
      ((serviceGraph setup deps).nodes event) = .bind owner payload := by
    generalize cast (congrArg (EventCode (serviceGraph setup deps).layout) binding)
      ((serviceGraph setup deps).nodes event) = code
    cases code
    rfl
  have node := nodeView_eq_bind binding code
  have effective : EffectiveAction middle.application.config event action := by
    simp only [EffectiveAction, node]
  have loud : ¬ SilentAction event action := by
    simp only [SilentAction, node, action, cast_cast, cast_eq, reduceCtorEq, not_false_eq_true]
  have activeMiddle : owner ∉ middle.application.config.defaulted := by
    rw [appEq]
    exact activeBefore
  obtain ⟨material, submits⟩ := canonicalServiceDecision_transmits_of_effective
    (serviceTimeouts setup deps duration) _ middleTrace owner event turnNow action
      effective loud
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
  have opened : reference owner event owned
      ((serviceGraph setup deps).playerObserve owner middle.application.config) activeMiddle =
        PMF.pure action := fixed _ _
  simp only [id] at chosen
  rw [opened, PMF.pure_map, PMF.pure_bind, submits, ite_eq_right (by simp),
    PMF.mem_support_pure_iff] at chosen
  subst chosen
  have shape : (canonicalServiceDecision (serviceTimeouts setup deps duration)) leaks owner
      (middle.logs owner) (middle.observe app owner) event action =
        (⟨some material⟩ : app.Action) := by
    rw [← submits]
  have call := canonical_freshCall middleTrace bound owner event turnNow fitsMiddle
    action material submits
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


private theorem bindingCalled_runRounds {event : (serviceGraph setup deps).EventId}
    (unique : (serviceGraph setup deps).OwnerSolitary event) {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (players : Player → (serviceApplication setup deps duration leaks).Policy) (owner : Player)
    {turns : Nat} (reference : (serviceGraph setup deps).BehavioralProfile)
    (payload : L.Ty)
    (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (result : PublicationResult (L.Val payload))
    (fixed : ∀ view active, reference owner event
      (EventCode.actor_eq_of_binding ((serviceGraph setup deps).nodes event) binding) view active =
      PMF.pure (cast (congrArg EventField.Action binding.symm) (some result)))
    (follows : players owner = turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) reference owner) (remaining : Nat) :
    ∀ count (execution next : (serviceApplication setup deps duration leaks).Execution),
      ((serviceApplication setup deps duration leaks).protocol
        (serviceInitialDistribution setup deps) horizon scheduler).Trace
          (some ⟨remaining + count, none, execution⟩) →
      BindingCalled setup leaks bound execution owner event →
      OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks execution owner →
      ActivationsAnswered setup leaks execution →
      OwnFreshCalls setup leaks bound execution owner →
      OneCallPerEvent setup leaks execution owner →
      next ∈ ((serviceApplication setup deps duration leaks).runRounds scheduler players count
        execution).support →
      BindingCalled setup leaks bound next owner event ∧
        OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks next owner ∧
        ActivationsAnswered setup leaks next ∧
        OwnFreshCalls setup leaks bound next owner ∧
        OneCallPerEvent setup leaks next owner := by
  let app := serviceApplication setup deps duration leaks
  intro count
  induction count with
  | zero =>
      intro execution next _ called truthful answered calls once reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨called, truthful, answered, calls, once⟩
  | succ count ih =>
      intro execution next trace called truthful answered calls once reached
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have budget : remaining + (count + 1) = (remaining + count) + 1 := by omega
      rw [budget] at trace
      obtain ⟨middleTrace⟩ := app.raw_trace_round (serviceInitialDistribution setup deps) horizon
        scheduler
        players (remaining + count) execution middle trace moved
      have calledMiddle := bindingCalled_round unique contract timely players owner reference
        payload binding result fixed follows (remaining + count) execution middle trace answered
          truthful called moved
      have truthfulMiddle := EventGraphRuntime.round_ownSubmissionsAtTurn
        (serviceTimeouts setup deps duration) leaks
        (follows ▸ sourceServiceTurnPolicy_submitsAtTurn_reference setup leaks bound turns
          (firstTurnTiming setup turns deps) reference owner) truthful moved
      have answeredMiddle := round_activationsAnswered setup leaks answered moved
      have freshMiddle := round_freshCalls_reference (firstTurnTiming setup turns deps)
        reference follows calls once moved
      exact ih middle next middleTrace calledMiddle truthfulMiddle answeredMiddle freshMiddle.1
        freshMiddle.2 rest

/-- A fixed submitted binding stays within its deadline after an arbitrary initialized
boundary at which that event was untouched. Other native clients remain arbitrary. -/
theorem fixedBinding_withinDeadline_runRounds {horizon remaining count : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (players : Player → (serviceApplication setup deps duration leaks).Policy) (owner : Player)
    {turns : Nat} (reference : (serviceGraph setup deps).BehavioralProfile)
    (event : (serviceGraph setup deps).EventId)
    (unique : (serviceGraph setup deps).OwnerSolitary event)
    (payload : L.Ty)
    (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (result : PublicationResult (L.Val payload))
    (fixed : ∀ view active, reference owner event
      (EventCode.actor_eq_of_binding ((serviceGraph setup deps).nodes event) binding) view active =
      PMF.pure (cast (congrArg EventField.Action binding.symm) (some result)))
    (follows : players owner = turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) reference owner)
    (execution next : (serviceApplication setup deps duration leaks).Execution)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨remaining + count, none, execution⟩))
    (truthful : OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks execution owner)
    (answered : ActivationsAnswered setup leaks execution)
    (calls : OwnFreshCalls setup leaks bound execution owner)
    (once : OneCallPerEvent setup leaks execution owner)
    (untouched : Untouched setup leaks event execution)
    (reached : next ∈ ((serviceApplication setup deps duration leaks).runRounds scheduler players
      count execution).support)
    (ready : next.application.config.cut.Ready event) :
    next.application.WithinDeadline (serviceTimeouts setup deps duration) event := by
  let app := serviceApplication setup deps duration leaks
  have owned := EventCode.actor_eq_of_binding ((serviceGraph setup deps).nodes event) binding
  have initial : BindingCalled setup leaks bound execution owner event := by
    rintro ⟨entry, member, turn⟩
    exact (untouched owner entry member
      (entry.beforeView.application.publicView.ownTurn?_spec owner event turn).1).elim
  obtain ⟨calledNext, _truthfulNext, answeredNext, _callsNext, onceNext⟩ :=
    bindingCalled_runRounds unique contract timely players owner reference payload binding result
      fixed follows remaining count execution next trace initial truthful answered calls once
        reached
  obtain ⟨nextTrace⟩ := app.raw_trace_runRounds (serviceInitialDistribution setup deps) horizon
    scheduler
    players remaining count execution next trace reached
  by_cases turned : ∃ entry ∈ next.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner = some event
  · obtain ⟨entry, member, message, call⟩ := calledNext turned
    obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp member
    have sole := FreshCall.sole nextTrace owner event onceNext earlier entry later message split
      call
    have settled := settlesFreshCalls_history setup leaks contract.inclusion owner event unique
      owned nextTrace earlier entry later message split call sole
    exact FreshCall.withinDeadline setup leaks owner event owned nextTrace
      (ProtectedInclusion.at (serviceTimeouts setup deps duration) leaks contract.inclusion _
        nextTrace) earlier entry later message split call sole settled ready.1
  · have never : ∀ entry ∈ next.logs owner,
        entry.beforeView.application.publicView.ownTurn? owner ≠ some event :=
      fun entry present equal => turned ⟨entry, present, equal⟩
    have first := first_of_never next owner event
      (next.application.ownTurn?_of_ready unique ready owned) never
    exact (firstTurn_inclusionFits unique contract timely nextTrace answeredNext owned ready
      first).withinDeadline

private theorem bindingTail_rounds_path
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (count : Nat) (origin final : (serviceApplication setup deps duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup deps duration leaks).runRounds scheduler players
      count origin).support) :
    Relation.ReflTransGen Config.Step origin.application.config final.application.config := by
  induction count generalizing origin with
  | zero =>
    cases (PMF.mem_support_pure_iff _ _).mp reached
    exact .refl
  | succ count ih =>
    obtain ⟨middle, moved, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
    exact (reactive_round_graph_steps (serviceTimeouts setup deps duration) leaks scheduler players
      origin middle moved).trans (ih middle rest)

/-- Once all bindings outside the compiled subfamily have completed, live clients finish the
remaining private interval without a default. Every deadline is justified from
the original block anchor, rather than from a newly initialized frozen profile. -/
theorem fixedBinding_block_endpoint
    {horizon budget used turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (serial : (serviceGraph setup deps).ActorSerial)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (reference : (serviceGraph setup deps).BehavioralProfile) (compiled : Player → Prop)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (follows : ∀ owner, compiled owner → players owner =
      turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference owner)
    (anchor : (serviceApplication setup deps duration leaks).Execution)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨budget, none, anchor⟩))
    (truthful : ∀ owner, compiled owner → OwnSubmissionsAtTurn
      (serviceTimeouts setup deps duration) leaks anchor owner)
    (answered : ActivationsAnswered setup leaks anchor)
    (calls : ∀ owner, compiled owner → OwnFreshCalls setup leaks bound anchor owner)
    (once : ∀ owner, compiled owner → OneCallPerEvent setup leaks anchor owner)
    (start finish : Nat) (shaped : BlockShaped (graph := serviceGraph setup deps) start finish)
    (bounded : finish ≤ (serviceGraph setup deps).order.eventCount)
    (bindings : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish →
      ∃ owner payload, (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (fixed : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish → ∀ owner,
      (owned : (serviceGraph setup deps).actor? event = some owner) → compiled owner →
      ∃ (payload : L.Ty)
        (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
        (result : PublicationResult (L.Val payload)),
        ∀ view active, reference owner event owned view active =
          PMF.pure (cast (congrArg EventField.Action binding.symm) (some result)))
    (untouched : ∀ owner, compiled owner → ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish →
      (serviceGraph setup deps).actor? event = some owner → Untouched setup leaks event anchor)
    (current : (serviceApplication setup deps duration leaks).Execution)
    (counted : used ≤ budget)
    (supported : current ∈ ((serviceApplication setup deps duration leaks).runRounds scheduler
      players used anchor).support)
    (clear : current.application.config.defaulted = ∅)
    (inside : InBlock start finish current.application.config)
    (completed : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish → ∀ owner,
      (serviceGraph setup deps).actor? event = some owner → ¬ compiled owner →
        event ∈ current.application.config.cut.completed)
    (final : (serviceApplication setup deps duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup deps duration leaks).runUntil scheduler players
      (fun next => BlockDone finish next.application.config) (budget - used) current).support) :
    final.application.config.defaulted = ∅ ∧
      final.application.config.cut.IsPrefix finish ∧
      ∃ extra, used + extra ≤ budget ∧
        final ∈ ((serviceApplication setup deps duration leaks).runRounds scheduler players
          (used + extra) anchor).support := by
  classical
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  let stop := fun next : app.Execution => BlockDone finish next.application.config
  let holds := fun (remaining : Nat) (next : app.Execution) =>
    ∃ extra, used + extra + remaining = budget ∧
      next ∈ (app.runRounds scheduler players (used + extra) anchor).support ∧
      next.application.config.defaulted = ∅ ∧ next.application.config.cut.Within start finish ∧
      ∀ event : G.EventId, start ≤ event.val → event.val < finish → ∀ owner,
        G.actor? event = some owner → ¬ compiled owner →
          event ∈ next.application.config.cut.completed
  have preserved : ∀ remaining next, holds (remaining + 1) next → ¬ stop next →
      ∀ later ∈ (app.round scheduler players next).support, holds remaining later := by
    intro remaining next valid running later moved
    obtain ⟨extra, accounted, supportedNext, clearNext, within, alreadyDone⟩ := valid
    have insideNext : InBlock start finish next.application.config :=
      ⟨within.1, fun event late done => Nat.not_lt.mpr late (within.2 event done)⟩
    have readyBounds (event : G.EventId) (ready : next.application.config.cut.Ready event) :
        start ≤ event.val ∧ event.val < finish := shaped _ insideNext running event ready
    have currentBindings (event : G.EventId) (ready : next.application.config.cut.Ready event) :
        ∃ owner payload, G.outputLayout event = .binding owner payload :=
      bindings event (readyBounds event ready).1 (readyBounds event ready).2
    have deadlines (event : G.EventId) (ready : next.application.config.cut.Ready event) :
        next.application.WithinDeadline (serviceTimeouts setup deps duration) event := by
      obtain ⟨owner, _payload, binding⟩ := currentBindings event ready
      have actor := EventCode.actor_eq_of_binding (G.nodes event) binding
      have ownerCompiled : compiled owner := by
        by_contra outside
        exact ready.1 (alreadyDone event (readyBounds event ready).1
          (readyBounds event ready).2 owner actor outside)
      obtain ⟨payload, binding, result, constant⟩ := fixed event
        (readyBounds event ready).1 (readyBounds event ready).2 owner actor ownerCompiled
      have traceBudget : (app.protocol (serviceInitialDistribution setup deps) horizon
        scheduler).Trace
          (some ⟨(remaining + 1) + (used + extra), none, anchor⟩) := by
        simpa only [show (remaining + 1) + (used + extra) = budget by omega] using trace
      exact fixedBinding_withinDeadline_runRounds contract timely players owner reference event
        (serial event) payload binding result constant (follows owner ownerCompiled)
        anchor next traceBudget (truthful owner ownerCompiled) answered (calls owner ownerCompiled)
        (once owner ownerCompiled)
        (untouched owner ownerCompiled event (readyBounds event ready).1
          (readyBounds event ready).2 actor) supportedNext ready
    obtain ⟨clearLater, primary⟩ := reactive_round_bindings_clear
      (serviceTimeouts setup deps duration) leaks scheduler players next later clearNext
      currentBindings deadlines moved
    refine ⟨extra + 1, by omega, ?_, clearLater, ?_, ?_⟩
    · rw [show used + (extra + 1) = (used + extra) + 1 by omega,
        app.runRounds_add scheduler players (used + extra) 1 anchor, PMF.mem_support_bind_iff]
      exact ⟨next, supportedNext, by
        simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using moved⟩
    · rcases primary with same | ⟨event, ready, action, selected⟩
      · rw [same]
        exact within
      · rw [next.application.config.step_cut event ready action later.application.config selected]
        exact within.complete event ready (readyBounds event ready).2
    · intro event lower upper owner owned outside
      exact Config.Step.path_completed_mono
        (reactive_round_graph_steps (serviceTimeouts setup deps duration) leaks scheduler players
          next later moved) (alreadyDone event lower upper owner owned outside)
  have initial : holds (budget - used) current :=
    ⟨0, by omega, by simpa only [Nat.add_zero] using supported, clear,
      ⟨inside.1, fun event done => Nat.lt_of_not_ge (fun late => inside.2 event late done)⟩,
      completed⟩
  obtain ⟨remaining, extra, accounted, supportedFinal, clearFinal, withinFinal, _alreadyDone⟩ :=
    app.runUntil_support_holds scheduler players stop holds preserved (budget - used) current
      initial final reached
  have done : BlockDone finish final.application.config := by
    rcases app.runUntil_stopped scheduler players stop (budget - used) current final reached with
      finished | spent
    · exact finished
    have currentLength := app.runRounds_environmentRecall_length scheduler players used anchor
      current supported
    have finalLength := app.runRounds_environmentRecall_length scheduler players (used + extra)
      anchor final supportedFinal
    have exhausted : used + extra = budget := by omega
    obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (serviceInitialDistribution setup deps) horizon
      scheduler
      players 0 (used + extra) anchor final
      (by simpa only [Nat.zero_add, exhausted] using trace) supportedFinal
    have terminal := contract.completes ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
    intro event _
    rw [terminal]
    exact Finset.mem_univ event
  exact ⟨clearFinal, withinFinal.isPrefix bounded done, extra, by omega, supportedFinal⟩

/-- Completing a selected compiled subfamily recovers the exact source table, retaining
all other records that were already accepted before the tail started. -/
theorem fixedBinding_block_key
    {horizon budget used turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (serial : (serviceGraph setup deps).ActorSerial)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (reference : (serviceGraph setup deps).BehavioralProfile) (compiled : Player → Prop)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (follows : ∀ owner, compiled owner → players owner =
      turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference owner)
    (anchor : (serviceApplication setup deps duration leaks).Execution)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨budget, none, anchor⟩))
    (truthful : ∀ owner, compiled owner → OwnSubmissionsAtTurn
      (serviceTimeouts setup deps duration) leaks anchor owner)
    (answered : ActivationsAnswered setup leaks anchor)
    (calls : ∀ owner, compiled owner → OwnFreshCalls setup leaks bound anchor owner)
    (once : ∀ owner, compiled owner → OneCallPerEvent setup leaks anchor owner)
    (start finish : Nat) (shaped : BlockShaped (graph := serviceGraph setup deps) start finish)
    (ordered : anchor.application.config.cut.IsPrefix start)
    (bindings : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish →
      ∃ owner payload, (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (ghost : (serviceGraph setup deps).Config)
    {inputs : (serviceGraph setup deps).Inputs}
    (anchorReach : anchor.application.config.Reachable inputs)
    (ghostPath : Relation.ReflTransGen Config.Step anchor.application.config ghost)
    (ghostOrdered : ghost.cut.IsPrefix finish)
    (fixed : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish → ∀ owner,
      (owned : (serviceGraph setup deps).actor? event = some owner) → compiled owner →
      ∃ (payload : L.Ty)
        (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
        (result : PublicationResult (L.Val payload)),
        (∀ view active, reference owner event owned view active =
          PMF.pure (cast (congrArg EventField.Action binding.symm) (some result))) ∧
        completionOf ghost event = some (EventGraph.completion (serviceGraph setup deps) event
          (some (cast (congrArg EventField.Action binding.symm) (some result)))
          (cast (congrArg EventField.Value binding.symm) result)))
    (untouched : ∀ owner, compiled owner → ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish →
      (serviceGraph setup deps).actor? event = some owner → Untouched setup leaks event anchor)
    (current : (serviceApplication setup deps duration leaks).Execution)
    (counted : used ≤ budget)
    (supported : current ∈ ((serviceApplication setup deps duration leaks).runRounds scheduler
      players used anchor).support)
    (clear : current.application.config.defaulted = ∅)
    (inside : InBlock start finish current.application.config)
    (completed : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish → ∀ owner,
      (serviceGraph setup deps).actor? event = some owner → ¬ compiled owner →
        event ∈ current.application.config.cut.completed)
    (matched : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish → ∀ owner,
      (serviceGraph setup deps).actor? event = some owner → ¬ compiled owner →
        completionOf current.application.config event = completionOf ghost event)
    (final : (serviceApplication setup deps duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup deps duration leaks).runUntil scheduler players
      (fun next => BlockDone finish next.application.config) (budget - used) current).support) :
    final.application.config.defaulted = ∅ ∧ final.application.config.cut.IsPrefix finish ∧
      runKey final.application.config = runKey ghost ∧
      ∃ extra, used + extra ≤ budget ∧
        final ∈ ((serviceApplication setup deps duration leaks).runRounds scheduler players
          (used + extra) anchor).support := by
  classical
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  have constant : ∀ event : G.EventId, start ≤ event.val → event.val < finish → ∀ owner,
      (owned : G.actor? event = some owner) → compiled owner →
      ∃ (payload : L.Ty) (binding : G.outputLayout event = .binding owner payload)
        (result : PublicationResult (L.Val payload)),
        ∀ view active, reference owner event owned view active =
          PMF.pure (cast (congrArg EventField.Action binding.symm) (some result)) := by
    intro event lower upper owner owned selected
    obtain ⟨payload, binding, result, fixed, _⟩ := fixed event lower upper owner owned selected
    exact ⟨payload, binding, result, fixed⟩
  obtain ⟨finalClear, finalOrdered, extra, enough, finalSupport⟩ := fixedBinding_block_endpoint
    scheduler bound serial contract timely reference compiled players follows anchor trace truthful
    answered calls once start finish shaped ghostOrdered.1 bindings constant untouched current
    counted supported clear inside completed final reached
  have actualPath := bindingTail_rounds_path scheduler players (used + extra) anchor final
    finalSupport
  have tailPath := reactive_runUntil_graph_steps (serviceTimeouts setup deps duration) leaks
    scheduler players (fun next => BlockDone finish next.application.config) (budget - used)
    current final reached
  have records : completionOf final.application.config = completionOf ghost := by
    funext event
    by_cases early : event.val < start
    · have done := (ordered.2 event).mpr early
      obtain ⟨record, found⟩ := Option.isSome_iff_exists.mp
        ((completionOf_isSome_iff anchor.application.config event).mpr done)
      rw [Config.Step.path_completionOf_of_some actualPath event record found,
        Config.Step.path_completionOf_of_some ghostPath event record found]
    by_cases upper : event.val < finish
    · obtain ⟨owner, _payload, binding⟩ := bindings event (by omega) upper
      have actor := EventCode.actor_eq_of_binding (G.nodes event) binding
      by_cases selected : compiled owner
      · obtain ⟨payload, binding, result, constant, expected⟩ :=
          fixed event (by omega) upper owner actor selected
        have unfinished : event ∉ anchor.application.config.cut.completed :=
          fun done => early ((ordered.2 event).mp done)
        have done : event ∈ final.application.config.cut.completed :=
          (finalOrdered.2 event).mpr upper
        rcases fixed_reference_binding_record_runRounds leaks scheduler bound turns reference owner
            event actor payload binding result constant players (follows owner selected) anchor
            trace (truthful owner selected)
            (untouched owner selected event (by omega) upper actor) unfinished
            (used + extra) final finalSupport done with defaulted | ⟨actual, _⟩
        · simp only [finalClear, Finset.notMem_empty] at defaulted
        · exact actual.trans expected.symm
      · obtain ⟨record, found⟩ := Option.isSome_iff_exists.mp
          ((completionOf_isSome_iff current.application.config event).mpr
            (completed event (by omega) upper owner actor selected))
        exact (Config.Step.path_completionOf_of_some tailPath event record found).trans
          (found.symm.trans (matched event (by omega) upper owner actor selected))
    · rw [(completionOf_eq_none_iff final.application.config event).mpr
        (fun done => upper ((finalOrdered.2 event).mp done)),
        (completionOf_eq_none_iff ghost event).mpr
          (fun done => upper ((ghostOrdered.2 event).mp done))]
  have stores := store_eq_of_binding_paths anchor.application.config final.application.config
    ghost start finish anchorReach ordered actualPath ghostPath finalOrdered ghostOrdered bindings
    records
  have cuts : final.application.config.cut = ghost.cut := by
    apply EventOrder.Cut.ext
    ext event
    exact (finalOrdered.2 event).trans (ghostOrdered.2 event).symm
  refine ⟨finalClear, finalOrdered, ?_, extra, enough, finalSupport⟩
  change (final.application.config.cut, final.application.config.store,
    completionOf final.application.config) = (ghost.cut, ghost.store, completionOf ghost)
  rw [cuts, stores, records]

/-- Honest source-prefix clients have the exact canonical graph key law across a
private binding block, including the complete sampled joint binding table. -/
theorem native_binding_block_key_distribution
    {horizon budget turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile : (serviceGraph setup deps).BehavioralProfile)
    (submits : (serviceGraph setup deps).SubmitsBindings profile)
    (origin : (serviceApplication setup deps duration leaks).Execution)
    {inputs : (serviceGraph setup deps).Inputs}
    (initialReach : origin.application.config.Reachable inputs)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨budget, none, origin⟩))
    (truthful : ∀ owner, OwnSubmissionsAtTurn
      (serviceTimeouts setup deps duration) leaks origin owner)
    (answered : ActivationsAnswered setup leaks origin)
    (calls : ∀ owner, OwnFreshCalls setup leaks bound origin owner)
    (once : ∀ owner, OneCallPerEvent setup leaks origin owner)
    (start count : Nat)
    (bounded : start + count ≤ (serviceGraph setup deps).order.eventCount)
    (ordered : origin.application.config.cut.IsPrefix start)
    (clear : origin.application.config.defaulted = ∅)
    (bindings : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < start + count →
      ∃ owner payload, (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (barrier : ∀ event : (serviceGraph setup deps).EventId, event.val = start + count →
      ((serviceGraph setup deps).outputLayout event).IsPublic)
    (untouched : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < start + count → Untouched setup leaks event origin) :
    let G := serviceGraph setup deps
    let app := serviceApplication setup deps duration leaks
    let reference := G.prefixProfile profile
    (app.runUntil scheduler
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference)
      (fun current => BlockDone (start + count) current.application.config) budget origin).map
        (fun final => runKey final.application.config) =
      (G.runPlan (G.policyPlan reference G.canonicalScheduler) count
        origin.application.config).map runKey := by
  classical
  intro G app reference
  let finish := start + count
  let stop := fun current : app.Execution => BlockDone finish current.application.config
  let clients := fun reference => turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
    (firstTurnTiming setup turns deps) reference
  let source := G.runPlan (G.policyPlan reference G.canonicalScheduler) count
    origin.application.config
  let member := fun ghost => app.runUntil scheduler
    (clients (G.prefixProfile (G.freezeBindingsBefore profile start finish ghost))) stop budget
      origin
  have referenceSubmits : G.SubmitsBindings reference := by
    intro who event actor observation active action selected
    exact submits who event actor _ _ action selected
  have mixed := native_binding_subfamily_mixture
    (horizon := horizon) (nativeCount := budget) (remaining := 0) (turns := turns)
    scheduler bound relaxed profile submits (fun _ => True) (fun _ => app.silentPolicy) stop origin
    initialReach start count ordered clear bounded bindings (fun owner _ => truthful owner)
    (fun _ _ event lower upper _ => untouched event lower upper)
    (by simpa only [Nat.zero_add] using trace)
  simp only [ite_true] at mixed
  change app.runUntil scheduler (clients reference) stop budget origin = source.bind member at mixed
  have fixedMember (ghost : G.Config) (sampled : ghost ∈ source.support) :
      (member ghost).map (fun final => runKey final.application.config) =
        PMF.pure (runKey ghost) := by
    obtain ⟨ghostOrdered, ghostPath, _ghostClear, _ghostClean, records⟩ :=
      runPlan_submitted_binding_frame reference count start origin.application.config ordered
        clear bounded
        (fun event _ _ owner actor observation active action member =>
          referenceSubmits owner event actor observation active action member)
        bindings ghost sampled
    have fixed : ∀ event : G.EventId, start ≤ event.val → event.val < finish →
        ∃ (owner : Player) (payload : L.Ty)
          (binding : G.outputLayout event = .binding owner payload)
          (result : PublicationResult (L.Val payload)),
          (∀ view active,
            G.prefixProfile (G.freezeBindingsBefore profile start finish ghost) owner event
              (EventCode.actor_eq_of_binding (G.nodes event) binding) view active =
              PMF.pure (cast (congrArg EventField.Action binding.symm) (some result))) ∧
          completionOf ghost event = some (EventGraph.completion G event
            (some (cast (congrArg EventField.Action binding.symm) (some result)))
            (cast (congrArg EventField.Value binding.symm) result)) := by
      intro event lower upper
      obtain ⟨owner, payload, binding, result, record, output⟩ := records event lower upper
      refine ⟨owner, payload, binding, result, ?_, record⟩
      intro view active
      change G.freezeBindingsBefore profile start finish ghost owner event _ _ _ = _
      apply freezeBindingsBefore_binding profile start finish ghost owner event _ _ _
        ⟨lower, upper⟩ binding result
      have castSome {α β : Type} (same : α = β) (item : α) :
          cast (congrArg Option same) (some item) = some (cast same item) := by
        cases same
        rfl
      rw [output]
      change cast (congrArg Option (congrArg EventField.Value binding))
        (some (cast (congrArg EventField.Value binding.symm) result)) = some result
      rw [castSome (congrArg EventField.Value binding)
        (cast (congrArg EventField.Value binding.symm) result)]
      simp only [cast_cast, cast_eq]
    let frozen := G.prefixProfile (G.freezeBindingsBefore profile start finish ghost)
    have fixedOwned : ∀ event : G.EventId, start ≤ event.val → event.val < finish → ∀ owner,
        (owned : G.actor? event = some owner) → True →
        ∃ (payload : L.Ty) (binding : G.outputLayout event = .binding owner payload)
          (result : PublicationResult (L.Val payload)),
          (∀ view active, frozen owner event owned view active =
            PMF.pure (cast (congrArg EventField.Action binding.symm) (some result))) ∧
          completionOf ghost event = some (EventGraph.completion G event
            (some (cast (congrArg EventField.Action binding.symm) (some result)))
            (cast (congrArg EventField.Value binding.symm) result)) := by
      intro event lower upper owner owned _
      obtain ⟨actor, payload, binding, result, constant, record⟩ := fixed event lower upper
      have equal : actor = owner := Option.some.inj
        ((EventCode.actor_eq_of_binding (G.nodes event) binding).symm.trans owned)
      subst actor
      exact ⟨payload, binding, result, constant, record⟩
    have initialInside : InBlock start finish origin.application.config := by
      have within := ordered.within (show start ≤ finish by dsimp only [finish]; omega)
      exact ⟨within.1, fun event late done => Nat.not_lt.mpr late (within.2 event done)⟩
    have exactKey (final : app.Execution) (selected : final ∈ (member ghost).support) :
        runKey final.application.config = runKey ghost := by
      have result := fixedBinding_block_key (used := 0) scheduler bound relaxed.actorSerial
        contract timely frozen (fun _ => True) (clients frozen) (fun _ _ => rfl) origin trace
        (fun owner _ => truthful owner) answered (fun owner _ => calls owner)
        (fun owner _ => once owner) start finish
        (bindingInterval_shaped relaxed start finish bindings barrier) ordered bindings ghost
        initialReach ghostPath ghostOrdered fixedOwned
        (fun _ _ event lower upper _ => untouched event lower upper) origin (Nat.zero_le _)
        (by simp only [ReactiveApplication.runRounds, PMF.mem_support_pure_iff]) clear initialInside
        (fun _ _ _ _ _ outside => (outside trivial).elim)
        (fun _ _ _ _ _ outside => (outside trivial).elim) final selected
      exact result.2.2.1
    calc
      _ = (member ghost).map (fun _ => runKey ghost) := map_congr_on_support _ exactKey
      _ = _ := pmf_map_fun_const _ _
  calc
    _ = (source.bind member).map (fun final => runKey final.application.config) :=
      congrArg (PMF.map fun final => runKey final.application.config) mixed
    _ = source.bind (fun ghost => (member ghost).map (fun final =>
        runKey final.application.config)) := PMF.map_bind _ _ _
    _ = source.bind (fun ghost => PMF.pure (runKey ghost)) :=
      bind_congr_on_support _ fixedMember
    _ = _ := PMF.bind_pure_comp _ _

/-- A private binding block preserves the canonical terminal continuation law. -/
theorem native_binding_block_outcomeDistribution
    {horizon budget turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile : (serviceGraph setup deps).BehavioralProfile)
    (submits : (serviceGraph setup deps).SubmitsBindings profile)
    (independent : ReadyIndependent ((serviceGraph setup deps).prefixProfile profile))
    {Outcome : Type*} (read : (serviceGraph setup deps).Config → Outcome)
    (keyed : ∀ left right : (serviceGraph setup deps).Config,
      runKey left = runKey right → read left = read right)
    (origin : (serviceApplication setup deps duration leaks).Execution)
    {inputs : (serviceGraph setup deps).Inputs}
    (initialReach : origin.application.config.Reachable inputs)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨budget, none, origin⟩))
    (truthful : ∀ owner, OwnSubmissionsAtTurn
      (serviceTimeouts setup deps duration) leaks origin owner)
    (answered : ActivationsAnswered setup leaks origin)
    (calls : ∀ owner, OwnFreshCalls setup leaks bound origin owner)
    (once : ∀ owner, OneCallPerEvent setup leaks origin owner)
    (start count : Nat)
    (bounded : start + count ≤ (serviceGraph setup deps).order.eventCount)
    (ordered : origin.application.config.cut.IsPrefix start)
    (clear : origin.application.config.defaulted = ∅)
    (bindings : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < start + count →
      ∃ owner payload, (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (barrier : ∀ event : (serviceGraph setup deps).EventId, event.val = start + count →
      ((serviceGraph setup deps).outputLayout event).IsPublic)
    (untouched : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < start + count → Untouched setup leaks event origin) :
    let G := serviceGraph setup deps
    let app := serviceApplication setup deps duration leaks
    let reference := G.prefixProfile profile
    (app.runUntil scheduler
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference)
      (fun current => BlockDone (start + count) current.application.config) budget origin).bind
        (fun final => outcomeDistribution reference read final.application.config) =
      outcomeDistribution reference read origin.application.config := by
  classical
  intro G app reference
  let law := app.runUntil scheduler
    (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) reference)
    (fun current => BlockDone (start + count) current.application.config) budget origin
  let source := G.runPlan (G.policyPlan reference G.canonicalScheduler) count
    origin.application.config
  have keyLaw := native_binding_block_key_distribution (turns := turns) scheduler bound relaxed
    contract
    timely profile submits origin initialReach trace truthful answered calls once start count
    bounded ordered clear bindings barrier untouched
  change law.map (fun final => runKey final.application.config) = source.map runKey at keyLaw
  have congruent (left right : G.Config) (same : runKey left = runKey right) :
      outcomeDistribution reference read left = outcomeDistribution reference read right :=
    outcomeDistribution_eq_of_canonicalDistribution_eq read keyed
      (independent.canonicalDistribution_congr left.remaining left right rfl same)
  let through := fun key =>
    if found : ∃ config : G.Config, runKey config = key then
      outcomeDistribution reference read found.choose
    else outcomeDistribution reference read origin.application.config
  have factor (config : G.Config) : through (runKey config) = outcomeDistribution reference read
    config := by
    have found : ∃ other : G.Config, runKey other = runKey config := ⟨config, rfl⟩
    simp only [through, dite_eq_left found]
    exact congruent _ _ found.choose_spec
  calc
    _ = (law.map (fun final => runKey final.application.config)).bind through := by
      rw [PMF.bind_map]
      exact bind_congr_on_support _ (fun final _ => (factor _).symm)
    _ = (source.map runKey).bind through := congrArg (fun law => law.bind through) keyLaw
    _ = source.bind (outcomeDistribution reference read) := by
      rw [PMF.bind_map]
      exact bind_congr_on_support _ (fun config _ => factor config)
    _ = _ := runPlan_bind_outcomeDistribution reference read count origin.application.config

/-- Fixed foreign bindings remain clear up to an arbitrary block-bounded stop
whenever the focal owner remains active at that stop. -/
theorem fixedBinding_runUntil_clear_of_active
    {horizon budget used turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (serial : (serviceGraph setup deps).ActorSerial)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (reference : (serviceGraph setup deps).BehavioralProfile) (focal : Player)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (follows : ∀ owner, owner ≠ focal → players owner =
      turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference owner)
    (anchor : (serviceApplication setup deps duration leaks).Execution)
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
        (some ⟨budget, none, anchor⟩))
    (truthful : ∀ owner, owner ≠ focal → OwnSubmissionsAtTurn
      (serviceTimeouts setup deps duration) leaks anchor owner)
    (answered : ActivationsAnswered setup leaks anchor)
    (calls : ∀ owner, owner ≠ focal → OwnFreshCalls setup leaks bound anchor owner)
    (once : ∀ owner, owner ≠ focal → OneCallPerEvent setup leaks anchor owner)
    (start finish : Nat) (shaped : BlockShaped (graph := serviceGraph setup deps) start finish)
    (bindings : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish →
      ∃ owner payload, (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (fixed : ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish → ∀ owner,
      (owned : (serviceGraph setup deps).actor? event = some owner) → owner ≠ focal →
      ∃ (payload : L.Ty)
        (binding : (serviceGraph setup deps).outputLayout event = .binding owner payload)
        (result : PublicationResult (L.Val payload)),
        ∀ view active, reference owner event owned view active =
          PMF.pure (cast (congrArg EventField.Action binding.symm) (some result)))
    (untouched : ∀ owner, owner ≠ focal → ∀ event : (serviceGraph setup deps).EventId,
      start ≤ event.val → event.val < finish →
      (serviceGraph setup deps).actor? event = some owner → Untouched setup leaks event anchor)
    (current : (serviceApplication setup deps duration leaks).Execution)
    (counted : used ≤ budget)
    (supported : current ∈ ((serviceApplication setup deps duration leaks).runRounds scheduler
      players used anchor).support)
    (clear : current.application.config.defaulted = ∅)
    (inside : InBlock start finish current.application.config)
    (stop : (serviceApplication setup deps duration leaks).Execution → Prop)
    [DecidablePred stop]
    (completedStops : ∀ next, BlockDone finish next.application.config → stop next)
    (final : (serviceApplication setup deps duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup deps duration leaks).runUntil scheduler players
      stop (budget - used) current).support)
    (active : focal ∉ final.application.config.defaulted) :
    final.application.config.defaulted = ∅ ∧
      final.application.config.cut.Within start finish ∧ stop final ∧
      ∃ extra, used + extra ≤ budget ∧
        final ∈ ((serviceApplication setup deps duration leaks).runRounds scheduler players
          (used + extra) anchor).support := by
  classical
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  let holds := fun (remaining : Nat) (next : app.Execution) =>
    ∃ extra, used + extra + remaining = budget ∧
      next ∈ (app.runRounds scheduler players (used + extra) anchor).support ∧
      (focal ∈ next.application.config.defaulted ∨
        (next.application.config.defaulted = ∅ ∧
          next.application.config.cut.Within start finish))
  have preserved : ∀ remaining next, holds (remaining + 1) next → ¬ stop next →
      ∀ later ∈ (app.round scheduler players next).support, holds remaining later := by
    intro remaining next valid running later moved
    obtain ⟨extra, accounted, supportedNext, safe⟩ := valid
    have supportedLater : later ∈
        (app.runRounds scheduler players (used + (extra + 1)) anchor).support := by
      rw [show used + (extra + 1) = (used + extra) + 1 by omega,
        app.runRounds_add scheduler players (used + extra) 1 anchor, PMF.mem_support_bind_iff]
      exact ⟨next, supportedNext, by
        simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using moved⟩
    refine ⟨extra + 1, by omega, supportedLater, ?_⟩
    rcases safe with failed | ⟨clearNext, within⟩
    · exact Or.inl (Config.Step.path_defaulted_mono
        (reactive_round_graph_steps (serviceTimeouts setup deps duration) leaks scheduler players
          next later moved) failed)
    · have unfinished : ¬ BlockDone finish next.application.config :=
        fun done => running (completedStops next done)
      have insideNext : InBlock start finish next.application.config :=
        ⟨within.1, fun event late done => Nat.not_lt.mpr late (within.2 event done)⟩
      have readyBounds (event : G.EventId) (ready : next.application.config.cut.Ready event) :
          start ≤ event.val ∧ event.val < finish := shaped _ insideNext unfinished event ready
      have currentBindings (event : G.EventId) (ready : next.application.config.cut.Ready event) :
          ∃ owner payload, G.outputLayout event = .binding owner payload :=
        bindings event (readyBounds event ready).1 (readyBounds event ready).2
      have deadlines (event : G.EventId) (owner : Player)
          (ready : next.application.config.cut.Ready event) (owned : G.actor? event = some owner)
          (foreign : owner ≠ focal) :
          next.application.WithinDeadline (serviceTimeouts setup deps duration) event := by
        obtain ⟨payload, binding, result, constant⟩ := fixed event
          (readyBounds event ready).1 (readyBounds event ready).2 owner owned foreign
        have traceBudget : (app.protocol (serviceInitialDistribution setup deps) horizon
          scheduler).Trace
            (some ⟨(remaining + 1) + (used + extra), none, anchor⟩) := by
          simpa only [show (remaining + 1) + (used + extra) = budget by omega] using trace
        exact fixedBinding_withinDeadline_runRounds contract timely players owner reference event
          (serial event) payload binding result constant (follows owner foreign) anchor next
          traceBudget (truthful owner foreign) answered (calls owner foreign) (once owner foreign)
          (untouched owner foreign event (readyBounds event ready).1
            (readyBounds event ready).2 owned) supportedNext ready
      rcases reactive_round_bindings_clear_or_focal_default
          (serviceTimeouts setup deps duration) leaks scheduler players next later focal
          clearNext currentBindings deadlines moved with failed | ⟨clearLater, primary⟩
      · exact Or.inl failed
      · right
        refine ⟨clearLater, ?_⟩
        rcases primary with same | ⟨event, ready, action, selected⟩
        · rw [same]
          exact within
        · rw [next.application.config.step_cut event ready action later.application.config selected]
          exact within.complete event ready (readyBounds event ready).2
  have initial : holds (budget - used) current :=
    ⟨0, by omega, by simpa only [Nat.add_zero] using supported, Or.inr ⟨clear,
      ⟨inside.1, fun event done => Nat.lt_of_not_ge (fun late => inside.2 event late done)⟩⟩⟩
  obtain ⟨remaining, extra, accounted, supportedFinal, safeFinal⟩ :=
    app.runUntil_support_holds scheduler players stop holds preserved (budget - used) current
      initial final reached
  obtain ⟨clearFinal, withinFinal⟩ := safeFinal.resolve_left active
  have done : stop final := by
    rcases app.runUntil_stopped scheduler players stop (budget - used) current final reached with
      finished | spent
    · exact finished
    have currentLength := app.runRounds_environmentRecall_length scheduler players used anchor
      current supported
    have finalLength := app.runRounds_environmentRecall_length scheduler players (used + extra)
      anchor final supportedFinal
    have exhausted : used + extra = budget := by omega
    obtain ⟨finalTrace⟩ := app.raw_trace_runRounds (serviceInitialDistribution setup deps) horizon
      scheduler
      players 0 (used + extra) anchor final
      (by simpa only [Nat.zero_add, exhausted] using trace) supportedFinal
    have terminal := contract.completes ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
    apply completedStops final
    intro event _
    rw [terminal]
    exact Finset.mem_univ event
  exact ⟨clearFinal, withinFinal, done, extra, by omega, supportedFinal⟩

end Vegas
