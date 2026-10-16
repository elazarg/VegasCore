/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServiceRawOrigin

/-! # Good foreign phase trajectories from original RAW labels -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode

section GoodPhase

variable
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (phaseApplication runtime leaks).PlayerEntry → (phaseApplication runtime
      leaks).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent (serviceGraph setup mode) → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
  (horizon : Nat) (tapes : PhaseSeedAddress (serviceGraph setup mode) → Fin horizon → Bool × Bool)
  (plan : RuntimePhasePlan (serviceGraph setup mode)) (ordered : (serviceGraph setup
      mode).RevealRelaxedOrdered)
  (inputs : PMF (serviceGraph setup mode).Inputs)
  {LocalSeed RestSeed : Type}
  (seedLaw : PMF (RestSeed × (PhaseSeedAddress (serviceGraph setup mode) → LocalSeed)))
  (family : (RestSeed × (PhaseSeedAddress (serviceGraph setup mode) → LocalSeed)) →
      (phaseApplication runtime leaks).Scheduler)
  (calendar : PhaseService.PrivateActivationCalendar runtime leaks bounds plan inputs horizon
    seedLaw family)
  (privateSuccess : PhaseService.PrivateBindingSuccess runtime leaks bounds plan inputs horizon
    seedLaw family)
  (capacity : horizon ≤ bounds.candidateCount)
  (catalogue : ∀ owner event payload (_binding : (serviceGraph setup mode).outputLayout event =
      .binding owner payload),
    ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)

local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "Q" => phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes



/-- No effective RAW label is read at an actual unsent foreign callback of
this original commitment attempt. Sent and inert callbacks are omitted. -/
def phaseCountServiceRawFree
    (scheduler : (app).Scheduler) (start : (app).Control) (phase : RuntimePhase graph)
    (focal : Player) (final : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some final)) : Prop :=
  ∀ owner, owner ≠ focal → owner ∉ start.execution.application.current.excluded →
    ∀ event ∈ phase.events, ∀ bounded,
    ∀ (before : (app).Control)
      (prior : ((menu).protocol initial horizon scheduler).Trace (some before)),
      TracePrefix prior trace → ∀ active : before.actor = some owner,
      before.execution.application.SeedRequest owner
        ⟨start.execution.application.attempt, event⟩ →
      (∀ packet ∈ (app).outputs (before.execution.recall owner),
        PhaseCount.event? packet.payload ≠ some ⟨start.execution.application.attempt, event⟩) →
      (tapes ⟨⟨start.execution.application.attempt, event⟩, bounded⟩
        ⟨_, PhaseCount.bindingServiceOrdinal_lt_horizon runtime leaks initial horizon scheduler
          before ((menu).toRawTrace initial horizon scheduler prior) owner active
            ⟨start.execution.application.attempt, event⟩⟩).1 = false

private theorem consistent_at_prefix
    (scheduler : (app).Scheduler) (before final : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some final))
    (prefixProof : TracePrefix prior trace) (owner : Player)
    (consistent : (Q owner).Consistent (final.execution.recall owner)) :
    (Q owner).Consistent (before.execution.recall owner) := by
  have mapPrefix : ∀ {before after}
      (earlier : ((menu).protocol initial horizon scheduler).Trace before)
      (later : ((menu).protocol initial horizon scheduler).Trace after),
      TracePrefix earlier later → TracePrefix
        ((menu).toRawTrace initial horizon scheduler earlier)
        ((menu).toRawTrace initial horizon scheduler later) := by
    intro before after earlier later retained
    induction retained with
    | refl => exact .refl
    | extend retained actions legal moved ih =>
        exact TracePrefix.extend ih actions ((menu).legal_raw initial horizon scheduler legal) moved
  have rawPrefix := mapPrefix prior trace prefixProof
  obtain ⟨suffix, kept⟩ := (app).reaches_recall_prefix initial horizon scheduler
    rawPrefix.reachesWithin before final rfl rfl owner
  rw [← kept] at consistent
  exact ReactiveApplication.Policy.Consistent.of_append consistent

include capacity catalogue in
private theorem raw_choice_sends
    (scheduler : (app).Scheduler) (before : (app).Control)
    (prior : ((menu).protocol initial horizon scheduler).Trace (some before))
    (owner : Player) (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout coordinate.1.event = .binding owner payload)
    (active : before.actor = some owner)
    (request : before.execution.application.SeedRequest owner coordinate.1)
    (unsent : ∀ message ∈ (app).outputs (before.execution.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate.1)
    (rawTrue : (tapes coordinate
      ⟨_, PhaseCount.bindingServiceOrdinal_lt_horizon runtime leaks initial horizon scheduler before
        ((menu).toRawTrace initial horizon scheduler prior) owner active coordinate.1⟩).1 = true)
    (action : (app).Action)
    (chosen : action ∈ (Q owner (before.execution.recall owner)
      (before.execution.observe app owner)).support) :
    action.transmission.isSome = true := by
  have tag : before.execution.application.attempt = coordinate.1.attempt := request.1.symm
  have requested : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, coordinate.1.event⟩ := by
    simpa only [tag] using request
  have notSent : ∀ message ∈ (app).outputs (before.execution.recall owner),
      PhaseCount.event? message.payload ≠
        some ⟨before.execution.application.attempt, coordinate.1.event⟩ := by
    simpa only [tag] using unsent
  have law := PhaseCount.bindingServiceTapeMember_transmission_of_history runtime leaks bounds
    (Q owner) owner coordinate.1.event payload
    (fun past view => (values owner coordinate.1.event payload binding past view).map
      PublicationResult.success)
    (choose owner coordinate.1) failure timing firstNonnegative firstBounded timingNonnegative
    timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded plan
    inputs horizon scheduler capacity (tapes coordinate) before prior active binding requested
    notSent (catalogue owner coordinate.1.event payload binding)
  dsimp only at law
  simp only [tag] at law
  simp only [PhaseCount.bindingServiceCoinSends, rawTrue, Bool.true_or] at law
  rw [phaseCountServiceTapePolicy_local_member_at setup mode runtime leaks bounds values choose
    failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan inputs
    scheduler before prior owner coordinate payload binding] at chosen
  have observed : action.transmission.isSome ∈ (PMF.pure true : PMF Bool).support := by
    rw [← law]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨action, chosen, rfl⟩
  exact (PMF.mem_support_pure_iff _ _).mp observed

include ordered calendar capacity catalogue in
/-- A surviving RAW-free reference forces every paired foreign episode to
remain RAW-free under the SAME original positive-RAW table. The comparison
uses actual first-attempt stopped support and occurs BEFORE success privacy. -/
theorem phaseCountServiceTapePolicy_rawFree_of_surviving_reference
    (firstSeeds secondSeeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (firstSupport : firstSeeds ∈ seedLaw.support) (secondSupport : secondSeeds ∈ seedLaw.support)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (firstContract : PhaseService.AsyncContract runtime leaks initial horizon (family firstSeeds)
      delay bound)
    (firstProfile : ∀ who, ((menu).information initial horizon
      (family firstSeeds)).BehavioralPolicy who)
    (secondProfile : ∀ who, ((menu).information initial horizon
      (family secondSeeds)).BehavioralPolicy who)
    (start first second : (app).Control)
    (firstStart : ((menu).protocol initial horizon (family firstSeeds)).Trace (some start))
    (secondStart : ((menu).protocol initial horizon (family secondSeeds)).Trace (some start))
    (firstTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace (some first))
    (secondTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace (some second))
    (phase : RuntimePhase graph) (installed : phase ∈ start.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) (focal : Player)
    (firstRun : ⟨some first, firstTrace⟩ ∈
      (((menu).information initial horizon (family firstSeeds)).runBehavioralUntil
        ((menu).bounded initial horizon (family firstSeeds)).wellFoundedHistories firstProfile
        (fun history => match history.state with
          | none => False
          | some control => control.execution.application.attempt ≠
      start.execution.application.attempt)
        ⟨some start, firstStart⟩).support)
    (secondRun : ⟨some second, secondTrace⟩ ∈
      (((menu).information initial horizon (family secondSeeds)).runBehavioralUntil
        ((menu).bounded initial horizon (family secondSeeds)).wellFoundedHistories secondProfile
        (fun history => match history.state with
          | none => False
          | some control => control.execution.application.attempt ≠
      start.execution.application.attempt)
        ⟨some start, secondStart⟩).support)
    (atEntry : ∀ owner, owner ≠ focal →
      (Q owner).Consistent (start.execution.recall owner))
    (firstFollows : ∀ owner, owner ≠ focal → firstProfile owner =
      (menu).restrictPolicy initial horizon (family firstSeeds) owner (Q owner))
    (secondFollows : ∀ owner, owner ≠ focal → secondProfile owner =
      (menu).restrictPolicy initial horizon (family secondSeeds) owner (Q owner))
    (sameSeeds : ∀ owner, owner ≠ focal → ∀ event ∈ phase.events, (serviceGraph setup mode).actor?
      event = some owner →
      ∀ bounded, firstSeeds.2 (⟨⟨start.execution.application.attempt, event⟩, bounded⟩) =
        secondSeeds.2 (⟨⟨start.execution.application.attempt, event⟩, bounded⟩))
    (survives : ∀ owner, owner ≠ focal → owner ∉ start.execution.application.current.excluded →
      owner ∉ first.execution.application.current.excluded)
    (proper : phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan inputs
      (family firstSeeds) start phase focal first firstTrace) :
    phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan inputs
      (family secondSeeds) start phase focal second secondTrace := by
  classical
  obtain ⟨_ending, stateEq, _changed, idle, _snapshot⟩ :=
    phase_attempt_stopped_receipt_snapshot runtime leaks menu plan inputs horizon (family
      firstSeeds) delay bound firstContract firstProfile start firstStart phase installed
      ⟨some first, firstTrace⟩ (by
        convert firstRun using 1; congr 3; funext history;
          cases history.state <;> rfl)
  cases Option.some.inj stateEq
  rcases first with ⟨remaining, actor, execution⟩
  change actor = none at idle
  subst actor
  let first : (app).Control := ⟨remaining, none, execution⟩
  let firstIdleTrace := firstTrace
  obtain ⟨_ending, stateEq, receipts⟩ := phase_attempt_stopped_survivor_iff_receipts runtime leaks
    menu plan inputs horizon (family firstSeeds) delay bound firstContract firstProfile start
    firstStart phase installed commitment ⟨some first, firstTrace⟩ (by
      convert firstRun using 1; congr 3; funext history;
        cases history.state <;> rfl)
  cases Option.some.inj stateEq
  intro owner foreign active event inside bounded before prior prefixProof activated request unsent
  let coordinate : PhaseSeedAddress graph :=
    ⟨⟨start.execution.application.attempt, event⟩, bounded⟩
  have firstConsistent := phaseCountServiceTapePolicy_consistent_of_continuation setup mode
    runtime leaks bounds values choose failure timing firstNonnegative firstBounded
    timingNonnegative
    timingBounded slotWeight slotNonnegative slotBounded horizon tapes plan inputs rawWeight
    rawNonnegative rawBounded (family firstSeeds) firstProfile start first firstStart firstTrace _
    firstRun owner (firstFollows owner foreign) (atEntry owner foreign)
  have secondConsistent := phaseCountServiceTapePolicy_consistent_of_continuation setup mode
    runtime leaks bounds values choose failure timing firstNonnegative firstBounded
    timingNonnegative
    timingBounded slotWeight slotNonnegative slotBounded horizon tapes plan inputs rawWeight
    rawNonnegative rawBounded (family secondSeeds) secondProfile start second secondStart
    secondTrace
    _ secondRun owner (secondFollows owner foreign) (atEntry owner foreign)
  have beforeConsistent := consistent_at_prefix setup mode runtime leaks bounds values choose
    failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan inputs
    (family secondSeeds) before second prior secondTrace prefixProof owner secondConsistent
  have ranks := (phase.mem_events event).mp inside
  obtain ⟨other, payload, layout⟩ := commitment ▸ phase.fields event ranks.1 ranks.2
  have owned : other = owner := Option.some.inj
    ((actor?_of_outputLayout_binding graph layout).symm.trans request.2.2.2.1)
  subst other
  have accepted := (receipts owner active).mp (survives owner foreign active) event inside
    request.2.2.2.1
  have localConsistent := phaseCountServiceTapePolicy_local_consistent setup mode runtime leaks
    bounds values choose failure timing firstNonnegative firstBounded timingNonnegative
    timingBounded
    slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan
    inputs (family firstSeeds) first firstTrace coordinate owner payload layout
    firstConsistent
  obtain ⟨message, input, sender, tag, named, _receipt⟩ := accepted
  have recalled := (app).history_inputRecall initial horizon (family firstSeeds)
    ((menu).toRawTrace initial horizon (family firstSeeds) firstTrace)
  have authored : message ∈ (app).outputs (first.execution.recall owner) := by
    rw [← recalled owner]
    exact List.mem_filter.mpr ⟨input, by simp only [sender, decide_true]⟩
  have addressed : PhaseCount.event? message.payload = some coordinate.1 := by
    simp only [PhaseCount.event?, named, Option.map_some, tag]
    rfl
  obtain ⟨reference, referenceTrace, referenceAction, referencePrefix, referenceActive,
    referenceRequest, referenceUnsent, _localBefore, referenceChosen, referenceSends, _emission⟩ :=
    PhaseCount.bindingServiceTapeMember_emission_origin runtime leaks bounds plan ordered inputs
      horizon (family firstSeeds) (Q owner) owner coordinate.1 payload
      (fun past view => (values owner event payload layout past view).map PublicationResult.success)
      (choose owner coordinate.1) failure timing firstNonnegative firstBounded timingNonnegative
      timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
      (tapes coordinate) first.remaining first.execution firstIdleTrace localConsistent message
      authored addressed
  have referenceConsistent := consistent_at_prefix setup mode runtime leaks bounds values choose
    failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan inputs
    (family firstSeeds) reference first referenceTrace firstTrace referencePrefix owner
    firstConsistent
  rw [← phaseCountServiceTapePolicy_local_member_at setup mode runtime leaks bounds values choose
    failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan inputs
    (family firstSeeds) reference referenceTrace owner coordinate payload layout] at referenceChosen
  by_contra notFalse
  have rawTrue := Bool.eq_true_of_ne_false notFalse
  obtain ⟨action, chosen⟩ := (Q owner (before.execution.recall owner)
    (before.execution.observe app owner)).support_nonempty
  have sends := raw_choice_sends setup mode runtime leaks bounds values choose failure timing
    firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
    slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan inputs capacity catalogue
    (family secondSeeds) before prior owner coordinate payload layout activated request unsent
    rawTrue action chosen
  have common := phaseCountServiceTapePolicy_first_send_raw_eq setup mode runtime leaks bounds
    values choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
    slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan
    ordered inputs seedLaw family calendar capacity catalogue secondSeeds firstSeeds secondSupport
    firstSupport owner coordinate payload layout before reference prior referenceTrace activated
    referenceActive request referenceRequest (sameSeeds owner foreign event inside
      request.2.2.2.1 bounded).symm unsent referenceUnsent beforeConsistent referenceConsistent
    action
    referenceAction chosen referenceChosen sends referenceSends
  have referenceFalse := proper owner foreign active event inside bounded reference referenceTrace
    referencePrefix referenceActive referenceRequest referenceUnsent
  exact Bool.noConfusion (rawTrue.symm.trans (common.2.trans referenceFalse))

include ordered calendar privateSuccess capacity catalogue in
/-- On the actual normalized counted-SEND reference, a surviving RAW-free
foreign phase remains surviving and RAW-free under every focal continuation.
The RAW contradiction is established BEFORE proper success privacy is used;
all original tier/timing tables, entry recall and first-attempt outcomes remain. -/
theorem phaseCountServiceTapePolicy_good_survival
    (firstSeeds secondSeeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (firstSupport : firstSeeds ∈ seedLaw.support) (secondSupport : secondSeeds ∈ seedLaw.support)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (firstContract : PhaseService.AsyncContract runtime leaks initial horizon (family firstSeeds)
      delay bound)
    (secondContract : PhaseService.AsyncContract runtime leaks initial horizon (family secondSeeds)
      delay bound)
    (firstProfile : ∀ who, ((menu).information initial horizon
      (family firstSeeds)).BehavioralPolicy who)
    (secondProfile : ∀ who, ((menu).information initial horizon
      (family secondSeeds)).BehavioralPolicy who)
    (start first second : (app).Control)
    (firstStart : ((menu).protocol initial horizon (family firstSeeds)).Trace (some start))
    (secondStart : ((menu).protocol initial horizon (family secondSeeds)).Trace (some start))
    (firstTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace (some first))
    (secondTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace (some second))
    (phase : RuntimePhase graph) (installed : phase ∈ start.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) (focal : Player)
    (firstRun : ⟨some first, firstTrace⟩ ∈
      (((menu).information initial horizon (family firstSeeds)).runBehavioralUntil
        ((menu).bounded initial horizon (family firstSeeds)).wellFoundedHistories firstProfile
        (fun history => match history.state with
          | none => False
          | some control => control.execution.application.attempt ≠
      start.execution.application.attempt)
        ⟨some start, firstStart⟩).support)
    (secondRun : ⟨some second, secondTrace⟩ ∈
      (((menu).information initial horizon (family secondSeeds)).runBehavioralUntil
        ((menu).bounded initial horizon (family secondSeeds)).wellFoundedHistories secondProfile
        (fun history => match history.state with
          | none => False
          | some control => control.execution.application.attempt ≠
      start.execution.application.attempt)
        ⟨some start, secondStart⟩).support)
    (atEntry : ∀ owner, owner ≠ focal →
      (Q owner).Consistent (start.execution.recall owner))
    (firstFollows : ∀ owner, owner ≠ focal → firstProfile owner =
      (menu).restrictPolicy initial horizon (family firstSeeds) owner (Q owner))
    (secondFollows : ∀ owner, owner ≠ focal → secondProfile owner =
      (menu).restrictPolicy initial horizon (family secondSeeds) owner (Q owner))
    (sameSeeds : ∀ owner, owner ≠ focal → ∀ event ∈ phase.events, (serviceGraph setup mode).actor?
      event = some owner →
      ∀ bounded, firstSeeds.2 (⟨⟨start.execution.application.attempt, event⟩, bounded⟩) =
        secondSeeds.2 (⟨⟨start.execution.application.attempt, event⟩, bounded⟩))
    (survives : ∀ owner, owner ≠ focal → owner ∉ start.execution.application.current.excluded →
      owner ∉ first.execution.application.current.excluded)
    (proper : phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan inputs
      (family firstSeeds) start phase focal first firstTrace) :
    (∀ owner, owner ≠ focal → owner ∉ start.execution.application.current.excluded →
      owner ∉ second.execution.application.current.excluded) ∧
    phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan inputs
      (family secondSeeds) start phase focal second secondTrace := by
  classical
  have pairedProper := phaseCountServiceTapePolicy_rawFree_of_surviving_reference setup mode
    runtime leaks bounds values choose failure timing firstNonnegative firstBounded
      timingNonnegative
    timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
    tapes plan ordered inputs seedLaw family calendar capacity catalogue firstSeeds secondSeeds
    firstSupport secondSupport delay bound firstContract firstProfile secondProfile start first
    second firstStart secondStart firstTrace secondTrace phase installed commitment focal firstRun
    secondRun atEntry firstFollows secondFollows sameSeeds survives proper
  refine ⟨?_, pairedProper⟩
  intro owner foreign active failed
  have survived := survives owner foreign active
  have firstConsistent := phaseCountServiceTapePolicy_consistent_of_continuation setup mode
    runtime leaks bounds values choose
    failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded horizon tapes plan inputs rawWeight rawNonnegative rawBounded
    (family firstSeeds) firstProfile start
    first firstStart firstTrace _ firstRun owner (firstFollows owner foreign) (atEntry owner
      foreign)
  have secondConsistent := phaseCountServiceTapePolicy_consistent_of_continuation setup mode
    runtime leaks bounds values choose
    failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative slotBounded horizon tapes plan inputs rawWeight rawNonnegative rawBounded
    (family secondSeeds) secondProfile start
    second secondStart secondTrace _ secondRun owner (secondFollows owner foreign) (atEntry owner
      foreign)
  have sameSeeds := sameSeeds owner foreign
  obtain ⟨firstEnd, firstState, firstChanged, firstIdle, _snapshot⟩ :=
    phase_attempt_stopped_receipt_snapshot runtime leaks menu plan inputs horizon (family
      firstSeeds)
      delay bound firstContract firstProfile start firstStart phase installed ⟨some first,
      firstTrace⟩ (by
        convert firstRun using 1; congr 3; funext history;
          cases history.state <;> rfl)
  cases Option.some.inj firstState
  obtain ⟨secondEnd, secondState, secondChanged, secondIdle, _snapshot⟩ :=
    phase_attempt_stopped_receipt_snapshot runtime leaks menu plan inputs horizon (family
      secondSeeds)
      delay bound secondContract secondProfile start secondStart phase installed ⟨some second,
      secondTrace⟩ (by
        convert secondRun using 1; congr 3; funext history;
          cases history.state <;> rfl)
  cases Option.some.inj secondState
  rcases first with ⟨firstRemaining, firstActor, firstExecution⟩
  change firstActor = none at firstIdle
  subst firstActor
  let first : (app).Control := ⟨firstRemaining, none, firstExecution⟩
  rcases second with ⟨secondRemaining, secondActor, secondExecution⟩
  change secondActor = none at secondIdle
  subst secondActor
  let second : (app).Control := ⟨secondRemaining, none, secondExecution⟩
  let firstIdleTrace : ((menu).protocol initial horizon (family firstSeeds)).Trace
      (some ⟨first.remaining, none, first.execution⟩) := firstTrace
  let secondIdleTrace : ((menu).protocol initial horizon (family secondSeeds)).Trace
      (some ⟨second.remaining, none, second.execution⟩) := secondTrace
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered plan draw
  have firstOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    (family firstSeeds) initialized ((menu).toRawTrace initial horizon (family firstSeeds)
      firstStart)
  have secondOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    (family secondSeeds) initialized ((menu).toRawTrace initial horizon (family secondSeeds)
      secondStart)
  have firstPrefix := ((menu).information initial horizon (family
      firstSeeds)).runBehavioralUntil_support_prefix
    ((menu).bounded initial horizon (family firstSeeds)).wellFoundedHistories firstProfile _
    ⟨some start, firstStart⟩ ⟨some first, firstTrace⟩ firstRun
  have secondPrefix := ((menu).information initial horizon (family
      secondSeeds)).runBehavioralUntil_support_prefix
    ((menu).bounded initial horizon (family secondSeeds)).wellFoundedHistories secondProfile _
    ⟨some start, secondStart⟩ ⟨some second, secondTrace⟩ secondRun
  have firstProgress := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
      horizon
    (family firstSeeds) start first firstStart firstTrace firstPrefix firstOrdered
  have secondProgress := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
      horizon
    (family secondSeeds) start second secondStart secondTrace secondPrefix secondOrdered
  have firstResolved (event : (serviceGraph setup mode).EventId) :
      (⟨start.execution.application.attempt, event⟩ : CommitAttemptEvent graph).Resolved
        first.execution.application := CommitAttemptEvent.Resolved.of_step _ _ _ rfl
          ⟨firstProgress.1, firstProgress.2.1⟩ (Or.inl (Ne.symm firstChanged))
  have secondResolved (event : (serviceGraph setup mode).EventId) :
      (⟨start.execution.application.attempt, event⟩ : CommitAttemptEvent graph).Resolved
        second.execution.application := CommitAttemptEvent.Resolved.of_step _ _ _ rfl
          ⟨secondProgress.1, secondProgress.2.1⟩ (Or.inl (Ne.symm secondChanged))
  have boundFor (event : (serviceGraph setup mode).EventId) (before : (app).Control)
      (prior : ((menu).protocol initial horizon (family firstSeeds)).Trace (some before))
      (request : before.execution.application.SeedRequest owner
        ⟨start.execution.application.attempt, event⟩) :
      start.execution.application.attempt.phase < (serviceGraph setup mode).order.eventCount ∧
        start.execution.application.attempt.generation ≤ Fintype.card Player := by
    have budget := (phaseApplication_seedBudget runtime leaks).history initial horizon
      (family firstSeeds) (fun state member => by
        obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ member
        exact PhaseRuntimeState.initial_seedBudget plan draw)
      ((menu).toRawTrace initial horizon (family firstSeeds) prior)
    exact (request.coordinate budget).2
  obtain ⟨_first, firstEq, firstReceipt⟩ := phase_attempt_stopped_survivor_iff_receipts runtime
      leaks
    menu plan inputs horizon (family firstSeeds) delay bound firstContract firstProfile start
      firstStart
    phase installed commitment ⟨some first, firstTrace⟩ (by
        convert firstRun using 1; congr 3; funext history;
          cases history.state <;> rfl)
  cases Option.some.inj firstEq
  obtain ⟨_second, secondEq, secondReceipt⟩ := phase_attempt_stopped_survivor_iff_receipts runtime
      leaks
    menu plan inputs horizon (family secondSeeds) delay bound secondContract secondProfile start
      secondStart
    phase installed commitment ⟨some second, secondTrace⟩ (by
        convert secondRun using 1; congr 3; funext history;
          cases history.state <;> rfl)
  cases Option.some.inj secondEq
  obtain ⟨event, inside, before, prior, _fromStart, retained, _same, request, absent⟩ :=
    PhaseService.phase_attempt_stopped_exclusion_unaccepted runtime leaks menu plan inputs horizon
      (family secondSeeds) secondProfile start secondStart phase installed commitment owner active
      ⟨some second, secondTrace⟩ (by
      convert secondRun using 1; congr 3; funext history;
        cases history.state <;> rfl) second rfl failed
  have accepted := (firstReceipt owner active).mp survived event inside request.2.2.2.1
  have bounded : start.execution.application.attempt.phase < (serviceGraph setup
    mode).order.eventCount ∧
      start.execution.application.attempt.generation ≤ Fintype.card Player := by
    have budget := (phaseApplication_seedBudget runtime leaks).history initial horizon
      (family secondSeeds) (fun state member => by
        obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ member
        exact PhaseRuntimeState.initial_seedBudget plan draw)
      ((menu).toRawTrace initial horizon (family secondSeeds) prior)
    exact (request.coordinate budget).2
  let coordinate : PhaseSeedAddress graph := ⟨⟨start.execution.application.attempt, event⟩,
    bounded⟩
  have ranks := (phase.mem_events event).mp inside
  obtain ⟨who, payload, layout⟩ := commitment ▸ phase.fields event ranks.1 ranks.2
  have same : who = owner := Option.some.inj
    ((actor?_of_outputLayout_binding graph layout).symm.trans request.2.2.2.1)
  subst who
  have ready := phaseCountServiceTapePolicy_receipt_request_origin setup mode runtime leaks
    bounds values choose failure
    timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
    slotNonnegative
    slotBounded horizon tapes plan ordered inputs family rawWeight rawNonnegative rawBounded
    firstSeeds first.remaining
    first.execution firstIdleTrace owner coordinate payload layout firstConsistent accepted
  have success := phaseCountServiceTapePolicy_accepted_iff_of_resolved setup mode runtime leaks
    bounds values choose failure timing firstNonnegative firstBounded timingNonnegative
    timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
    horizon tapes plan ordered inputs seedLaw family calendar privateSuccess firstSeeds
    secondSeeds
    firstSupport secondSupport owner coordinate payload layout capacity
    (catalogue owner event payload layout) first.remaining second.remaining first.execution
    second.execution firstIdleTrace secondIdleTrace ready ⟨before, prior, retained, request⟩
    (firstResolved event) (secondResolved event) (sameSeeds event inside request.2.2.2.1 bounded)
    firstConsistent secondConsistent
  exact absent (success.mp accepted)

open Classical in
include ordered calendar privateSuccess capacity catalogue in
/-- The literal stopped good-event law is nonfocal at the original phase
boundary for the SAME positive-RAW table and foreign seeds. No word or payoff
is asserted after RAW. The direct reference has transmission-only RAW;
whole-menu RAW WAIT requires its separate same-action origin repair. -/
theorem phaseCountServiceTapePolicy_good_law
    (firstSeeds secondSeeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (firstSupport : firstSeeds ∈ seedLaw.support) (secondSupport : secondSeeds ∈ seedLaw.support)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (firstContract : PhaseService.AsyncContract runtime leaks initial horizon (family firstSeeds)
      delay bound)
    (secondContract : PhaseService.AsyncContract runtime leaks initial horizon (family secondSeeds)
      delay bound)
    (firstProfile : ∀ who, ((menu).information initial horizon
      (family firstSeeds)).BehavioralPolicy who)
    (secondProfile : ∀ who, ((menu).information initial horizon
      (family secondSeeds)).BehavioralPolicy who)
    (start : (app).Control)
    (firstStart : ((menu).protocol initial horizon (family firstSeeds)).Trace (some start))
    (secondStart : ((menu).protocol initial horizon (family secondSeeds)).Trace (some start))
    (phase : RuntimePhase graph) (installed : phase ∈ start.execution.application.phases.head?)
    (commitment : phase.kind = .commitment) (focal : Player)
    (atEntry : ∀ owner, owner ≠ focal →
      (Q owner).Consistent (start.execution.recall owner))
    (firstFollows : ∀ owner, owner ≠ focal → firstProfile owner =
      (menu).restrictPolicy initial horizon (family firstSeeds) owner (Q owner))
    (secondFollows : ∀ owner, owner ≠ focal → secondProfile owner =
      (menu).restrictPolicy initial horizon (family secondSeeds) owner (Q owner))
    (sameSeeds : ∀ owner, owner ≠ focal → ∀ event ∈ phase.events, (serviceGraph setup mode).actor?
      event = some owner →
      ∀ bounded, firstSeeds.2 (⟨⟨start.execution.application.attempt, event⟩, bounded⟩) =
        secondSeeds.2 (⟨⟨start.execution.application.attempt, event⟩, bounded⟩))
    :
    let firstStopped := fun history : ((menu).protocol initial horizon
        (family firstSeeds)).History => match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ start.execution.application.attempt
    let secondStopped := fun history : ((menu).protocol initial horizon
        (family secondSeeds)).History => match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ start.execution.application.attempt
    let firstLaw := ((menu).information initial horizon (family firstSeeds)).runBehavioralUntil
      ((menu).bounded initial horizon (family firstSeeds)).wellFoundedHistories firstProfile
      firstStopped ⟨some start, firstStart⟩
    let secondLaw := ((menu).information initial horizon (family secondSeeds)).runBehavioralUntil
      ((menu).bounded initial horizon (family secondSeeds)).wellFoundedHistories secondProfile
      secondStopped ⟨some start, secondStart⟩
    let firstGood : ((menu).protocol initial horizon (family firstSeeds)).History → Bool :=
      fun history => match history with
        | ⟨none, _⟩ => false
        | ⟨some control, trace⟩ => decide
          ((∀ owner, owner ≠ focal → owner ∉ start.execution.application.current.excluded →
            owner ∉ control.execution.application.current.excluded) ∧
          phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan inputs
            (family firstSeeds) start phase focal control trace)
    let secondGood : ((menu).protocol initial horizon (family secondSeeds)).History → Bool :=
      fun history => match history with
        | ⟨none, _⟩ => false
        | ⟨some control, trace⟩ => decide
          ((∀ owner, owner ≠ focal → owner ∉ start.execution.application.current.excluded →
            owner ∉ control.execution.application.current.excluded) ∧
          phaseCountServiceRawFree setup mode runtime leaks bounds horizon tapes plan inputs
            (family secondSeeds) start phase focal control trace)
    firstLaw.map firstGood = secondLaw.map secondGood := by
  classical
  intro firstStopped secondStopped firstLaw secondLaw firstGood secondGood
  have same : ∀ first ∈ firstLaw.support, ∀ second ∈ secondLaw.support,
      firstGood first = secondGood second := by
    rintro ⟨firstState, firstTrace⟩ firstRun ⟨secondState, secondTrace⟩ secondRun
    obtain ⟨first, firstEq, _changed, _idle, _snapshot⟩ :=
      phase_attempt_stopped_receipt_snapshot runtime leaks menu plan inputs horizon
        (family firstSeeds) delay bound firstContract firstProfile start firstStart phase installed
        ⟨firstState, firstTrace⟩ (by
          convert firstRun using 1; congr 3; funext history
          dsimp only [firstStopped]
          cases history.state <;> rfl)
    cases firstEq
    obtain ⟨second, secondEq, _changed, _idle, _snapshot⟩ :=
      phase_attempt_stopped_receipt_snapshot runtime leaks menu plan inputs horizon
        (family secondSeeds) delay bound secondContract secondProfile start secondStart phase
        installed ⟨secondState, secondTrace⟩ (by
          convert secondRun using 1; congr 3; funext history
          dsimp only [secondStopped]
          cases history.state <;> rfl)
    cases secondEq
    change decide _ = decide _
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨survives, proper⟩
      exact phaseCountServiceTapePolicy_good_survival setup mode runtime leaks bounds values choose
        failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan ordered
        inputs seedLaw family calendar privateSuccess capacity catalogue firstSeeds secondSeeds
        firstSupport secondSupport delay bound firstContract secondContract firstProfile
          secondProfile
        start first second firstStart secondStart firstTrace secondTrace phase installed commitment
        focal firstRun secondRun atEntry firstFollows secondFollows sameSeeds survives proper
    · rintro ⟨survives, proper⟩
      exact phaseCountServiceTapePolicy_good_survival setup mode runtime leaks bounds values choose
        failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan ordered
        inputs seedLaw family calendar privateSuccess capacity catalogue secondSeeds firstSeeds
        secondSupport firstSupport delay bound secondContract firstContract secondProfile
          firstProfile
        start second first secondStart firstStart secondTrace firstTrace phase installed commitment
        focal secondRun firstRun atEntry secondFollows firstFollows
        (fun owner foreign event inside actor bounded =>
          (sameSeeds owner foreign event inside actor bounded).symm) survives proper
  obtain ⟨reference, supported⟩ := secondLaw.support_nonempty
  calc
    _ = firstLaw.map (fun _ => secondGood reference) :=
      map_congr_on_support firstLaw (fun first member => same first member reference supported)
    _ = PMF.pure (secondGood reference) := PMF.map_const _ _
    _ = secondLaw.map (fun _ => secondGood reference) := (PMF.map_const _ _).symm
    _ = secondLaw.map secondGood :=
      map_congr_on_support secondLaw (fun second member => by
        obtain ⟨first, present⟩ := firstLaw.support_nonempty
        exact (same first present reference supported).symm.trans (same first present second
          member))

end GoodPhase

end Vegas
