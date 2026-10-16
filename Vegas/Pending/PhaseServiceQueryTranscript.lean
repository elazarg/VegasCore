/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceCallbackCounters
import Vegas.Pending.PhaseServiceQueryPrefix

/-! # Complete actual query transcripts from clocked owner emissions -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability
open LocalSeedController (CountedQueryLog positiveQueries exhaustedClocks)

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (counterLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => phaseApplication runtime leaks
local notation "counterApp" => runtime.reactiveApplication counterLeaks

/-- Restore each query from its actual earlier clocked emission prefix.
Raw packet values are erased only by the existing operational-input map. -/
def restoreWordCounterEntry (owner : Player) (attempt : CommitAttemptId)
    (word : List (Nat × List (Message Player (CommitAttemptPacket graph))))
    (entry : LocalSeedEntry graph (counterApp).Command) :
    PhaseSeedOperationalInput graph × (app).Command :=
  (PhaseSeedInput.operational attempt
    { elapsed := entry.query.input.elapsed
      activationClocks := (word.take entry.query.activationIndex).map Prod.fst
      emissions := (word.take entry.query.activationIndex).flatMap fun item =>
        item.2.map (Prod.mk item.1) },
    match entry.reply with
    | .activation => .activate owner
    | _ => .wait)

omit [Fintype Player] in
private theorem restore_word_counter_map (owner : Player) (attempt : CommitAttemptId)
    (word : List (Nat × List (Message Player (CommitAttemptPacket graph))))
    (items : List (PhaseSeedOperationalInput graph × (app).Command))
    (prefixes : ∀ item ∈ items,
      ∃ before : List (Nat × List (Message Player (CommitAttemptPacket graph))),
        before <+: word ∧ item.1 = PhaseSeedInput.operational attempt
          { elapsed := item.1.elapsed
            activationClocks := before.map Prod.fst
            emissions := before.flatMap fun entry => entry.2.map (Prod.mk entry.1) })
    (unresolved : ∀ item ∈ items, item.2 = .activate owner ∨ item.2 = .wait) :
    (items.map (counterEntry runtime leaks counterLeaks owner)).map
      (restoreWordCounterEntry runtime leaks counterLeaks owner attempt word) = items := by
  rw [List.map_map]
  calc
    _ = List.map id items := by
      apply List.map_congr_left
      intro item member
      obtain ⟨before, isPrefix, query⟩ := prefixes item member
      have clockEq : item.1.activationClocks = before.map Prod.fst :=
        congrArg PhaseSeedOperationalInput.activationClocks query
      have take : word.take item.1.activationClocks.length = before := by
        obtain ⟨later, joined⟩ := isPrefix
        rw [← joined, clockEq, List.length_map]
        exact List.take_left
      have canonical : item.1 = PhaseSeedInput.operational attempt
          { elapsed := item.1.elapsed
            activationClocks := (word.take item.1.activationClocks.length).map Prod.fst
            emissions := (word.take item.1.activationClocks.length).flatMap fun entry =>
              entry.2.map (Prod.mk entry.1) } := by
        rw [take]
        exact query
      rcases unresolved item member with activated | waited
      · simp only [Function.comp_def, restoreWordCounterEntry, counterEntry,
          ite_eq_left activated]
        exact Prod.ext canonical.symm activated.symm
      · simp only [Function.comp_def, restoreWordCounterEntry, counterEntry, waited,
          reduceCtorEq, ite_false]
        exact Prod.ext canonical.symm waited.symm
    _ = items := List.map_id _

/-- The current callback contributes its elapsed clock to the actual retained own word. -/
theorem active_owner_word_clocks
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (coordinate : PhaseSeedAddress graph)
    (request : execution.application.SeedRequest owner coordinate.1) :
    (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        ((execution.respond app owner ⟨none⟩).recall owner)).map Prod.fst =
      (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
        (execution.recall owner) (execution.observe app owner)).activationClocks ++
        [(PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
          (execution.recall owner) (execution.observe app owner)).elapsed] := by
  classical
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon _ trace
  obtain ⟨_, valid, _⟩ :=
    currentTokenPrerequisites_history runtime leaks plan inputs horizon _ raw
  have visible : PhaseRuntimeState.requests (execution.observe app owner).application.2 owner
      coordinate.1 :=
    (PhaseRuntimeState.requests_publicView _ valid owner coordinate.1).mpr request
  have visibleBool : decide (PhaseRuntimeState.requests
      (execution.observe app owner).application.2 owner coordinate.1) = true :=
    decide_eq_true visible
  simp only [ReactiveApplication.Execution.respond, PhaseSeedScheduler.ownerWord,
    List.filter_append, List.filter_cons, List.filter_nil, List.map_append, List.map_cons,
    List.map_nil, visibleBool, ite_true, PhaseSeedScheduler.informationInput]

/-- Actual complete owner information recovers every prior local query,
including its original emitted packet identifiers and authorization. -/
theorem active_query_transcript_signature
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (timed : DeadlineExpiry runtime decideLocal)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks priority decideLocal).family seeds)).Trace
        (some ⟨remaining, some owner, execution⟩))
    (coordinate : PhaseSeedAddress graph)
    (request : execution.application.SeedRequest owner coordinate.1) :
    let transcript := (controller runtime leaks priority decideLocal).coordinateTranscriptFrom
      seeds.1 coordinate [] execution.environmentRecall
    let log := transcript.map (counterEntry runtime leaks counterLeaks owner)
    let input := PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
      (execution.recall owner) (execution.observe app owner)
    CountedQueryLog log ∧
      (positiveQueries log).map (fun query => query.input.elapsed) =
        input.activationClocks ++ [input.elapsed] ∧
      (exhaustedClocks log).length = input.elapsed ∧
      log.map (restoreWordCounterEntry runtime leaks counterLeaks owner coordinate.1.attempt
        (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
          ((execution.respond app owner ⟨none⟩).recall owner))) = transcript := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let scheduler := (controller runtime leaks priority decideLocal).family seeds
  let idle := execution.respond app owner ⟨none⟩
  obtain ⟨idleTrace⟩ := menu.trace_respond initial horizon scheduler remaining execution owner
    ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds owner
      (execution.recall owner) (execution.observe app owner))
  have clocks := active_owner_word_clocks runtime leaks bounds plan inputs horizon scheduler
    remaining owner execution trace coordinate request
  have fullSupport := menu.roundSupported_uniform initial horizon scheduler idleTrace
  obtain ⟨state, stateSupported, reached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ fullSupport.2)
  obtain ⟨initialInput, _supported, rfl⟩ := PMF.support_map .. ▸ stateSupported
  have counted := history_countedQueryLog runtime leaks counterLeaks priority decideLocal timed
    seeds bounds plan ordered maximal inputs horizon remaining idle idleTrace coordinate owner
      request
  have actualWord := runRounds_activationTranscript runtime leaks priority decideLocal seeds ordered
    coordinate owner request.2.2.2.1 menu.uniformResponses idle.environmentRecall.length
    (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan initialInput)) idle
      (PhaseRuntimeState.initial_invariant plan initialInput).1
      (PhaseSeedScheduler.initial_wordRecall runtime leaks
        (PhaseRuntimeState.initial plan initialInput)) (by rfl) reached
  have queryInputs := initialized_queryOperationalPrefixes runtime leaks priority decideLocal
    seeds.1 coordinate owner request.2.2.2.1 scheduler menu.uniformResponses
      idle.environmentRecall.length (PhaseRuntimeState.initial plan initialInput) idle reached
  have unresolved := queried_activate_or_wait runtime leaks priority decideLocal timed seeds bounds
    plan ordered maximal inputs horizon remaining idle idleTrace coordinate owner request
  have positives := counterEntry_positive_clocks runtime leaks counterLeaks owner
    ((controller runtime leaks priority decideLocal).coordinateTranscriptFrom seeds.1 coordinate []
      idle.environmentRecall)
  change _ = activationTranscript runtime leaks priority decideLocal seeds.1 coordinate owner
    idle.environmentRecall at positives
  rw [← actualWord, clocks] at positives
  have exhausts := counterEntry_exhausted runtime leaks counterLeaks owner
    ((controller runtime leaks priority decideLocal).coordinateTranscriptFrom seeds.1 coordinate []
      idle.environmentRecall) unresolved
  change _ = waitClocks runtime leaks priority decideLocal seeds.1 coordinate
    idle.environmentRecall at exhausts
  have exhaustionCount := congrArg List.length exhausts
  rw [(app).respond_environmentRecall,
    active_wait_count runtime leaks priority decideLocal timed seeds bounds plan ordered maximal
      inputs horizon remaining owner execution trace coordinate request] at exhaustionCount
  have restored := restore_word_counter_map runtime leaks counterLeaks owner coordinate.1.attempt
    (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner (idle.recall owner))
    ((controller runtime leaks priority decideLocal).coordinateTranscriptFrom seeds.1 coordinate []
      idle.environmentRecall) queryInputs unresolved
  simpa only [idle, (app).respond_environmentRecall] using
    And.intro counted ⟨positives, exhaustionCount, restored⟩


omit [Fintype Player] in
private theorem restore_word_counter_congr (owner : Player) (attempt : CommitAttemptId)
    (first second : List (Nat × List (Message Player (CommitAttemptPacket graph))))
    (same : first.map (fun item => (item.1, item.2.map fun message =>
        PhaseSeedInput.operationalEmission attempt (item.1, message))) =
      second.map (fun item => (item.1, item.2.map fun message =>
        PhaseSeedInput.operationalEmission attempt (item.1, message))))
    (entry : LocalSeedEntry graph (counterApp).Command) :
    restoreWordCounterEntry runtime leaks counterLeaks owner attempt first entry =
      restoreWordCounterEntry runtime leaks counterLeaks owner attempt second entry := by
  have prefixes := congrArg (List.take entry.query.activationIndex) same
  rw [← List.map_take, ← List.map_take] at prefixes
  have clocks := congrArg (List.map Prod.fst) prefixes
  simp only [List.map_map, Function.comp_def] at clocks
  have emissions := congrArg (List.flatMap Prod.snd) prefixes
  simp only [List.flatMap_map] at emissions
  apply Prod.ext
  · apply congrArg₂ (PhaseSeedOperationalInput.mk entry.query.input.elapsed)
    · exact clocks
    · simpa only [PhaseSeedInput.operational, List.map_flatMap, List.map_map,
        Function.comp_def] using emissions
  · rfl

/-- The complete erased own clock-and-packet word determines every actual
local query and every candidate-seed constraint, including after a send.
Foreign traffic, private packet values and native information may differ. -/
theorem operational_word_transcript
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision) (timed : DeadlineExpiry runtime decideLocal)
    (firstSeeds secondSeeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon firstRemaining secondRemaining : Nat) (owner : Player)
    (first second : (app).Execution)
    (firstTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks priority decideLocal).family firstSeeds)).Trace
        (some ⟨firstRemaining, some owner, first⟩))
    (secondTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks priority decideLocal).family secondSeeds)).Trace
        (some ⟨secondRemaining, some owner, second⟩))
    (coordinate : PhaseSeedAddress graph)
    (firstRequest : first.application.SeedRequest owner coordinate.1)
    (secondRequest : second.application.SeedRequest owner coordinate.1)
    (same :
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        ((first.respond app owner ⟨none⟩).recall owner)).map (fun item =>
          (item.1, item.2.map fun message =>
            PhaseSeedInput.operationalEmission coordinate.1.attempt (item.1, message))) =
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        ((second.respond app owner ⟨none⟩).recall owner)).map (fun item =>
          (item.1, item.2.map fun message =>
            PhaseSeedInput.operationalEmission coordinate.1.attempt (item.1, message)))) :
    (controller runtime leaks priority decideLocal).coordinateTranscriptFrom firstSeeds.1 coordinate
        [] first.environmentRecall =
      (controller runtime leaks priority decideLocal).coordinateTranscriptFrom secondSeeds.1
        coordinate [] second.environmentRecall ∧
    ∀ candidate, (controller runtime leaks priority decideLocal).coordinateConsistentFrom
        firstSeeds.1 coordinate candidate [] first.environmentRecall ↔
      (controller runtime leaks priority decideLocal).coordinateConsistentFrom secondSeeds.1
        coordinate candidate [] second.environmentRecall := by
  let counterLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph) :=
    fun _ _ => PMF.pure ∅
  obtain ⟨leftCounted, leftClocks, leftWaits, leftRestored⟩ :=
    active_query_transcript_signature runtime leaks counterLeaks priority decideLocal timed
      firstSeeds bounds plan ordered maximal inputs horizon firstRemaining owner first firstTrace
        coordinate firstRequest
  obtain ⟨rightCounted, rightClocks, rightWaits, rightRestored⟩ :=
    active_query_transcript_signature runtime leaks counterLeaks priority decideLocal timed
      secondSeeds bounds plan ordered maximal inputs horizon secondRemaining owner second
        secondTrace coordinate secondRequest
  have nativeClocks := congrArg (List.map Prod.fst) same
  simp only [List.map_map, Function.comp_def] at nativeClocks
  have leftVisible := active_owner_word_clocks runtime leaks bounds plan inputs horizon _
    firstRemaining owner first firstTrace coordinate firstRequest
  have rightVisible := active_owner_word_clocks runtime leaks bounds plan inputs horizon _
    secondRemaining owner second secondTrace coordinate secondRequest
  rw [leftVisible, rightVisible] at nativeClocks
  have reversed := congrArg List.reverse nativeClocks
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.cons.injEq] at reversed
  have emptyLog (items : List (PhaseSeedOperationalInput graph × (app).Command)) :
      ∀ entry ∈ items.map (counterEntry runtime leaks counterLeaks owner),
        entry.query.input.emitted = [] ∧
          (entry.reply = .activation ∨ entry.reply = .exhausted) := by
    intro entry member
    obtain ⟨item, _member, rfl⟩ := List.mem_map.mp member
    dsimp only [counterEntry]
    split <;> simp
  have sameLogs := leftCounted.eq_of_unsent_signature rightCounted
    (fun entry member => (emptyLog _ entry member).1)
    (fun entry member => (emptyLog _ entry member).1)
    (fun entry member => (emptyLog _ entry member).2)
    (fun entry member => (emptyLog _ entry member).2)
    (leftClocks.trans (nativeClocks.trans rightClocks.symm))
    (leftWaits.trans (reversed.1.trans rightWaits.symm))
  have restored := congrArg (List.map (restoreWordCounterEntry runtime leaks counterLeaks owner
    coordinate.1.attempt (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      ((first.respond app owner ⟨none⟩).recall owner)))) sameLogs
  rw [leftRestored] at restored
  have sameRestore : restoreWordCounterEntry runtime leaks counterLeaks owner coordinate.1.attempt
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        ((first.respond app owner ⟨none⟩).recall owner)) =
    restoreWordCounterEntry runtime leaks counterLeaks owner coordinate.1.attempt
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        ((second.respond app owner ⟨none⟩).recall owner)) := by
    funext entry
    exact restore_word_counter_congr runtime leaks counterLeaks owner coordinate.1.attempt _ _
      same entry
  rw [sameRestore, rightRestored] at restored
  refine ⟨restored, ?_⟩
  intro candidate
  simp only [ReactiveApplication.AddressedScheduler.coordinateConsistentFrom_iff_transcript,
    restored]

end Vegas.EventGraphRuntime.PhaseServiceScheduler
