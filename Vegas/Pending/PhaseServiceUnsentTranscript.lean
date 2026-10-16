/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceCallbackCounters

/-! # Complete actual unsent query transcripts from owner information -/

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

/-- Recover the operational input from the original owner clock word and the
existing log counters. Resolution branches are unused at a surviving address. -/
def restoreCounterEntry (owner : Player) (clocks : List Nat)
    (entry : LocalSeedEntry graph (counterApp).Command) :
    PhaseSeedOperationalInput graph × (app).Command :=
  (⟨entry.query.input.elapsed, clocks.take entry.query.activationIndex, []⟩,
    match entry.reply with
    | .activation => .activate owner
    | _ => .wait)

/-- The actual unsent callback transcript has the existing counted-log
signature read from full owner information and is exactly restored from it. -/
theorem active_unsent_transcript_signature
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
    (request : execution.application.SeedRequest owner coordinate.1)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false) :
    let transcript := (controller runtime leaks priority decideLocal).coordinateTranscriptFrom
      seeds.1 coordinate [] execution.environmentRecall
    let log := transcript.map (counterEntry runtime leaks counterLeaks owner)
    let input := PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
      (execution.recall owner) (execution.observe app owner)
    CountedQueryLog log ∧
      (positiveQueries log).map (fun query => query.input.elapsed) =
        input.activationClocks ++ [input.elapsed] ∧
      (exhaustedClocks log).length = input.elapsed ∧
      log.map (restoreCounterEntry runtime leaks counterLeaks owner
        (input.activationClocks ++ [input.elapsed])) = transcript := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let scheduler := (controller runtime leaks priority decideLocal).family seeds
  let idle := execution.respond app owner ⟨none⟩
  obtain ⟨idleTrace⟩ := menu.trace_respond initial horizon scheduler remaining execution owner
    ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds owner
      (execution.recall owner) (execution.observe app owner))
  have raw := menu.toRawTrace initial horizon scheduler trace
  obtain ⟨input, valid, _geometry⟩ :=
    currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler raw
  have visible : PhaseRuntimeState.requests (execution.observe app owner).application.2 owner
      coordinate.1 :=
    (PhaseRuntimeState.requests_publicView _ valid owner coordinate.1).mpr request
  have visibleBool : decide (PhaseRuntimeState.requests
      (execution.observe app owner).application.2 owner coordinate.1) = true :=
    decide_eq_true visible
  have clocks : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (idle.recall owner)).map Prod.fst =
      (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
        (execution.recall owner) (execution.observe app owner)).activationClocks ++
      [(PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
        (execution.recall owner) (execution.observe app owner)).elapsed] := by
    simp only [idle, ReactiveApplication.Execution.respond, PhaseSeedScheduler.ownerWord,
      List.filter_append, List.filter_cons, List.filter_nil, List.map_append, List.map_cons,
      List.map_nil, visibleBool, ite_true, PhaseSeedScheduler.informationInput]
  have networkUnsent := PhaseSeedCalendar.network_unsent_of_information runtime leaks initial
    bounds horizon scheduler remaining owner execution trace coordinate unsent
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
  have queryInputs := unsent_queried_input runtime leaks priority decideLocal seeds.1 coordinate
    owner request.2.2.2.1 scheduler menu.uniformResponses idle.environmentRecall.length
    (PhaseRuntimeState.initial plan initialInput) idle reached networkUnsent
  rw [clocks] at queryInputs
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
  have restored : (((controller runtime leaks priority decideLocal).coordinateTranscriptFrom seeds.1
      coordinate [] idle.environmentRecall).map (counterEntry runtime leaks counterLeaks owner)).map
        (restoreCounterEntry runtime leaks counterLeaks owner
          ((PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
            (idle.recall owner)).map Prod.fst)) =
      (controller runtime leaks priority decideLocal).coordinateTranscriptFrom seeds.1 coordinate []
        idle.environmentRecall := by
    rw [List.map_map]
    calc
      _ = List.map id _ := by
        apply List.map_congr_left
        intro item member
        have canonical := queryInputs item member
        rw [← clocks] at canonical
        rcases unresolved item member with activated | waited
        · simp only [Function.comp_def, restoreCounterEntry, counterEntry, ite_eq_left activated]
          exact Prod.ext canonical.symm activated.symm
        · simp only [Function.comp_def, restoreCounterEntry, counterEntry, waited, reduceCtorEq,
            ite_false]
          exact Prod.ext canonical.symm waited.symm
      _ = _ := List.map_id _
  rw [clocks] at restored
  simpa only [idle, (app).respond_environmentRecall] using
    And.intro counted ⟨positives, exhaustionCount, restored⟩

/-- Complete owner information recovers the whole actual unsent query
transcript, for arbitrary original remainder and local seeds. Consequently
every candidate seed has the same filter throughout that information fiber. -/
theorem unsent_information_transcript
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (timed : DeadlineExpiry runtime decideLocal)
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
    (same : (first.recall owner, first.observe app owner) =
      (second.recall owner, second.observe app owner))
    (unsent : ∀ message ∈ (app).outputs (first.recall owner),
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false) :
    (controller runtime leaks priority decideLocal).coordinateTranscriptFrom firstSeeds.1 coordinate
        [] first.environmentRecall =
      (controller runtime leaks priority decideLocal).coordinateTranscriptFrom secondSeeds.1
        coordinate [] second.environmentRecall ∧
    ∀ candidate, (controller runtime leaks priority decideLocal).coordinateConsistentFrom
        firstSeeds.1 coordinate candidate [] first.environmentRecall ↔
      (controller runtime leaks priority decideLocal).coordinateConsistentFrom secondSeeds.1
        coordinate candidate [] second.environmentRecall := by
  classical
  let alphabet : MessageNetwork.ObservationRule Player (WitnessedPacket graph) :=
    fun _ _ => PMF.pure ∅
  have samePast : first.recall owner = second.recall owner := congrArg Prod.fst same
  have secondUnsent : ∀ message ∈ (app).outputs (second.recall owner),
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false := by
    rw [← samePast]
    exact unsent
  have inputEq := congrArg (fun pair : List (app).PlayerEntry × (app).PlayerView =>
    PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner pair.1 pair.2) same
  obtain ⟨firstCounted, firstClocks, firstWaits, firstRestore⟩ :=
    active_unsent_transcript_signature runtime leaks alphabet priority decideLocal timed firstSeeds
      bounds plan ordered maximal inputs horizon firstRemaining owner first firstTrace coordinate
        firstRequest unsent
  obtain ⟨secondCounted, secondClocks, secondWaits, secondRestore⟩ :=
    active_unsent_transcript_signature runtime leaks alphabet priority decideLocal timed secondSeeds
      bounds plan ordered maximal inputs horizon secondRemaining owner second secondTrace coordinate
        secondRequest secondUnsent
  rw [inputEq] at firstClocks firstWaits firstRestore
  have emptyLog (items : List (PhaseSeedOperationalInput graph × (app).Command)) :
      ∀ entry ∈ items.map (counterEntry runtime leaks alphabet owner),
        entry.query.input.emitted = [] := by
    intro entry member
    obtain ⟨item, _member, rfl⟩ := List.mem_map.mp member
    rfl
  have unresolvedLog (items : List (PhaseSeedOperationalInput graph × (app).Command)) :
      ∀ entry ∈ items.map (counterEntry runtime leaks alphabet owner),
        entry.reply = .activation ∨ entry.reply = .exhausted := by
    intro entry member
    obtain ⟨item, _member, rfl⟩ := List.mem_map.mp member
    dsimp only [counterEntry]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have sameLogs := firstCounted.eq_of_unsent_signature secondCounted (emptyLog _) (emptyLog _)
    (unresolvedLog _) (unresolvedLog _) (firstClocks.trans secondClocks.symm)
      (firstWaits.trans secondWaits.symm)
  have restored := congrArg (List.map (restoreCounterEntry runtime leaks alphabet owner
    ((PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
      (second.recall owner) (second.observe app owner)).activationClocks ++
      [(PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
        (second.recall owner) (second.observe app owner)).elapsed]))) sameLogs
  rw [firstRestore, secondRestore] at restored
  refine ⟨restored, ?_⟩
  intro candidate
  simp only [ReactiveApplication.AddressedScheduler.coordinateConsistentFrom_iff_transcript,
    restored]

end Vegas.EventGraphRuntime.PhaseServiceScheduler
