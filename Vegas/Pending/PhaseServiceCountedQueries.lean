/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceQueryWaitCount
import Vegas.Pending.ReactiveLocalSeedLogRecovery

/-! # Original phased transcripts instantiate the existing counted query log -/

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

open Classical in
/-- Counter-only encoding into the existing log alphabet. Its resolution
command carrier and observation rule are unused; no execution law is changed. -/
def counterEntry (owner : Player)
    (item : PhaseSeedOperationalInput graph × (app).Command) :
    LocalSeedEntry graph (counterApp).Command :=
  ⟨⟨⟨item.1.elapsed, []⟩, item.1.activationClocks.length⟩,
    if item.2 = .activate owner then .activation else .exhausted⟩

omit [Fintype Player] in
open Classical in
/-- The positive-clock projection is unchanged by the counter encoding. -/
theorem counterEntry_positive_clocks (owner : Player)
    (items : List (PhaseSeedOperationalInput graph × (app).Command)) :
    (positiveQueries (items.map (counterEntry runtime leaks counterLeaks owner))).map
        (fun query => query.input.elapsed) =
      (items.filter fun item => decide (item.2 = .activate owner)).map
        (fun item => item.1.elapsed) := by
  classical
  induction items with
  | nil => rfl
  | cons item later ih =>
      by_cases activated : item.2 = .activate owner
      · simp only [List.map_cons, positiveQueries, List.filterMap_cons, counterEntry,
          ite_eq_left activated, List.map_cons, List.filter_cons, decide_eq_true activated,
          ite_true] at ih ⊢
        exact congrArg (item.1.elapsed :: ·) ih
      · simp only [List.map_cons, positiveQueries, List.filterMap_cons, counterEntry,
          ite_eq_right activated, List.filter_cons, decide_eq_false activated, Bool.false_eq_true,
          ite_false] at ih ⊢
        exact ih

omit [Fintype Player] in
open Classical in
private theorem counterEntry_positive_count (owner : Player)
    (items : List (PhaseSeedOperationalInput graph × (app).Command)) :
    (positiveQueries (items.map (counterEntry runtime leaks counterLeaks owner))).length =
      (items.filter fun item => decide (item.2 = .activate owner)).length := by
  have same := congrArg List.length
    (counterEntry_positive_clocks runtime leaks counterLeaks owner items)
  simpa only [List.length_map] using same

omit [Fintype Player] in
open Classical in
/-- The exhaustion projection records exactly the original WAIT clocks. -/
theorem counterEntry_exhausted (owner : Player)
    (items : List (PhaseSeedOperationalInput graph × (app).Command))
    (unresolved : ∀ item ∈ items, item.2 = .activate owner ∨ item.2 = .wait) :
    exhaustedClocks (items.map (counterEntry runtime leaks counterLeaks owner)) =
      items.filterMap (fun item => if item.2 = .wait then some item.1.elapsed else none) := by
  classical
  revert unresolved
  induction items with
  | nil => intro _; rfl
  | cons item later ih =>
      intro unresolved
      have rest := ih (fun next member => unresolved next (List.mem_cons_of_mem _ member))
      rcases unresolved item (List.mem_cons_self) with activated | waited
      · simp only [List.map_cons, exhaustedClocks, List.filterMap_cons, counterEntry,
          activated, reduceCtorEq, ite_false]
        exact rest
      · simp only [List.map_cons, exhaustedClocks, List.filterMap_cons, counterEntry,
          waited, reduceCtorEq, ite_false, ite_true]
        exact congrArg (item.1.elapsed :: ·) rest

/-- Every original counted history with a surviving requested coordinate
produces a genuinely counted log in the existing recovery API. Both counters
come from actual query occurrences, not a supplied log-validity premise. -/
theorem history_countedQueryLog
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (timed : DeadlineExpiry runtime decideLocal)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon remaining : Nat) (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks priority decideLocal).family seeds)).Trace
        (some ⟨remaining, none, execution⟩))
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (request : execution.application.SeedRequest owner coordinate.1) :
    CountedQueryLog (((controller runtime leaks priority decideLocal).coordinateTranscriptFrom
      seeds.1 coordinate [] execution.environmentRecall).map
        (counterEntry runtime leaks counterLeaks owner)) := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let driver := controller runtime leaks priority decideLocal
  let scheduler := driver.family seeds
  have fullSupport := menu.roundSupported_uniform initial horizon scheduler trace
  obtain ⟨state, stateSupported, reached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ fullSupport.2)
  obtain ⟨initialInput, _supported, rfl⟩ := PMF.support_map .. ▸ stateSupported
  have extend (before later : List (app).EnvironmentEntry)
      (recalled : execution.environmentRecall = before ++ later)
      (counted : CountedQueryLog ((driver.coordinateTranscriptFrom seeds.1 coordinate [] before).map
        (counterEntry runtime leaks counterLeaks owner))) :
      CountedQueryLog ((driver.coordinateTranscriptFrom seeds.1 coordinate []
        execution.environmentRecall).map (counterEntry runtime leaks counterLeaks owner)) := by
    induction later generalizing before with
    | nil =>
        rw [List.append_nil] at recalled
        rw [recalled]
        exact counted
    | cons entry later ih =>
        have unresolved : ∀ item ∈ driver.coordinateTranscriptFrom seeds.1 coordinate [] before,
            item.2 = .activate owner ∨ item.2 = .wait := by
          intro item member
          apply queried_activate_or_wait runtime leaks priority decideLocal timed seeds bounds plan
            ordered maximal inputs horizon remaining execution trace coordinate owner request item
          rw [recalled, ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom_append]
          exact List.mem_append_left _ member
        have nextCounted : CountedQueryLog ((driver.coordinateTranscriptFrom seeds.1 coordinate []
            (before ++ [entry])).map (counterEntry runtime leaks counterLeaks owner)) := by
          rw [ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom_append,
            List.map_append]
          simp only [List.nil_append,
            ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom]
          cases queried : driver.request seeds.1 before entry.beforeView with
          | none => simpa only [List.map_nil, List.append_nil] using counted
          | some selected =>
              rcases selected with ⟨selected, query⟩
              by_cases same : selected = coordinate
              · subst selected
                simp only [ite_true, List.map_cons, List.map_nil]
                apply CountedQueryLog.append counted
                  (counterEntry runtime leaks counterLeaks owner (query, entry.command))
                · rw [counterEntry_exhausted runtime leaks counterLeaks owner _ unresolved]
                  exact (recorded_query_wait_count runtime leaks priority decideLocal timed seeds
                    bounds plan ordered maximal inputs horizon remaining execution trace coordinate
                      owner request.2.2.2.1 before entry later recalled query queried).symm
                · change query.activationClocks.length = _
                  rw [counterEntry_positive_count runtime leaks counterLeaks owner]
                  have clocks := recorded_query_activationClocks runtime leaks priority decideLocal
                    seeds ordered plan initialInput menu.uniformResponses
                    execution.environmentRecall.length execution reached coordinate owner
                      request.2.2.2.1 before entry later recalled query queried
                  rw [clocks]
                  simp only [activationTranscript, List.length_map]
                  rfl
              · simpa only [ite_eq_right same, List.map_nil, List.append_nil] using counted
        apply ih (before ++ [entry])
        · simpa only [List.append_assoc, List.singleton_append] using recalled
        · exact nextCounted
  exact extend [] execution.environmentRecall (by simp) .empty

end Vegas.EventGraphRuntime.PhaseServiceScheduler
