/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseApplication

/-! # Finite seed allocation from permanent exclusions

Every retry consumes a newly excluded owner. The exclusion set is permanent
although source outputs are rolled back. This gives an actual application
invariant bounding the generation of every addressed seed request.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- A retry generation is charged to permanent exclusions, independently of
rollback of the current source store and binding registry. -/
structure SeedBudget (state : PhaseRuntimeState graph) : Prop where
  generation : state.generation ≤ state.entry.excluded.card
  excluded : state.entry.excluded ⊆ state.current.excluded

private theorem fresh_failure_card (entry current : RecoveryState graph)
    (owners : Finset Player) (monotone : entry.excluded ⊆ current.excluded)
    (fresh : ((current.excluded \ entry.excluded) ∩ owners).Nonempty) :
    entry.excluded.card + 1 ≤ current.excluded.card := by
  obtain ⟨owner, member⟩ := fresh
  obtain ⟨newMember, _⟩ := Finset.mem_inter.mp member
  obtain ⟨currentMember, absent⟩ := Finset.mem_sdiff.mp newMember
  have inserted : insert owner entry.excluded ⊆ current.excluded :=
    Finset.insert_subset_iff.mpr ⟨currentMember, monotone⟩
  have count := Finset.card_le_card inserted
  rwa [Finset.card_insert_of_notMem absent] at count

theorem settle_seedBudget (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (bounded : generation ≤ entry.excluded.card)
    (monotone : entry.excluded ⊆ current.excluded) :
    (settle phases generation entry current retired).SeedBudget := by
  induction phases generalizing generation entry current retired with
  | nil => exact ⟨bounded, monotone⟩
  | cons phase remaining ih =>
      have currentBound : generation ≤ current.excluded.card :=
        bounded.trans (Finset.card_le_card monotone)
      have drainedBound : generation ≤ (phase.drain current).excluded.card := by
        simpa only [phase.drain_excluded] using currentBound
      simp only [settle]
      split
      · rename_i finished
        split
        · rename_i failed
          have resetBound : generation + 1 ≤ (phase.drain current).excluded.card := by
            have growth := fresh_failure_card entry (phase.drain current) phase.owners
              (by simpa only [phase.drain_excluded] using monotone) failed.2
            omega
          split
          · refine ⟨?_, ?_⟩
            · simpa only [restore] using resetBound
            · simp only [restore, phase.drain_excluded]
              exact Finset.Subset.refl _
          · apply ih
            · simpa only [phase.drain_excluded, restore] using currentBound
            · exact Finset.Subset.refl _
        · exact ih _ _ _ _ drainedBound (Finset.Subset.refl _)
      · refine ⟨bounded, ?_⟩
        simpa only [phase.drain_excluded] using monotone

theorem initial_seedBudget (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).SeedBudget :=
  settle_seedBudget _ _ _ _ _ (Nat.zero_le _) (Finset.Subset.refl _)

omit [DecidableEq Player] in
theorem SeedBudget.current_generation {state : PhaseRuntimeState graph}
    (valid : state.SeedBudget) : state.generation ≤ state.current.excluded.card :=
  valid.generation.trans (Finset.card_le_card valid.excluded)

omit [DecidableEq Player] in
/-- The finite owner set bounds every actual retry generation. -/
theorem SeedBudget.generation_le_card [Fintype Player] {state : PhaseRuntimeState graph}
    (valid : state.SeedBudget) : state.generation ≤ Fintype.card Player :=
  valid.current_generation.trans (Finset.card_le_univ _)

end PhaseRuntimeState

/-- The seed budget is preserved by genuine submissions, accepted packets and
actual supported environment commands of the reset-aware application. -/
theorem phaseApplication_seedBudget (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.SeedBudget where
  submit state who submission valid := ⟨valid.generation, valid.excluded⟩
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      apply PhaseRuntimeState.settle_seedBudget
      · exact valid.generation
      · exact valid.excluded.trans (state.current.inclusionResult_excluded_subset _ native)
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, reached, rfl⟩ := reached
      apply PhaseRuntimeState.settle_seedBudget
      · exact valid.generation
      · exact valid.excluded.trans (state.current.environmentResult_excluded_subset command native)
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- A finite carrier of the existing physical attempt/event coordinates. -/
def BoundedAttemptEvent (graph : Vegas.EventGraph Player L) (maximum : Nat) :=
  {coordinate : CommitAttemptEvent graph //
    coordinate.attempt.phase < graph.order.eventCount ∧ coordinate.attempt.generation ≤ maximum}

namespace BoundedAttemptEvent

variable (maximum : Nat)

def encode (coordinate : BoundedAttemptEvent graph maximum) :
    Fin graph.order.eventCount × Fin (maximum + 1) × graph.EventId :=
  (⟨coordinate.1.attempt.phase, coordinate.2.1⟩,
    ⟨coordinate.1.attempt.generation, Nat.lt_succ_iff.mpr coordinate.2.2⟩, coordinate.1.event)

omit [DecidableEq Player] in
theorem encode_injective : Function.Injective (encode (graph := graph) maximum) := by
  intro first second same
  rcases first with ⟨⟨⟨firstPhase, firstGeneration⟩, firstEvent⟩, firstBound⟩
  rcases second with ⟨⟨⟨secondPhase, secondGeneration⟩, secondEvent⟩, secondBound⟩
  simp only [encode, Prod.mk.injEq, Fin.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl⟩
  rfl

omit [DecidableEq Player] in
instance : Finite (BoundedAttemptEvent graph maximum) :=
  Finite.of_injective (encode maximum) (encode_injective maximum)

omit [DecidableEq Player] in
instance : Fintype (BoundedAttemptEvent graph maximum) := Fintype.ofFinite _

instance : DecidableEq (BoundedAttemptEvent graph maximum) := inferInstanceAs
  (DecidableEq {coordinate : CommitAttemptEvent graph //
    coordinate.attempt.phase < graph.order.eventCount ∧ coordinate.attempt.generation ≤ maximum})

end BoundedAttemptEvent

namespace PhaseRuntimeState

omit [DecidableEq Player] in
/-- Every actual nonexcluded ready request has a coordinate in the fixed finite
original seed product. No seed allocation premise is required from the scheduler. -/
theorem SeedRequest.bounded [Fintype Player] {state : PhaseRuntimeState graph}
    (budget : state.SeedBudget) {owner : Player} {coordinate : CommitAttemptEvent graph}
    (request : state.SeedRequest owner coordinate) :
    coordinate.attempt.phase < graph.order.eventCount ∧
      coordinate.attempt.generation ≤ Fintype.card Player := by
  obtain ⟨phase, member, inPhase⟩ := request.2.1
  have head : state.phases.head? = some phase := Option.mem_def.mp member
  constructor
  · have phaseBound : phase.low < graph.order.eventCount :=
      phase.nonempty.trans_le phase.bounded
    simpa only [request.1, attempt, head, Option.map_some, Option.getD_some] using phaseBound
  · simpa only [request.1, attempt] using budget.generation_le_card

def SeedRequest.coordinate [Fintype Player] {state : PhaseRuntimeState graph}
    (budget : state.SeedBudget) {owner : Player} {coordinate : CommitAttemptEvent graph}
    (request : state.SeedRequest owner coordinate) :
    BoundedAttemptEvent graph (Fintype.card Player) := ⟨coordinate, request.bounded budget⟩

end PhaseRuntimeState
end Vegas.EventGraphRuntime
