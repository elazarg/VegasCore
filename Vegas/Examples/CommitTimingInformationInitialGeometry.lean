/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.CommitTimingInformationService
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseReadyRequests
import Vegas.Pending.PhaseBindingInertResponse
import Vegas.Pending.EventInitialObservation

/-! # Concrete initial phase geometry of the hidden-input timing game -/

noncomputable section

namespace Vegas.Examples.CommitTimingInformation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

private theorem binding_layouts :
    graph.outputLayout (bindingEvent alice) = .binding alice .bool ∧
      graph.outputLayout (bindingEvent bob) = .binding bob .bool := by
  constructor <;> rfl

private theorem reveal_layouts :
    graph.outputLayout (revealEvent alice) = .publication .bool ∧
      graph.outputLayout (revealEvent bob) = .publication .bool := by
  constructor <;> rfl

theorem binding_predecessors (owner : Player) :
    graph.order.predecessors (bindingEvent owner) = ∅ := by
  fin_cases owner <;> decide

def commitmentPhase : RuntimePhase graph where
  kind := .commitment
  low := 0
  high := 2
  nonempty := by decide
  bounded := by decide
  fields event lower upper := by
    fin_cases event
    · exact ⟨alice, .bool, rfl⟩
    · exact ⟨bob, .bool, rfl⟩
    · change 2 < 2 at upper
      omega
    · change 3 < 2 at upper
      omega
  sample_singleton impossible := by cases impossible

def publicationPhase : RuntimePhase graph where
  kind := .reveal
  low := 2
  high := 4
  nonempty := by decide
  bounded := by decide
  fields event lower upper := by
    fin_cases event
    · change 2 ≤ 0 at lower
      omega
    · change 2 ≤ 1 at lower
      omega
    · exact ⟨.bool, rfl⟩
    · exact ⟨.bool, rfl⟩
  sample_singleton impossible := by cases impossible

private theorem phase_kind_at_binding (phase : RuntimePhase graph)
    (event : graph.EventId) (owner : Player)
    (output : graph.outputLayout event = .binding owner .bool)
    (lower : phase.low ≤ event.val) (upper : event.val < phase.high) :
    phase.kind = .commitment := by
  have matching := phase.fields event lower upper
  rw [output] at matching
  cases kind : phase.kind <;> simp_all [RuntimePhaseKind.Matches]

private theorem phase_kind_at_publication (phase : RuntimePhase graph)
    (event : graph.EventId) (output : graph.outputLayout event = .publication .bool)
    (lower : phase.low ≤ event.val) (upper : event.val < phase.high) :
    phase.kind = .reveal := by
  have matching := phase.fields event lower upper
  rw [output] at matching
  cases kind : phase.kind <;> simp_all [RuntimePhaseKind.Matches]

/-- The actual chosen maximal compiled partition has these two concrete blocks. -/
theorem plan_phases : plan.phases = [commitmentPhase, publicationPhase] := by
  classical
  have adjacent := plan.adjacent
  have maximal := compiledRuntimePhasePlan_maximal program .concurrentReveals
  change plan.phases.IsChain _ at maximal
  cases phases : plan.phases with
  | nil =>
      have impossible := plan.empty phases
      change 4 = 0 at impossible
      omega
  | cons first rest =>
      have firstLow : first.low = 0 := plan.first first (by simp [phases])
      have firstKind : first.kind = .commitment :=
        phase_kind_at_binding first (bindingEvent alice) alice binding_layouts.1
          (by simp [firstLow, bindingEvent, alice]) (by
            change 0 < first.high
            have := first.nonempty
            omega)
      have firstHigh : first.high ≤ 2 := by
        by_contra beyond
        have matching := first.fields (revealEvent alice) (by simp [firstLow, revealEvent, alice])
          (by change 2 < first.high; omega)
        rw [firstKind, reveal_layouts.1] at matching
        simp only [RuntimePhaseKind.Matches] at matching
        obtain ⟨owner, payload, impossible⟩ := matching
        cases impossible
      cases rest with
      | nil =>
          have last := plan.last first (by simp [phases])
          change first.high = 4 at last
          omega
      | cons second rest =>
          rw [phases] at adjacent maximal
          have nextLow := (List.isChain_cons_cons.mp adjacent).1
          have different := (List.isChain_cons_cons.mp maximal).1
          have firstEnd : first.high = 2 := by
            by_contra unequal
            have one : first.high = 1 := by have := first.nonempty; omega
            have secondKind : second.kind = .commitment :=
              phase_kind_at_binding second (bindingEvent bob) bob binding_layouts.2
                (by change second.low ≤ 1; omega) (by
                  change 1 < second.high
                  have := second.nonempty
                  omega)
            rcases different with unequalKind | sampled
            · exact unequalKind (firstKind.trans secondKind.symm)
            · rw [firstKind] at sampled
              cases sampled
          have secondLow : second.low = 2 := by omega
          have secondKind : second.kind = .reveal :=
            phase_kind_at_publication second (revealEvent alice) reveal_layouts.1
              (by simp [secondLow, revealEvent, alice]) (by
                change 2 < second.high
                have := second.nonempty
                omega)
          cases rest with
          | nil =>
              have last := plan.last second (by simp [phases])
              change second.high = 4 at last
              have firstEq : first = commitmentPhase := by
                cases first
                simp_all [commitmentPhase]
              have secondEq : second = publicationPhase := by
                cases second
                simp_all [publicationPhase]
              rw [firstEq, secondEq]
          | cons third rest =>
              have nextAdjacent :=
                (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp adjacent).2).1
              have nextDifferent :=
                (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp maximal).2).1
              have thirdBound : third.high ≤ 4 := third.bounded
              have endThree : second.high = 3 := by
                have := second.nonempty
                have := third.nonempty
                omega
              have thirdKind : third.kind = .reveal :=
                phase_kind_at_publication third (revealEvent bob) reveal_layouts.2
                  (by change third.low ≤ 3; omega) (by
                    change 3 < third.high
                    have := third.nonempty
                    omega)
              rcases nextDifferent with unequalKind | sampled
              · exact (unequalKind (secondKind.trans thirdKind.symm)).elim
              · rw [secondKind] at sampled
                cases sampled

theorem initialState_eq (bit : Bool) : initialState bit =
    ⟨[commitmentPhase, publicationPhase], 0,
      ⟨State.initial (encodeInputs (sourceInitial bit)), ∅⟩,
      ⟨State.initial (encodeInputs (sourceInitial bit)), ∅⟩, []⟩ := by
  classical
  let native : EventGraphRuntime.State graph :=
    EventGraphRuntime.State.initial (encodeInputs (sourceInitial bit))
  have drained : commitmentPhase.drain (⟨native, ∅⟩ : RecoveryState graph) = ⟨native, ∅⟩ := by
    apply RuntimePhase.drain_eq_of_clear
    intro event eligible
    rcases eligible.2 with ⟨_ready, excluded⟩
    cases actor : graph.actor? event <;> simp [actor] at excluded
  have unfinished : ¬ commitmentPhase.Finished (⟨native, ∅⟩ : RecoveryState graph) := by
    intro finished
    have inside : bindingEvent alice ∈ commitmentPhase.events := by
      apply (RuntimePhase.mem_events commitmentPhase _).mpr
      change 0 ≤ 0 ∧ 0 < 2
      omega
    have member := finished inside
    change bindingEvent alice ∈ (EventOrder.Cut.empty graph.order).completed at member
    exact Finset.notMem_empty _ member
  change PhaseRuntimeState.settle plan.phases 0 ⟨native, ∅⟩ ⟨native, ∅⟩ [] = _
  rw [plan_phases, PhaseRuntimeState.settle, drained, ite_eq_right unfinished]

theorem initialState_attempt (bit : Bool) : (initialState bit).attempt = originalAttempt := by
  rw [initialState_eq]
  rfl

theorem initial_binding_request (bit : Bool) (owner : Player) :
    (initialState bit).SeedRequest owner (originalCoordinate owner) := by
  rw [initialState_eq]
  refine ⟨rfl, ⟨commitmentPhase, rfl, ?_⟩, ?_, bindingEvent_actor owner, ?_⟩
  · apply (RuntimePhase.mem_events commitmentPhase _).mpr
    change 0 ≤ owner.val ∧ owner.val < 2
    exact ⟨Nat.zero_le _, owner.isLt⟩
  · constructor
    · change bindingEvent owner ∉ (∅ : Finset graph.EventId)
      exact Finset.notMem_empty _
    · change graph.order.predecessors (bindingEvent owner) ⊆ (∅ : Finset graph.EventId)
      rw [binding_predecessors]
  · simp

theorem initial_bindings_ready (bit : Bool) (owner : Player) :
    ready owner (bindingEvent owner) ((initialExecution bit).observeEnvironment app) = true := by
  classical
  simp only [ready, decide_eq_true_eq]
  change PhaseRuntimeState.requests (initialState bit).publicView owner
    ⟨(initialState bit).attempt, bindingEvent owner⟩
  rw [initialState_attempt]
  have valid := (PhaseRuntimeState.initial_invariant plan
    (encodeInputs (sourceInitial bit))).1
  exact ((initialState bit).requests_publicView valid owner _).mpr
    (initial_binding_request bit owner)

/-- The quiet state at a physical clock, with the original hidden input retained. -/
def quietApplication (bit : Bool) (clock : Nat) : app.State :=
  { initialState bit with current := { (initialState bit).current with native :=
      { (initialState bit).current.native with clock := clock } } }

theorem quietApplication_normalize (bit : Bool) (clock : Nat) :
    (quietApplication bit clock).normalize = quietApplication bit clock := by
  let native : EventGraphRuntime.State graph :=
    { State.initial (encodeInputs (sourceInitial bit)) with clock := clock }
  have shaped : quietApplication bit clock =
      ⟨[commitmentPhase, publicationPhase], 0,
        ⟨State.initial (encodeInputs (sourceInitial bit)), ∅⟩,
        ⟨native, ∅⟩, []⟩ := by rw [quietApplication, initialState_eq]
  have drained : commitmentPhase.drain (⟨native, ∅⟩ : RecoveryState graph) = ⟨native, ∅⟩ := by
    apply RuntimePhase.drain_eq_of_clear
    intro event eligible
    rcases eligible.2 with ⟨_ready, excluded⟩
    cases actor : graph.actor? event <;> simp [actor] at excluded
  have unfinished : ¬ commitmentPhase.Finished (⟨native, ∅⟩ : RecoveryState graph) := by
    intro finished
    have inside : bindingEvent alice ∈ commitmentPhase.events := by
      apply (RuntimePhase.mem_events commitmentPhase _).mpr
      change 0 ≤ 0 ∧ 0 < 2
      omega
    have member := finished inside
    change bindingEvent alice ∈ (∅ : Finset graph.EventId) at member
    exact Finset.notMem_empty _ member
  rw [shaped, PhaseRuntimeState.normalize, PhaseRuntimeState.settle, drained,
    ite_eq_right unfinished]

end Vegas.Examples.CommitTimingInformation
