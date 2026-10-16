/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceTranscriptOrder
import Interaction.ReactiveRecordedEnvironmentPrefix

/-! # Exact actual WAIT counters at original phased queries -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- An actual query's elapsed clock is exactly the number of earlier WAIT
records for its address. The count is derived from initialized history,
coverage of every earlier tick and permanent same-tick closure. -/
theorem recorded_query_wait_count
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
    (actor : graph.actor? coordinate.1.event = some owner)
    (before : List (app).EnvironmentEntry) (entry : (app).EnvironmentEntry)
    (after : List (app).EnvironmentEntry)
    (recorded : execution.environmentRecall = before ++ entry :: after)
    (query : PhaseSeedOperationalInput graph)
    (queried : (controller runtime leaks priority decideLocal).request seeds.1 before
      entry.beforeView = some (coordinate, query)) :
    (waitClocks runtime leaks priority decideLocal seeds.1 coordinate before).length =
      query.elapsed := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let scheduler := (controller runtime leaks priority decideLocal).family seeds
  obtain ⟨used, prior, _within, ⟨priorTrace⟩, priorSupport, priorRecall, viewEq⟩ :=
    menu.recorded_environment_prefix initial horizon scheduler remaining execution trace before
      entry after recorded
  have requested : (controller runtime leaks priority decideLocal).request seeds.1
      prior.environmentRecall (prior.observeEnvironment app) = some (coordinate, query) := by
    rw [priorRecall, ← viewEq]
    exact queried
  have rawPrior := menu.toRawTrace initial horizon scheduler priorTrace
  obtain ⟨input, valid, _geometry⟩ :=
    currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler rawPrior
  obtain ⟨principal, request⟩ := request_sound runtime leaks priority decideLocal seeds.1 prior
    valid requested
  have principalEq : principal = owner := Option.some.inj (request.2.2.2.1.symm.trans actor)
  subst principal
  obtain ⟨entered, stamp⟩ := valid.active.activatedAt_eq_some_of_ready_actor coordinate.1.event
    request.2.2.1 (by simp only [actor, Option.isSome_some])
  have started := valid.active.activated_le coordinate.1.event entered stamp
  have queryInput := request_query runtime leaks priority decideLocal seeds.1 prior coordinate
    owner actor query requested
  have elapsedEq : query.elapsed = prior.application.current.native.clock - entered := by
    rw [queryInput]
    change prior.application.current.native.clock -
      (prior.application.current.native.activatedAt coordinate.1.event).getD
        prior.application.current.native.clock = _
    rw [stamp, Option.getD_some]
  let clocks := waitClocks runtime leaks priority decideLocal seeds.1 coordinate before
  have unique : clocks.Nodup := by
    obtain ⟨state, stateSupported, reached⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ priorSupport)
    obtain ⟨initialInput, _supported, rfl⟩ := PMF.support_map .. ▸ stateSupported
    have nodup := runRounds_waitClocks_nodup runtime leaks priority decideLocal seeds plan
      initialInput menu.uniformResponses used prior reached coordinate owner actor
    rwa [priorRecall] at nodup
  have fullSupport := menu.roundSupported_uniform initial horizon scheduler trace
  obtain ⟨state, stateSupported, reached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ fullSupport.2)
  obtain ⟨initialInput, _supported, rfl⟩ := PMF.support_map .. ▸ stateSupported
  have earlier (tick : Nat) (member : tick ∈ clocks) : tick < query.elapsed := by
    obtain ⟨oldQuery, oldMember, oldClock⟩ :=
      (waitClocks_mem_iff runtime leaks priority decideLocal seeds.1 coordinate before
        tick).mp member
    obtain ⟨oldBefore, oldEntry, oldAfter, oldRecorded, oldRequested, oldCommand⟩ :=
      (ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom_mem_iff
        (controller runtime leaks priority decideLocal) seeds.1 coordinate [] before
          (oldQuery, .wait)).mp oldMember
    simp only [List.nil_append] at oldRequested
    have oldPrefix : oldBefore ++ [oldEntry] ++ oldAfter = before := by
      simpa only [List.append_assoc, List.singleton_append] using oldRecorded.symm
    have chronological : execution.environmentRecall =
        (oldBefore ++ [oldEntry] ++ oldAfter) ++ entry :: after := by
      rw [oldPrefix]
      exact recorded
    have laterRequested : (controller runtime leaks priority decideLocal).request seeds.1
        (oldBefore ++ [oldEntry] ++ oldAfter) entry.beforeView = some (coordinate, query) := by
      rw [oldPrefix]
      exact queried
    have strictlyEarlier := recorded_queries_elapsed_strict_after_nonactivation runtime leaks
      priority decideLocal seeds plan initialInput menu.uniformResponses
      execution.environmentRecall.length execution reached coordinate owner actor oldBefore
        oldEntry oldAfter entry after chronological oldQuery query oldRequested laterRequested
          (by rw [oldCommand]; rfl)
    omega
  have covered (tick : Nat) (lower : tick < query.elapsed) : tick ∈ clocks := by
    have earlierTick : entered + tick < prior.application.current.native.clock := by omega
    obtain ⟨oldQuery, oldMember, oldClock⟩ := past_wait_query_of_tickExhaustion runtime leaks
      priority decideLocal timed seeds bounds plan ordered maximal inputs horizon (horizon - used)
        prior priorTrace coordinate owner request entered stamp (entered + tick) (by omega)
          earlierTick
    apply (waitClocks_mem_iff runtime leaks priority decideLocal seeds.1 coordinate before tick).mpr
    refine ⟨oldQuery, ?_, by omega⟩
    rwa [priorRecall] at oldMember
  have exactSet : clocks.toFinset = Finset.range query.elapsed := by
    ext tick
    simp only [List.mem_toFinset, Finset.mem_range]
    exact ⟨earlier tick, covered tick⟩
  have count := congrArg Finset.card exactSet
  simpa only [List.toFinset_card_of_nodup unique, Finset.card_range] using count

end Vegas.EventGraphRuntime.PhaseServiceScheduler
