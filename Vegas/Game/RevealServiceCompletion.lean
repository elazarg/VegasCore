/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceClock
import Vegas.Pending.ReactiveServiceCompletion
import Vegas.Pending.EventSequentialTiming
import Interaction.ReactiveRoundReachability

/-! # Settlement under arbitrary raw reveal-service play

Each ranked block waits a full relative deadline before its final expiry.
Events completed by arbitrary messages stay completed. If the current event
is still unfinished, its earlier activation time makes the expiry effective.
Induction over the actual plan therefore settles every source event without
assuming honest responses, reporting, successful monitoring, or equilibrium.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime GameTheory.Math.Probability
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The fixed scheduler executes the actual remaining plan, with its cursor
read from existing environment recall. This is an evaluation equation for the
native protocol; it changes neither histories nor information sets. -/
theorem suffix_rounds (watcher : Player)
    (players : Player → (application setup leaks).Policy)
    (before rest : List (ServiceInstruction (graph setup)))
    (split : plan setup watcher = before ++ rest)
    (execution : (application setup leaks).Execution)
    (position : execution.environmentRecall.length = before.length) :
    (application setup leaks).runRounds (scheduler setup leaks watcher) players rest.length
        execution =
      (runtime setup).runInteractionPlan leaks players ((runtime setup).reportNetwork leaks watcher)
        rest execution := by
  induction rest generalizing before execution with
  | nil => rfl
  | cons instruction rest ih =>
      have selected : (plan setup watcher)[before.length]? = some instruction := by
        rw [split, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      have step : (application setup leaks).round (scheduler setup leaks watcher) players
          execution = (runtime setup).interactionStep leaks players
            ((runtime setup).reportNetwork leaks watcher) instruction execution := by
        simp only [ReactiveApplication.round, scheduler, position, selected, interactionStep]
      rw [List.length_cons, ReactiveApplication.runRounds, step, runInteractionPlan]
      apply bind_congr_on_support _
      intro next supported
      apply ih (before ++ [instruction])
      · simpa only [List.append_assoc, List.singleton_append] using split
      · have advanced := (runtime setup).interactionStep_recall leaks players
          ((runtime setup).reportNetwork leaks watcher) instruction execution next supported
        simp only [List.length_append, List.length_singleton]
        omega

/-- Every finite-menu behavioral profile runs the same plan evaluator. This
covers C, W, effective and raw menus, including arbitrary off-profile play. -/
theorem menu_execution_law [Fintype Player]
    (responses : (application setup leaks).ResponseMenu) (watcher : Player)
    (profile : ∀ who, (responses.information (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).BehavioralPolicy who) :
    ((responses.information (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).runBehavioral profile
        (2 * horizon setup watcher + 1)).map History.state =
      (initialLaw setup).bind (fun state =>
        ((runtime setup).runInteractionPlan leaks
          (responses.decodeProfile (initialLaw setup) (horizon setup watcher)
            (scheduler setup leaks watcher) profile)
          ((runtime setup).reportNetwork leaks watcher) (plan setup watcher)
          (ReactiveApplication.Execution.initial (application setup leaks) state)).map
            (application setup leaks).finished) := by
  rw [InformationModel.runBehavioral, responses.run_eq_finish (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher) profile
    (2 * horizon setup watcher + 1) _ (Nat.le_refl _)]
  change (initialLaw setup).bind _ = _
  apply bind_congr_on_support _
  intro state _
  congr 1
  exact suffix_rounds setup leaks watcher _ [] (plan setup watcher) rfl _ rfl

/-- The current event settles within its block whenever all earlier events
have settled, regardless of the owner, watcher and network response policies. -/
theorem block_completes (watcher : Player) (reveals : setup.program.RevealOnly)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (inputs : (graph setup).Inputs)
    (event : (graph setup).EventId) (execution final : (application setup leaks).Execution)
    (invariant : execution.application.Invariant inputs)
    (previous : ∀ prior : (graph setup).EventId, prior.val < event.val →
      prior ∈ execution.application.config.cut.completed)
    (supported : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (block setup watcher event) execution).support) :
    event ∈ final.application.config.cut.completed := by
  have allProgress := (runtime setup).runInteractionPlan_facts leaks inputs players network
    (block setup watcher event) execution final invariant supported
  by_cases already : event ∈ execution.application.config.cut.completed
  · exact allProgress.completed already
  have ready : execution.application.config.cut.Ready event := by
    refine ⟨already, ?_⟩
    intro prior member
    exact previous prior ((EventOrder.sequential.mem_predecessors prior event).mp member)
  obtain ⟨owner, owned⟩ := source_owner setup reveals event
  have strategic : ((graph setup).actor? event).isSome = true := by rw [owned]; rfl
  obtain ⟨entered, activated⟩ :=
    invariant.activatedAt_eq_some_of_ready_actor event ready strategic
  let beforeExpiry : List (ServiceInstruction (graph setup)) :=
    [.grant event, .player owner, .includeLatest event owner, .player watcher, .wire] ++
      List.replicate (event.val + 1) .tick
  have blockEq : block setup watcher event = beforeExpiry ++ [.expire event] :=
    block_of_owner setup watcher owner event owned
  have ticks : serviceTicks beforeExpiry = (runtime setup).deadline event := by
    simp [beforeExpiry, serviceTicks, ServiceInstruction.ticks, runtime]
  rw [blockEq] at supported
  obtain ⟨prior, reached, expired, expiredAt, finished⟩ :=
    (runtime setup).runInteractionPlan_support_instruction leaks players network beforeExpiry []
      (.expire event) execution final supported
  have same : final = expired := (PMF.mem_support_pure_iff _ _).mp finished
  subst final
  have progress := (runtime setup).runInteractionPlan_facts leaks inputs players network
    beforeExpiry execution prior invariant reached
  have finalProgress := (runtime setup).interactionStep_facts leaks inputs players network
    (.expire event) prior expired progress.invariant expiredAt
  rcases progress.ready_or_completed event ready with completed | stillReady
  · exact finalProgress.completed completed
  · apply (runtime setup).interactionStep_expire_complete leaks players network event prior expired
      stillReady strategic entered (progress.activated event entered activated stillReady.1)
      _ expiredAt
    rw [progress.clock, ticks]
    exact invariant.due_after_deadline (runtime setup) event entered activated

/-- Every supported raw prefix has settled all source events assigned to its
completed blocks. Messages may additionally have settled later events. -/
theorem planPrefix_completed (watcher : Player) (reveals : setup.program.RevealOnly)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (inputs : (graph setup).Inputs)
    (execution : (application setup leaks).Execution)
    (invariant : execution.application.Invariant inputs)
    (rank : Nat) (within : rank ≤ (graph setup).order.eventCount)
    (final : (application setup leaks).Execution)
    (supported : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (planPrefix setup watcher rank) execution).support) :
    ∀ event : (graph setup).EventId, event.val < rank →
      event ∈ final.application.config.cut.completed := by
  induction rank generalizing final with
  | zero => intro event before; omega
  | succ rank ih =>
      have inside : rank < (graph setup).order.eventCount := by omega
      let current : (graph setup).EventId := ⟨rank, inside⟩
      rw [show rank + 1 = current.val + 1 from rfl, planPrefix_succ,
        (runtime setup).runInteractionPlan_append, PMF.support_bind] at supported
      obtain ⟨middle, reached, rest⟩ := Set.mem_iUnion₂.mp supported
      have previous := ih (by omega) middle reached
      have progress := (runtime setup).runInteractionPlan_facts leaks inputs players network
        (planPrefix setup watcher rank) execution middle invariant reached
      have blockProgress := (runtime setup).runInteractionPlan_facts leaks inputs players network
        (block setup watcher current) middle final progress.invariant rest
      have completed := block_completes setup leaks watcher reveals players network inputs current
        middle final progress.invariant previous rest
      intro event before
      by_cases same : event.val = rank
      · have identified : event = current := Fin.ext same
        simpa only [identified] using completed
      · exact blockProgress.completed (previous event (by omega))

/-- The full declared service settles the application under arbitrary raw
policies and network choices. Bounded protocol termination alone would not
establish this application-level settlement fact. -/
theorem plan_terminal (watcher : Player) (reveals : setup.program.RevealOnly)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (inputs : (graph setup).Inputs)
    (execution final : (application setup leaks).Execution)
    (invariant : execution.application.Invariant inputs)
    (supported : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (plan setup watcher) execution).support) : final.application.config.cut.Terminal := by
  have completePlan : planPrefix setup watcher (graph setup).order.eventCount =
      plan setup watcher := by
    apply congrArg (List.flatMap (block setup watcher))
    simpa only [List.length_finRange] using
      (List.take_length (l := List.finRange (graph setup).order.eventCount))
  have allEvents := planPrefix_completed setup leaks watcher reveals players network inputs
    execution invariant (graph setup).order.eventCount (Nat.le_refl _) final
      (by simpa only [completePlan] using supported)
  apply Finset.eq_univ_of_forall
  intro event
  exact allEvents event event.isLt

/-- Any remaining service suffix settles the application when its preceding
events are already complete. The starting execution may come from an arbitrary
history; neither its responses nor its network choices need be conformant. -/
theorem planSuffix_terminal (watcher : Player) (reveals : setup.program.RevealOnly)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (inputs : (graph setup).Inputs) (rank : Nat)
    (within : rank ≤ (graph setup).order.eventCount)
    (execution final : (application setup leaks).Execution)
    (invariant : execution.application.Invariant inputs)
    (previous : ∀ event : (graph setup).EventId, event.val < rank →
      event ∈ execution.application.config.cut.completed)
    (supported : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (((List.finRange (graph setup).order.eventCount).drop rank).flatMap
        (block setup watcher)) execution).support) :
    final.application.config.cut.Terminal := by
  induction within using Nat.decreasingInduction generalizing execution with
  | self =>
      have empty : (List.finRange (graph setup).order.eventCount).drop
          (graph setup).order.eventCount = [] := by simp
      rw [empty, List.flatMap_nil] at supported
      have same : final = execution := (PMF.mem_support_pure_iff _ _).mp supported
      subst final
      apply Finset.eq_univ_of_forall
      intro event
      exact previous event event.isLt
  | of_succ rank inside ih =>
      let current : (graph setup).EventId := ⟨rank, inside⟩
      have split : (List.finRange (graph setup).order.eventCount).drop rank =
          current :: (List.finRange (graph setup).order.eventCount).drop (rank + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using inside)]
        simp only [List.getElem_finRange, current]
        congr 1
      rw [split, List.flatMap_cons, (runtime setup).runInteractionPlan_append,
        PMF.support_bind] at supported
      obtain ⟨middle, reached, rest⟩ := Set.mem_iUnion₂.mp supported
      have progress := (runtime setup).runInteractionPlan_facts leaks inputs players network
        (block setup watcher current) execution middle invariant reached
      have completed := block_completes setup leaks watcher reveals players network inputs
        current execution middle invariant previous reached
      apply ih middle progress.invariant _ rest
      intro event before
      by_cases same : event.val = rank
      · have identified : event = current := Fin.ext same
        simpa only [identified] using completed
      · exact progress.completed (previous event (by omega))

/-- Every legal terminal history is settled, including histories with zero
probability under the equilibrium or any particular behavioral profile. -/
theorem terminal_history_settled
    (responses : (application setup leaks).ResponseMenu) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (history : (responses.protocol (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).History)
    (terminal : (responses.protocol (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).terminal history.state) :
    ∃ execution : (application setup leaks).Execution,
      history.state = (application setup leaks).finished execution ∧
        execution.application.config.cut.Terminal := by
  rcases history with ⟨state, trace⟩
  cases state with
  | none => exact terminal.elim
  | some control =>
      obtain ⟨finished, idle⟩ := terminal
      have supported := responses.roundSupported_uniform (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher) trace
      rcases supported with ⟨accounted, reached⟩
      rw [idle] at reached
      have position : control.execution.environmentRecall.length = horizon setup watcher := by
        rw [finished, Nat.add_zero] at accounted
        exact accounted
      rw [position, ReactiveApplication.roundsFrom, PMF.support_bind] at reached
      obtain ⟨initial, initially, continued⟩ := Set.mem_iUnion₂.mp reached
      rw [initialLaw, PMF.support_map] at initially
      obtain ⟨source, _drawn, rfl⟩ := initially
      have actual := suffix_rounds setup leaks watcher responses.uniformResponses []
        (plan setup watcher) rfl
        (ReactiveApplication.Execution.initial (application setup leaks)
          (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs source))) rfl
      rw [actual] at continued
      refine ⟨control.execution, ?_, ?_⟩
      · cases control
        simp_all only [ReactiveApplication.finished]
      · exact plan_terminal setup leaks watcher reveals responses.uniformResponses
          ((runtime setup).reportNetwork leaks watcher) (setup.eventInputs source) _
          control.execution (EventGraphRuntime.State.initial_invariant (graph := graph setup)
            (setup.eventInputs source)) continued

/-- The actual finite-menu protocol reaches settled application states for
every behavioral profile. In particular this holds for the full raw menu,
without any conformance or equilibrium assumption on the profile. -/
theorem menu_settles [Fintype Player]
    (responses : (application setup leaks).ResponseMenu) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (profile : ∀ who, (responses.information (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).BehavioralPolicy who)
    (history : (responses.protocol (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).History)
    (supported : history ∈ ((responses.information (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).runBehavioral profile
        (2 * horizon setup watcher + 1)).support) :
    ∃ execution : (application setup leaks).Execution,
      history.state = (application setup leaks).finished execution ∧
        execution.application.config.cut.Terminal := by
  have observed : history.state ∈ (((responses.information (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).runBehavioral profile
        (2 * horizon setup watcher + 1)).map History.state).support := by
    rw [PMF.support_map]
    exact ⟨history, supported, rfl⟩
  rw [menu_execution_law setup leaks responses watcher profile, PMF.support_bind] at observed
  obtain ⟨initial, initially, continued⟩ := Set.mem_iUnion₂.mp observed
  rw [initialLaw, PMF.support_map] at initially
  obtain ⟨source, _drawn, rfl⟩ := initially
  rw [PMF.support_map] at continued
  obtain ⟨execution, reached, same⟩ := continued
  refine ⟨execution, same.symm, ?_⟩
  apply plan_terminal setup leaks watcher reveals _ ((runtime setup).reportNetwork leaks watcher)
    (setup.eventInputs source) _ execution
    (EventGraphRuntime.State.initial_invariant (graph := graph setup)
      (setup.eventInputs source)) reached

end Vegas
