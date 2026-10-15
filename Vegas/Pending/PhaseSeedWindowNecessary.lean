/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedEmissionUnique
import Vegas.Pending.PhaseSeedResolutionWindow
import Vegas.Pending.PhaseSeedRecordedWait

/-! # A later actual inclusion stays inside the original envelope's coin window -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [DecidableEq Player] in
/-- Moving the send tick later can only shrink the original-seed success event. -/
theorem inclusionWindow_antitone (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (seed : Seed runtime delay)
    {before after : Nat} (later : before ≤ after)
    (window : InclusionWindow runtime delay bound coordinate seed after) :
    InclusionWindow runtime delay bound coordinate seed before := by
  rcases window with protection | ⟨tick, lower, timely, coin⟩
  · exact Or.inl (lt_of_le_of_lt (Nat.add_le_add_right later _) protection)
  · exact Or.inr ⟨tick, later.trans lower, timely, coin⟩

/-- Every actual future selected inclusion uses the same immutable send tick and
original local coin word, regardless of the remainder's history-adaptive priority. -/
theorem future_inclusion_window (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (initial : PMF (app).State) (horizon : Nat)
    (players : Player → (app).Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (PhaseCount.onePacketMenu runtime leaks bounds).actions who past view)
    (remaining count : Nat) (execution next : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      ((controller runtime leaks delay bound priority).family seeds)).Trace
        (some ⟨remaining + count, none, execution⟩))
    {input : graph.Inputs} (valid : execution.application.Invariant input)
    (ordered : execution.application.Ordered)
    (words : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (reached : next ∈ ((app).runRounds
      ((controller runtime leaks delay bound priority).family seeds) players count
        execution).support)
    (owner : Player) (coordinate : PhaseSeedAddress graph)
    (requested : execution.application.SeedRequest owner coordinate.1)
    (entered : Nat)
    (activated : execution.application.current.native.activatedAt coordinate.1.event = some entered)
    (started : entered ≤ execution.application.current.native.clock)
    (timely : execution.application.current.native.clock - entered <
      runtime.deadline coordinate.1.event)
    (message : Message Player (CommitAttemptPacket graph))
    (recorded : (execution.application.current.native.clock - entered, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner execution.environmentRecall
        (execution.observeEnvironment app)).emissions)
    (selected : selectedAt runtime leaks priority seeds.1 next = some coordinate)
    (identifier : MessageId Player)
    (included : (.include identifier : (app).Command) ∈
      (((controller runtime leaks delay bound priority).family seeds)
        next.environmentRecall (next.observeEnvironment app)).support) :
    identifier = message.id ∧ InclusionWindow runtime delay bound coordinate (seeds.2 coordinate)
      (execution.application.current.native.clock - entered) := by
  classical
  let scheduler := (controller runtime leaks delay bound priority).family seeds
  have nextValid := (ReactiveApplication.Invariant.policyInvariant app
    (phaseApplication_invariant runtime leaks input) players).runRounds scheduler count
      execution next valid reached
  obtain ⟨acting, nextRequest⟩ := selected_request runtime leaks priority seeds.1 next nextValid
    coordinate selected
  have sameOwner : acting = owner := Option.some.inj
    (nextRequest.2.2.2.1.symm.trans requested.2.2.2.1)
  subst acting
  have initialBound : ClosedCoordinateBound runtime execution.application.current.native.clock
      entered coordinate.1 execution.application :=
    ⟨le_rfl, started, by rw [requested.1], by rw [requested.1],
      fun _ => Or.inr ⟨requested.2.2.1, activated, timely⟩⟩
  have retained := retained_bound_runRounds runtime leaks scheduler players count execution next
    valid ordered execution.application.current.native.clock entered coordinate.1 initialBound
      reached
  have stamp : next.application.current.native.activatedAt coordinate.1.event = some entered := by
    rcases retained.event nextRequest.1 with completed | active
    · exact (nextRequest.2.2.1.1 completed).elim
    · exact active.2.1
  have singleton := PhaseSeedScheduler.runRounds_emissions_eq_singleton runtime leaks bounds
    initial horizon scheduler players covered remaining count execution next trace words reached
      coordinate.1 owner (execution.application.current.native.clock - entered) message recorded
  have chosen := (PMF.mem_support_pure_iff _ _).mp included
  have replyEq : reply runtime leaks delay bound coordinate (seeds.2 coordinate)
      (queryAt runtime leaks next coordinate owner) = .include identifier := by
    rw [choose_eq_reply runtime leaks delay bound priority seeds next coordinate selected owner
      requested.2.2.2.1] at chosen
    exact chosen.symm
  unfold reply at replyEq
  cases decided : decision runtime delay bound coordinate (seeds.2 coordinate)
      (queryAt runtime leaks next coordinate owner) with
  | activation => simp [decided, requested.2.2.2.1] at replyEq
  | expiry => simp [decided] at replyEq
  | wait => simp [decided] at replyEq
  | inclusion index =>
      obtain ⟨emission, indexed, _authorized, inTime, service⟩ := decision_inclusion_service
        runtime delay bound coordinate (seeds.2 coordinate) _ index decided
      have emissions : (queryAt runtime leaks next coordinate owner).emissions =
          [PhaseSeedInput.operationalEmission coordinate.1.attempt
            (execution.application.current.native.clock - entered, message)] := by
        change ((PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner
          next.environmentRecall (next.observeEnvironment app)).emissions.map _) = _
        rw [singleton]
        rfl
      have indexedQuery := indexed
      rw [emissions] at indexed
      have entryEq : emission = PhaseSeedInput.operationalEmission coordinate.1.attempt
          (execution.application.current.native.clock - entered, message) :=
        List.mem_singleton.mp (List.mem_of_getElem? indexed)
      have identifierEq : emission.identifier = identifier := by
        simpa only [decided, indexedQuery, Option.map_some, Option.getD_some,
          ReactiveApplication.Command.include.injEq] using replyEq
      refine ⟨identifierEq.symm.trans (congrArg PhaseSeedEmission.identifier entryEq), ?_⟩
      rcases service with protection | coin
      · exact Or.inl (by simpa only [entryEq, PhaseSeedInput.operationalEmission] using protection)
      · change next.application.current.native.clock -
          (next.application.current.native.activatedAt coordinate.1.event).getD
            next.application.current.native.clock < _ at inTime
        have lower : execution.application.current.native.clock - entered ≤
            next.application.current.native.clock - entered := Nat.sub_le_sub_right retained.clock _
        exact Or.inr ⟨next.application.current.native.clock - entered, lower,
          by simpa only [stamp, Option.getD_some] using inTime,
          by
            change (seeds.2 coordinate).2 (Fin.ofNat (clockLimit runtime delay + 1)
              (next.application.current.native.clock -
                (next.application.current.native.activatedAt coordinate.1.event).getD
                  next.application.current.native.clock)) = true at coin
            simpa only [stamp, Option.getD_some] using coin⟩

end Vegas.EventGraphRuntime.PhaseSeedCalendar
