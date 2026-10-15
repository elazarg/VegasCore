/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedEmissionTimes
import Vegas.Pending.PhaseSeedWindowNecessary

/-! # Adaptive wait and send choices cannot enlarge the original coin window -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Any later adaptive send that the actual selected seed serves lies in the
window already available to an immediate send at this unsent callback. The later
policies can depend on their complete retained observations. -/
theorem future_unsent_inclusion_window (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (players : Player → (app).Policy) (count : Nat) (execution next : (app).Execution)
    {input : graph.Inputs} (valid : execution.application.Invariant input)
    (ordered : execution.application.Ordered)
    (words : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (owner : Player) (coordinate : PhaseSeedAddress graph)
    (requested : execution.application.SeedRequest owner coordinate.1)
    (entered : Nat)
    (activated : execution.application.current.native.activatedAt coordinate.1.event = some entered)
    (started : entered ≤ execution.application.current.native.clock)
    (timely : execution.application.current.native.clock - entered <
      runtime.deadline coordinate.1.event)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false)
    (reached : next ∈ ((app).runRounds
      ((controller runtime leaks delay bound priority).family seeds) players count
        execution).support)
    (selected : selectedAt runtime leaks priority seeds.1 next = some coordinate)
    (identifier : MessageId Player)
    (included : (.include identifier : (app).Command) ∈
      (((controller runtime leaks delay bound priority).family seeds)
        next.environmentRecall (next.observeEnvironment app)).support) :
    InclusionWindow runtime delay bound coordinate (seeds.2 coordinate)
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
  have futureLower := PhaseSeedScheduler.runRounds_unsent_emissions_lower runtime leaks scheduler
    players count execution next valid ordered words owner coordinate.1 requested entered activated
    started timely unsent reached
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
      rcases service with protection | coin
      · have member := List.mem_of_getElem? indexed
        change emission ∈ ((PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner
          next.environmentRecall (next.observeEnvironment app)).emissions.map _) at member
        obtain ⟨timed, member, same⟩ := List.mem_map.mp member
        have lower := futureLower timed member
        have clockEq := congrArg PhaseSeedEmission.clock same
        change timed.1 = emission.clock at clockEq
        rw [clockEq] at lower
        exact Or.inl (lt_of_le_of_lt (Nat.add_le_add_right lower _) protection)
      · change next.application.current.native.clock -
          (next.application.current.native.activatedAt coordinate.1.event).getD
            next.application.current.native.clock < _ at inTime
        change (seeds.2 coordinate).2 (Fin.ofNat (clockLimit runtime delay + 1)
          (next.application.current.native.clock -
            (next.application.current.native.activatedAt coordinate.1.event).getD
              next.application.current.native.clock)) = true at coin
        exact Or.inr ⟨next.application.current.native.clock - entered,
          Nat.sub_le_sub_right retained.clock _,
          by simpa only [stamp, Option.getD_some] using inTime,
          by simpa only [stamp, Option.getD_some] using coin⟩

end Vegas.EventGraphRuntime.PhaseSeedCalendar
