/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochRequestBound
import Vegas.Pending.ReservedEpochSampleProgress

/-! # Every nonterminal interval consumes semantic work -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem sampled_interval_decreases {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy) (limit cycle : Nat)
    (inputs : graph.Inputs) (before after : (app).Execution)
    (valid : WorkValid inputs before.application) (frontier : before.application.Frontier)
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth (graph := graph) packetBudget)
    (phase : RuntimePhase graph) (head : before.application.phases.head? = some phase)
    (kind : phase.kind = .sample) (event : graph.EventId) (atLow : event.val = phase.low)
    (ready : before.application.current.native.config.cut.Ready event)
    (chance : graph.actor? event = none)
    (reached : after ∈ ((app).runRounds (family runtime leaks packetBudget tape) players
      ((limit + 2) * cycleWidth (graph := graph) packetBudget) before).support) :
    workRemaining after.application < workRemaining before.application := by
  let width := cycleWidth (graph := graph) packetBudget
  let slot := packetBudget + Fintype.card Player
  let rest := (limit + 2) * width - slot - 1
  have slotBound : slot < width := by dsimp [slot, width, cycleWidth]; omega
  have duration : (limit + 2) * width = slot + (rest + 1) := by
    have enough : width ≤ (limit + 2) * width := by nlinarith
    dsimp [rest]
    omega
  rw [duration, (app).runRounds_add] at reached
  obtain ⟨middle, prefixReached, suffixReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨next, moved, finished⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ suffixReached)
  have middleValid := (work_bounded_invariant runtime leaks
    (family runtime leaks packetBudget tape) inputs (workRemaining before.application)).runRounds
      players slot before middle ⟨valid, le_rfl⟩ prefixReached
  have nextValid := (work_bounded_invariant runtime leaks
    (family runtime leaks packetBudget tape) inputs (workRemaining middle.application)).round
      players middle next ⟨middleValid.1, le_rfl⟩ moved
  have finalBound := runRounds_work_le runtime leaks (family runtime leaks packetBudget tape)
    players rest inputs next after nextValid.1 finished
  by_contra notStrict
  have flat : workRemaining middle.application = workRemaining before.application := by omega
  obtain ⟨_same, phases, completed⟩ := runRounds_flat_snapshot runtime leaks
    (family runtime leaks packetBudget tape) players slot inputs before middle valid
      prefixReached flat
  have middleHead : middle.application.phases.head? = some phase := by rw [phases]; exact head
  have middleReady : middle.application.current.native.config.cut.Ready event := by
    simpa only [EventOrder.Cut.Ready, completed] using ready
  have middleFrontier := (phaseApplication_frontier runtime leaks).policyInvariant app players
  have frontierNext := middleFrontier.runRounds (family runtime leaks packetBudget tape)
    slot before middle frontier prefixReached
  have middleCursor := (app).runRounds_environmentRecall_length
    (family runtime leaks packetBudget tape) players slot before middle prefixReached
  rw [cursor] at middleCursor
  have strict := sample_round_decreases runtime leaks packetBudget tape players cycle middle next
    inputs middleValid.1 frontierNext phase middleHead kind event atLow middleReady chance
      middleCursor moved
  omega

theorem nonterminal_interval_decreases {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (ordered : graph.RevealRelaxedOrdered) (inputs : graph.Inputs) (cycle limit : Nat)
    (deadline : ∀ event, runtime.deadline event ≤ limit)
    (before after : (app).Execution) (valid : WorkValid inputs before.application)
    (frontier : before.application.Frontier) (live : before.application.Live)
    (quiescent : ∀ event, ¬ before.application.current.AutomaticReady event)
    (cursor : before.environmentRecall.length =
      cycle * cycleWidth (graph := graph) packetBudget)
    (clock : before.application.current.native.clock = cycle)
    (nonempty : before.application.phases ≠ [])
    (reached : after ∈ ((app).runRounds (family runtime leaks packetBudget tape) players
      ((limit + 2) * cycleWidth (graph := graph) packetBudget) before).support) :
    workRemaining after.application < workRemaining before.application := by
  rcases before.application.request_or_sample frontier live quiescent nonempty with
    ⟨owner, event, request⟩ | ⟨phase, event, head, kind, atLow, ready, chance⟩
  · exact requested_interval_decreases runtime leaks packetBudget tape players ordered inputs
      cycle limit deadline before after valid cursor clock owner ⟨before.application.attempt, event⟩
        request reached
  · exact sampled_interval_decreases runtime leaks packetBudget tape players limit cycle inputs
      before after valid frontier cursor phase head kind event atLow ready chance reached

end Vegas.EventGraphRuntime.ReservedEpoch
