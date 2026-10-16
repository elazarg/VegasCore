/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingServiceTape
import Vegas.Pending.PhaseCurrentTokens

/-! # Actual counted emissions under original local service tapes -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

local notation "app" => phaseApplication runtime leaks

/-- Source values and hidden packet aliases do not enter the local tier's
emission choice. The first local flip is omission; later flips reverse the
clock-only service decision. -/
def bindingServiceCoinSends (clocks : List Nat) (choose : List Nat → Bool)
    (coin : Bool × Bool) : Bool :=
  coin.1 || if clocks.length = 1 then !coin.2
    else if choose clocks then !coin.2 else coin.2

/-- Actual history makes every SEND tier transmit. The result is a deterministic
local tape read, even though source results and both hidden encoders still
randomize. No fresh-slot or desired action-shape premise is supplied. -/
theorem bindingServiceCoinResponse_transmission_of_history
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView → PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (coin : Bool × Bool) (menu : (app).ResponseMenu) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount) (control : (app).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control))
    (active : control.actor = some owner)
    (output : graph.outputLayout event = .binding owner payload)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall owner),
      event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    (bindingServiceCoinResponse runtime leaks bounds owner
        ⟨control.execution.application.attempt, event⟩ payload values choose slotWeight
          slotNonnegative slotBounded coin (control.execution.recall owner)
            (control.execution.observe app owner)).map (fun response =>
                response.transmission.isSome) =
      PMF.pure (bindingServiceCoinSends (PhaseSeedScheduler.serviceClocks runtime leaks
        ⟨control.execution.application.attempt, event⟩ owner (control.execution.recall owner)
          (control.execution.observe app owner)) choose coin) := by
  obtain ⟨rawLaw, sourceLaw⟩ := bindingEncoders_transmission_of_history runtime leaks bounds
    owner event payload values slotWeight slotNonnegative slotBounded menu plan inputs horizon
      scheduler capacity control trace active output request unsent catalogue
  rcases coin with ⟨raw, flip⟩
  unfold bindingServiceCoinResponse bindingServiceCoinSends
  dsimp only
  cases raw <;> cases flip <;>
    simp only [Bool.false_or, Bool.true_or, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, rawLaw]
  all_goals split_ifs <;> first | exact sourceLaw | (rw [PMF.pure_map]; rfl)

omit [Fintype Player] in
/-- Every actual callback has an unused original tape index. This follows from
the protocol response budget and the filtered physical address word. -/
theorem bindingServiceOrdinal_lt_horizon (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (owner : Player) (active : control.actor = some owner) (coordinate : CommitAttemptEvent graph) :
    (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner
      (control.execution.recall owner)).length < horizon := by
  classical
  have bounded := (app).active_recall_lt_horizon initial horizon scheduler control trace owner
      active
  have filtered : (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner
      (control.execution.recall owner)).length ≤ (control.execution.recall owner).length := by
    simpa only [PhaseSeedScheduler.ownerWord, List.length_map] using List.length_filter_le
      (fun entry => decide (PhaseRuntimeState.requests entry.beforeView.application.2 owner
        coordinate)) (control.execution.recall owner)
  exact filtered.trans_lt bounded

/-- The original tape member's actual callback is exactly its clock-only
Boolean choice. The complete initial law, physical source result and private
catalogue stay unchanged. -/
theorem bindingServiceTapeMember_transmission_of_history
    (outside : (app).Policy)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView → PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool) (failure timing : ℝ)
    (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
    (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (capacity : horizon ≤ bounds.candidateCount)
    (tape : Fin horizon → Bool × Bool) (control : (app).Control)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (active : control.actor = some owner)
    (output : graph.outputLayout event = .binding owner payload)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall owner),
      event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    let raw := (onePacketMenu runtime leaks bounds).toRawTrace
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
    let selected : Fin horizon := ⟨_, bindingServiceOrdinal_lt_horizon runtime leaks
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler control raw owner active
        ⟨control.execution.application.attempt, event⟩⟩
    (bindingServiceTapeMember runtime leaks bounds outside owner
      ⟨control.execution.application.attempt, event⟩ payload values choose failure timing
        firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
          slotBounded rawWeight rawNonnegative rawBounded horizon tape
            (control.execution.recall owner) (control.execution.observe app owner)).map
              (fun response => response.transmission.isSome) =
      PMF.pure (bindingServiceCoinSends (PhaseSeedScheduler.serviceClocks runtime leaks
        ⟨control.execution.application.attempt, event⟩ owner (control.execution.recall owner)
          (control.execution.observe app owner)) choose (tape selected)) := by
  classical
  intro raw selected
  obtain ⟨input, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
      scheduler raw
  have publicRequest : PhaseRuntimeState.requests
      (control.execution.observe app owner).application.2 owner
        ⟨control.execution.application.attempt, event⟩ :=
    (PhaseRuntimeState.requests_publicView _ valid owner _).mpr request
  have inside := selected.isLt
  change (PhaseSeedScheduler.ownerWord runtime leaks
    ⟨control.execution.application.attempt, event⟩ owner (control.execution.recall owner)).length <
      horizon at inside
  simp only [bindingServiceTapeMember, publicRequest, ↓reduceIte, dite_eq_left inside]
  exact bindingServiceCoinResponse_transmission_of_history runtime leaks bounds owner event payload
    values choose slotWeight slotNonnegative slotBounded (tape selected)
      (onePacketMenu runtime leaks bounds) plan inputs horizon scheduler capacity control trace
          active
        output request unsent catalogue

end Vegas.EventGraphRuntime.PhaseCount
