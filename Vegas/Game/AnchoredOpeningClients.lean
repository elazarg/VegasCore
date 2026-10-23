/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AnchoredFirstTurnLaw
import Interaction.ReactiveAnchoredTrace
import Vegas.Game.OnePacketHonestLaw
import Vegas.Game.IntendedOpeningContinuation
import Vegas.Game.OnePacketHonestDecision
import Vegas.Game.OnePacketLawApproximation

/-! # First-turn clients of the intended effective opening from reached boundaries

A *reached boundary* is the execution of a legal history at a scheduler
boundary whose configuration is a prefix at some rank, every later event still
untouched, and every own submission made at its author's turn. Every reached
boundary is a completion boundary of its own anchored first-turn clients
(`Vegas.reachedBoundary_completionBoundary`), so those clients read out the
source continuation of its decoded point (`Vegas.reachedBoundary_continuation`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup leaks) in
/-- **A reached boundary.** The execution of a legal history at a scheduler
boundary, whose configuration is a prefix at `rank`, with every event from
`rank` on untouched and every own submission made at its author's turn. -/
structure ReachedBoundary (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (rank : Nat) (execution : (application setup leaks).Execution) : Prop where
  trace : Nonempty (((application setup leaks).protocol (initialLaw setup) horizon
    scheduler).Trace (some ⟨horizon - execution.environmentRecall.length, none, execution⟩))
  bounded : execution.environmentRecall.length ≤ horizon
  ordered : execution.application.config.cut.IsPrefix rank
  untouched : ∀ event : (graph setup).EventId, rank ≤ event.val →
    Untouched setup leaks event execution
  turns : ∀ who, OwnSubmissionsAtTurn setup leaks execution who

/-- **A reached boundary is a boundary of its anchored clients.** -/
theorem reachedBoundary_completionBoundary {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (reached : ReachedBoundary setup leaks horizon scheduler rank execution)
    (players : Player → (application setup leaks).Policy) :
    CompletionBoundary setup leaks scheduler
      (ReactiveApplication.anchoredPolicy execution players) rank execution := by
  obtain ⟨trace⟩ := reached.trace
  have member := (ReactiveApplication.mem_roundsFrom_anchoredPolicy_of_trace (initialLaw setup)
    horizon scheduler players trace).2
  rw [show horizon - (horizon - execution.environmentRecall.length) =
    execution.environmentRecall.length by have := reached.bounded; omega] at member
  exact ⟨member, reached.ordered, reached.untouched⟩

/-- **The clients' continuation from a reached boundary.** Under the
asynchronous contract with timely delays, for a source profile opening
effectively, the first-turn clients continued from a reached boundary read out
the source continuation of its decoded point. -/
theorem reachedBoundary_continuation [Finite Player] {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound) (turns : Nat)
    (profile : BehavioralProfile setup.program)
    (opens : ∀ who, (profile who).OpensEffectively setup.program []
      (Revelations.initial setup.context)) {rank : Nat}
    {execution : (application setup leaks).Execution}
    (reached : ReachedBoundary setup leaks horizon scheduler rank execution) :
    ((application setup leaks).runToHorizon scheduler
        (firstTurnClients setup leaks bound turns profile) horizon execution).map
        (fun final => sourceReadout setup leaks ((application setup leaks).finished final)) =
      sourceContinuation setup profile rank execution.application.config := by
  have anchored := anchored_firstTurn_boundaryContinuation contract timely turns profile opens
    execution rank execution (reachedBoundary_completionBoundary reached _) reached.bounded
    ⟨fun _ => List.prefix_refl _, reached.turns⟩
  unfold ReactiveApplication.runToHorizon at anchored ⊢
  rwa [ReactiveApplication.runRounds_anchoredPolicy] at anchored

end Vegas
