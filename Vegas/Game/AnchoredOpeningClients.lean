/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AnchoredFirstTurnLaw
import Interaction.ReactiveAnchoredTrace
import Vegas.Game.OnePacketHonestLaw
import Vegas.Game.IntendedOpeningContinuation
import Vegas.Game.OnePacketHonestAgreement

/-! # First-turn clients of the intended effective opening from reached boundaries

A *reached boundary* is the execution of a legal history at a scheduler
boundary whose configuration is a prefix at some rank, every later event still
untouched, and every own submission made at its author's turn. Every reached
boundary is a completion boundary of its own anchored first-turn clients
(`Vegas.reachedBoundary_completionBoundary`), so those clients read out the
source continuation of its decoded point (`Vegas.reachedBoundary_continuation`).

When the decoded point is a point of the intended game, the clients of the
intended effective opening read out a continuation recording no failed reveal,
while a decoded debt would record one on every terminal continuation; since
every source step from the intended game stays in it or leaves a debt, every
execution they reach from the boundary within the horizon decodes to a point
of the intended game (`Vegas.reachedBoundary_intended`).
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

/-- **The clients stay in the intended game from a reached boundary.** For a
well-formed setup, under the asynchronous contract with timely delays, from a
reached boundary decoding to a point of the intended game, every execution the
anchored first-turn clients of the intended effective opening reach within the
horizon decodes to a point of the intended game. -/
theorem reachedBoundary_intended [Finite Player] {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound) (turns : Nat)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) {rank : Nat}
    {anchor : (application setup leaks).Execution}
    (reached : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point) :
    ∀ more, anchor.environmentRecall.length + more ≤ horizon →
      ∀ execution ∈ ((application setup leaks).runRounds scheduler
          (ReactiveApplication.anchoredPolicy anchor
            (firstTurnClients setup leaks bound turns (setup.intendedOpeningProfile intended)))
          more anchor).support,
        DecodedExecution setup leaks (setup.intendedOpeningProfile intended)
          (ProtocolState.Intended setup.program) execution := by
  have := Fintype.ofFinite Player
  let app := application setup leaks
  let opening := setup.intendedOpeningProfile intended
  let players := ReactiveApplication.anchoredPolicy anchor
    (firstTurnClients setup leaks bound turns opening)
  let count := anchor.environmentRecall.length
  have boundary := reachedBoundary_completionBoundary reached
    (firstTurnClients setup leaks bound turns opening)
  have anchorSupported : anchor ∈ (app.roundsFrom (initialLaw setup) scheduler players
      count).support := boundary.supported
  -- The decoded anchor point carries the program's registry and publication status.
  have staticPoint : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context)
      point := by
    obtain ⟨staticRank, ⟨staticResidual⟩, staticHolds⟩ :=
      roundsFrom_static scheduler players opening count anchor anchorSupported
    have sameRank := isPrefix_unique staticResidual.checkpoint.ordered reached.ordered
    subst sameRank
    exact staticHolds point decoded
  -- The anchored clients' readout law from the anchor records no failed reveal.
  have lawFree : ∀ final ∈ (app.runRounds scheduler players (horizon - count) anchor).support,
      ∀ terminal, sourceReadout setup leaks (app.finished final) = some terminal →
        ∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0 := by
    intro final finalMem terminal read who
    have law := anchored_firstTurn_boundaryContinuation contract timely turns opening
      (setup.intendedOpeningProfile_opensEffectively intended) anchor rank anchor boundary
      reached.bounded ⟨fun _ => List.prefix_refl _, reached.turns⟩
    have inLaw : some terminal ∈ ((app.runToHorizon scheduler players horizon anchor).map
        (fun final => sourceReadout setup leaks (app.finished final))).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨final, finalMem, read⟩
    rw [law] at inLaw
    unfold sourceContinuation serviceSourcePrefix? at inLaw
    change some terminal ∈ ((setup.continuationLaw opening
      (sourceServicePrefix? setup rank anchor.application.config)).map some).support at inLaw
    rw [decoded] at inLaw
    obtain ⟨terminal', member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp inLaw
    cases Option.some.inj same
    exact setup.intendedOpening_continuation_failedReveals intended _ point le_rfl staticPoint
      intendedPoint _ member who
  intro more
  induction more with
  | zero =>
      intro _ execution supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      obtain ⟨residual⟩ := boundary.sourceResidual (profile := opening)
      refine ⟨rank, ⟨residual⟩, fun other otherDecoded => ?_⟩
      rw [decoded, Option.some.injEq] at otherDecoded
      subst otherDecoded
      exact intendedPoint
  | succ more ih =>
      intro within execution supported
      rw [show more + 1 = more + 1 from rfl, ReactiveApplication.runRounds_add] at supported
      obtain ⟨prior, priorMem, moved⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      have priorRound : execution ∈ (app.round scheduler players prior).support := by
        change execution ∈ ((app.round scheduler players prior).bind
          (app.runRounds scheduler players 0)).support at moved
        obtain ⟨middle, middleMem, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp moved
        cases (PMF.mem_support_pure_iff _ _).mp rest
        exact middleMem
      obtain ⟨rankPrior, ⟨residual⟩, decodedPrior⟩ := ih (by omega) prior priorMem
      have step := round_configStep setup leaks scheduler players prior execution priorRound
      rcases step with same | ⟨event, ready, action, member⟩
      · refine ⟨rankPrior, ⟨same ▸ residual⟩, ?_⟩
        rw [same]
        exact decodedPrior
      · obtain ⟨next, reachedPoint⟩ := residual.step event ready action _ member
        refine ⟨rankPrior + 1, ⟨next⟩, fun nextPoint nextDecoded => ?_⟩
        rw [next.decode, Option.some.injEq] at nextDecoded
        subst nextDecoded
        rcases ProtocolState.intended_or_owesFailure_step setup.program _ _ _
            (decodedPrior _ residual.decode) reachedPoint with kept | ⟨who, owed⟩
        · exact kept
        · exfalso
          have owing : DecodedExecution setup leaks opening
              (ProtocolState.OwesFailure who setup.program) execution :=
            ⟨rankPrior + 1, ⟨next⟩, fun other otherDecoded => by
              rw [next.decode, Option.some.injEq] at otherDecoded
              subst otherDecoded
              exact owed⟩
          have priorSupported := mem_roundsFrom_of_runRounds (app := app) anchorSupported priorMem
          have current : execution ∈ (app.roundsFrom (initialLaw setup) scheduler players
              (count + more + 1)).support := by
            rw [ReactiveApplication.roundsFrom_succ]
            exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨prior, priorSupported, priorRound⟩
          obtain ⟨final, finalMem⟩ := (app.runRounds scheduler players
            (horizon - (count + more + 1)) execution).support_nonempty
          obtain ⟨terminal, read, failed⟩ := runRounds_owesFailure_failedReveals
            contract.completes players within current who owing final finalMem
          have composed : final ∈ (app.runRounds scheduler players (horizon - count)
              anchor).support := by
            rw [show horizon - count = (more + 1) + (horizon - (count + more + 1)) by omega,
              ReactiveApplication.runRounds_add]
            refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨execution, ?_, finalMem⟩
            rw [ReactiveApplication.runRounds_add]
            exact supported
          have zero := lawFree final composed terminal read who
          omega

end Vegas
