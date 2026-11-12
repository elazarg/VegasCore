module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketComparisonRetention
public import Vegas.Game.OnePacketProjectedDecision
public import Vegas.Game.IntendedAuthenticOpening
public import GameTheory.Analysis.Protocol.BehavioralTerminalConvergence
public import GameTheory.Math.Probability.StatisticalDistanceStability

@[expose] public section

/-! # Intended continuation laws at clean native boundaries -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) (initialLaw setup) horizon scheduler

/-- An actually reached intended native boundary has an actual intended source history. -/
theorem intendedReached_of_reachedBoundary
    (wellFormed : setup.WellFormed)
    (rank : Nat) (start : (E).History)
    (anchor : (application setup timeouts leaks).Execution)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup timeouts leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    IntendedReached setup point := by
  have actual : decodedPoint setup anchor.application.config = some point :=
    (decodedPoint_eq_of_isPrefix boundary.ordered).trans decoded
  obtain ⟨history, replayed⟩ := intendedHistory?_isSome_of_debtFree (timeouts := timeouts)
    wellFormed start.trace _ state (by
      intro found foundDecoded player
      rw [actual, Option.some.injEq] at foundDecoded
      subst foundDecoded
      exact ProtocolState.Intended.not_owesFailure player setup.program point intended)
  refine ⟨history, ?_⟩
  have last := intendedHistory?_state (timeouts := timeouts) start.trace replayed
  rw [state] at last
  exact last.trans actual

omit [Fintype Player] in
/-- Source continuation laws converge at every intended point with an actual source history. -/
theorem intended_sourceContinuation_converges
    [Finite Player]
    (wellFormed : setup.WellFormed)
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {target : setup.intendedModel.BehavioralAssessment}
    (converges : BehavioralAssessmentConvergesPointwise sequence target)
    (point : ProtocolState setup.program) (reached : IntendedReached setup point) :
    PMFConvergesPointwise
      (fun n => (setup.continuationLaw
        (setup.intendedOpeningProfile (sequence n).strategy) (some point)).map some)
      ((setup.continuationLaw
        (setup.intendedOpeningProfile target.strategy) (some point)).map some) := by
  let := Fintype.ofFinite Player
  obtain ⟨history, state⟩ := reached
  have histories := setup.intendedModel.runBehavioralTerminalFrom_convergesPointwise
    setup.intended_bounded.wellFoundedHistories converges.strategy history
  have readouts := histories.map (fun final => setup.protocolReadout final.state)
  have law (source : setup.intendedModel.BehavioralAssessment) :
      (setup.intendedModel.runBehavioralTerminalFrom
        setup.intended_bounded.wellFoundedHistories source.strategy history).map
          (fun final => setup.protocolReadout final.state) =
      (setup.continuationLaw (setup.intendedOpeningProfile source.strategy)
        (some point)).map some := by
    rw [setup.intendedModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
      setup.intended_bounded.wellFoundedHistories setup.intended_bounded]
    rw [setup.intendedOpeningProfile_runFrom wellFormed source.strategy _ history
      (by
        have length := setup.protocol_history_length
          (CommitmentInterface.values setup.program)
          (restrictAvailable.trace history.trace)
        omega), state]
  simpa only [law] using readouts

namespace OnePacketComparison

/-- The selected common assessment limit has the exact intended continuation law
at every reached clean source boundary, including boundaries of zero equilibrium reach. -/
theorem assembled_boundary_readout_law_of_converges
    [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sourceSequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (source : setup.intendedModel.BehavioralAssessment)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sourceSequence source)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (vanishes : Tendsto scale atTop (nhds 0))
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sourceSequence
      scale positive le_one weights targetSequence)
    (target : (N).BehavioralAssessment) (index : ℕ → ℕ)
    (increasing : StrictMono index)
    (targetConverges : BehavioralAssessmentConvergesPointwise
      (fun n => targetSequence (index n)) target)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup timeouts leaks).Control,
      ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some control) →
      control.execution.application.config.defaulted = ∅ →
      OpportunityAt timeouts leaks control.execution delay)
    (inclusion : ∀ control : (application setup timeouts leaks).Control,
      ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some control) →
      control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt timeouts leaks control.execution bound)
    (timely : (AsyncTimely timeouts) delay bound)
    (completes : ∀ control : (application setup timeouts leaks).Control,
      ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some control) →
      control.execution.application.config.defaulted = ∅ →
      (application setup timeouts leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (certificate : (E).WellFoundedHistories)
    (rank : Nat) (start : (E).History)
    (anchor : (application setup timeouts leaks).Execution)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup timeouts leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    ((N).runBehavioralTerminalFrom certificate target.strategy start).map
        (fun final => sourceReadout setup timeouts leaks final.state) =
      sourceContinuation setup (setup.intendedOpeningProfile source.strategy) rank
        anchor.application.config := by
  classical
  let error : ℕ → ℝ := fun n => (1 - slotRetention (scale (index n))) *
    (application setup timeouts leaks).remainingResponses horizon start.state
  have sourceLaw := intended_sourceContinuation_converges wellFormed sourceConverges point
    (intendedReached_of_reachedBoundary wellFormed rank start anchor state boundary point
      decoded intended)
  have sourceLimit : PMFConvergesPointwise
      (fun n => sourceContinuation setup
        (setup.intendedOpeningProfile (sourceSequence (index n)).strategy) rank
          anchor.application.config)
      (sourceContinuation setup (setup.intendedOpeningProfile source.strategy) rank
        anchor.application.config) := by
    intro outcome
    simpa only [sourceContinuation, decoded, Function.comp_def] using
      (sourceLaw outcome).comp increasing.tendsto_atTop
  have targetLimit := ((N).runBehavioralTerminalFrom_convergesPointwise certificate
    targetConverges.strategy start).map
      (fun final => sourceReadout setup timeouts leaks final.state)
  have missing : Tendsto (fun n => 1 - slotRetention (scale (index n))) atTop (nhds 0) := by
    simpa only [sub_self, Function.comp_def] using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_slotRetention (vanishes.comp increasing.tendsto_atTop))
  have errorLimit : Tendsto error atTop (nhds 0) := by
    simpa only [error, sub_self, zero_mul] using missing.mul
      (tendsto_const_nhds (x :=
        ((application setup timeouts leaks).remainingResponses horizon start.state : ℝ)))
  apply targetLimit.eq_of_statisticalDistance_le sourceLimit error errorLimit
  intro n
  have retentionNonnegative := slotRetention_nonneg (positive (index n)).le (le_one (index n))
  have retentionSmall := slotRetention_le_one (positive (index n)).le (le_one (index n))
  have dominates := assembled_dominatesHonestFrom_boundary setup timeouts leaks bounds horizon
    scheduler wellFormed covers capacity sourceSequence scale positive le_one weights
    targetSequence assembled (index n) opportunity inclusion timely completes certificate rank
    start anchor state boundary point decoded intended
  have close := onePacket_terminal_withinTV_honest setup timeouts leaks bounds (initialLaw setup)
    horizon scheduler (sourceSequence (index n)) certificate
    (targetSequence (index n)).strategy start retentionNonnegative retentionSmall dominates
  have budget := ((bounds.onePacketMenu timeouts leaks).expectedResponses_bounds (initialLaw setup)
    horizon scheduler certificate
    (honestProfile setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      (sourceSequence (index n))) (fun _ => False) start).2
  have expanded : PMF.WithinTV (error n)
      ((N).runBehavioralTerminalFrom certificate
        (honestProfile setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          (sourceSequence (index n))) start)
      ((N).runBehavioralTerminalFrom certificate (targetSequence (index n)).strategy start) :=
    close.mono (mul_le_mul_of_nonneg_left budget (sub_nonneg.mpr retentionSmall))
  have projected := expanded.map (fun final => sourceReadout setup timeouts leaks final.state)
  rw [counted_honest_boundary_readout_law (timeouts := timeouts) opportunity inclusion timely
    completes covers capacity (sourceSequence (index n)) certificate rank start anchor state
      boundary point decoded intended] at projected
  exact (statisticalDistance_le_iff _ _ _).mpr projected.symm

end OnePacketComparison

end Vegas
