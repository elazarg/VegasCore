/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketPrescribedSupport
import Vegas.Game.OnePacketExclusionPayoff
import GameTheoryExtensions.Analysis.Protocol.SupportedChoiceContinuation

/-! # The one-packet law under trembles

A trembled component keeps the fraction `(1 - scale²)(1 - scale)` of its main
law at every choice (`Vegas.trembleRetention`), so the prescribed component
dominates the as-if-honest choice with that retention, which tends to one along
vanishing scales (`Vegas.tendsto_trembleRetention`). The results below are
parametric in the retention, so any component family that keeps a fraction of
the as-if-honest choice instantiates them.

The as-if-honest profile plays the as-if-honest choice at every information
state (`Vegas.honestProfile`). A profile of the one-packet game that dominates
it by that fraction at every history the as-if-honest play reaches, whatever it
does elsewhere, has a whole-run law within the missing mass in total variation
of the as-if-honest law, from initialization and from every history
(`Vegas.onePacket_withinTV_honest`, `Vegas.onePacket_continuation_withinTV_honest`).
The missing mass is at most the number of players times the fuel times one
minus the retention, uniformly over what the profile does off that support.

Hence, where the as-if-honest play has the intended law of typed readouts, the
joint law of typed readout and exclusion payoff of every such profile is within
that bound of the intended joint law
(`Vegas.onePacket_readout_exclusion_withinTV`), pointwise as the law
approximation of a limit certificate requires, with an error that vanishes along
every retention tending to one (`Vegas.onePacket_lawApproximation`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))
  (initial : PMF (application setup leaks).State) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

section Components

/-- The fraction of its main law a trembled component keeps. -/
def trembleRetention (scale : ℝ) : ℝ := (1 - scale ^ 2) * (1 - scale)

theorem trembleRetention_nonneg {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) :
    0 ≤ trembleRetention scale :=
  mul_nonneg (sub_nonneg.mpr (pow_le_one₀ nonnegative le_one)) (sub_nonneg.mpr le_one)

theorem trembleRetention_le_one {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) :
    trembleRetention scale ≤ 1 := by
  unfold trembleRetention
  have square : 0 ≤ scale ^ 2 := sq_nonneg scale
  have upper : 1 - scale ^ 2 ≤ 1 := by linarith
  calc (1 - scale ^ 2) * (1 - scale) ≤ 1 * 1 :=
        mul_le_mul upper (by linarith) (by linarith) zero_le_one
    _ = 1 := one_mul 1

/-- The mass a trembled component may move off its main law. -/
theorem one_sub_trembleRetention_le {scale : ℝ} (nonnegative : 0 ≤ scale) :
    1 - trembleRetention scale ≤ scale + scale ^ 2 := by
  unfold trembleRetention
  nlinarith [pow_nonneg nonnegative 3]

/-- Along vanishing tremble scales the retention tends to one. -/
theorem tendsto_trembleRetention {scales : ℕ → ℝ} (vanishing : Tendsto scales atTop (nhds 0)) :
    Tendsto (fun n => trembleRetention (scales n)) atTop (nhds 1) := by
  have limit := ((tendsto_const_nhds (x := (1 : ℝ))).sub (vanishing.pow 2)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub vanishing)
  simpa [trembleRetention] using limit

end Components

section Law

/-- **As-if-honest play.** Every player plays the as-if-honest choice at every
information state of the one-packet game. -/
def honestProfile (assessment : setup.intendedModel.BehavioralAssessment) :
    ∀ who, (onePacketModel setup leaks bounds initial horizon scheduler).BehavioralPolicy who :=
  fun who => honestChoice setup leaks bounds initial horizon scheduler assessment who

/-- A profile of the one-packet game dominates as-if-honest play from `start`
with retention `retention` when at every history the as-if-honest continuation
from `start` reaches, every player's law gives each choice at least `retention`
times its as-if-honest mass. -/
def DominatesHonestFrom (assessment : setup.intendedModel.BehavioralAssessment)
    (retention : ℝ)
    (profile : ∀ who,
      (onePacketModel setup leaks bounds initial horizon scheduler).BehavioralPolicy who)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
      scheduler).History) : Prop :=
  ∀ fuel history,
    history ∈ ((onePacketModel setup leaks bounds initial horizon scheduler).runBehavioralFrom
      (honestProfile setup leaks bounds initial horizon scheduler assessment) fuel start).support →
    ∀ who choice,
      retention *
          ((honestProfile setup leaks bounds initial horizon scheduler assessment who
            ((onePacketModel setup leaks bounds initial horizon scheduler).infoOf who
              history.trace)) choice).toReal ≤
        ((profile who ((onePacketModel setup leaks bounds initial horizon scheduler).infoOf who
          history.trace)) choice).toReal

/-- A profile playing the prescribed component at every information state the
as-if-honest play reaches dominates it with the retention of the tremble
scale. -/
theorem dominatesHonestFrom_of_prescribed
    (assessment : setup.intendedModel.BehavioralAssessment) (scale : ℝ) (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1)
    (profile : ∀ who,
      (onePacketModel setup leaks bounds initial horizon scheduler).BehavioralPolicy who)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
      scheduler).History)
    (prescribed : ∀ fuel history,
      history ∈ ((onePacketModel setup leaks bounds initial horizon scheduler).runBehavioralFrom
        (honestProfile setup leaks bounds initial horizon scheduler assessment) fuel
        start).support → ∀ who,
      profile who ((onePacketModel setup leaks bounds initial horizon scheduler).infoOf who
          history.trace) =
        prescribedComponent setup leaks bounds initial horizon scheduler assessment scale
          nonnegative le_one who
          ((onePacketModel setup leaks bounds initial horizon scheduler).infoOf who
            history.trace)) :
    DominatesHonestFrom setup leaks bounds initial horizon scheduler assessment
      (trembleRetention scale) profile start := by
  intro fuel history reached who choice
  rw [prescribed fuel history reached who]
  exact trembledChoice_ge_main setup leaks bounds initial horizon scheduler nonnegative le_one
    who _ _ _ choice

/-- **Continuations near as-if-honest play.** From every history, a profile
dominating as-if-honest play from it with retention `retention ∈ [0, 1]` has,
at every fuel, a continuation within `|Player| * fuel * (1 - retention)` in
total variation of the as-if-honest continuation. -/
theorem onePacket_continuation_withinTV_honest
    (assessment : setup.intendedModel.BehavioralAssessment) {retention : ℝ}
    (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (profile : ∀ who,
      (onePacketModel setup leaks bounds initial horizon scheduler).BehavioralPolicy who)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
      scheduler).History)
    (dominates : DominatesHonestFrom setup leaks bounds initial horizon scheduler assessment
      retention profile start) (fuel : Nat) :
    PMF.WithinTV ((Fintype.card Player * fuel : ℕ) * (1 - retention))
      ((onePacketModel setup leaks bounds initial horizon scheduler).runBehavioralFrom
        (honestProfile setup leaks bounds initial horizon scheduler assessment) fuel start)
      ((onePacketModel setup leaks bounds initial horizon scheduler).runBehavioralFrom
        profile fuel start) :=
  (InformationModel.runBehavioralFrom_withinTV_of_supported_choices
    (onePacketModel setup leaks bounds initial horizon scheduler) _ profile retention nonnegative
    le_one start dominates fuel).mono (one_sub_pow_le_mul nonnegative _)

/-- **The whole run near as-if-honest play.** From initialization, a profile
dominating as-if-honest play with retention `retention ∈ [0, 1]` has a run
within `|Player| * fuel * (1 - retention)` in total variation of the
as-if-honest run. -/
theorem onePacket_withinTV_honest
    (assessment : setup.intendedModel.BehavioralAssessment) {retention : ℝ}
    (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (profile : ∀ who,
      (onePacketModel setup leaks bounds initial horizon scheduler).BehavioralPolicy who)
    (dominates : DominatesHonestFrom setup leaks bounds initial horizon scheduler assessment
      retention profile ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
        scheduler).initHistory) (fuel : Nat) :
    PMF.WithinTV ((Fintype.card Player * fuel : ℕ) * (1 - retention))
      ((onePacketModel setup leaks bounds initial horizon scheduler).runBehavioral
        (honestProfile setup leaks bounds initial horizon scheduler assessment) fuel)
      ((onePacketModel setup leaks bounds initial horizon scheduler).runBehavioral
        profile fuel) :=
  onePacket_continuation_withinTV_honest setup leaks bounds initial horizon scheduler assessment
    nonnegative le_one profile _ dominates fuel

end Law

section Readout

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- The typed readout of a terminal history of the one-packet game, with the
exclusion payoff it determines. -/
def readoutExclusion
    (final : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
      scheduler).History) :
    Option (State L setup.program.terminalCtx) × (Player → ℝ) :=
  (sourceReadout setup leaks final.state,
    exclusionBase setup parameter utility excludedPayoff leaks final.state)

/-- The intended typed readout of an intended history, with the exclusion
payoff it determines. -/
def intendedReadoutExclusion (final : setup.intendedProtocol.History) :
    Option (State L setup.program.terminalCtx) × (Player → ℝ) :=
  (setup.protocolReadout final.state,
    exclusionReadoutUtility setup parameter utility excludedPayoff
      (setup.protocolReadout final.state))

/-- **The readout and exclusion law under trembles.** If as-if-honest play has
the intended law of typed readouts, the joint law of typed readout and native
exclusion payoff of every profile dominating as-if-honest play with retention
`retention ∈ [0, 1]` is within `|Player| * fuel * (1 - retention)` in total
variation of the intended joint law of typed readout and exclusion payoff. -/
theorem onePacket_readout_exclusion_withinTV
    (assessment : setup.intendedModel.BehavioralAssessment)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) (sourceFuel targetFuel : Nat)
    (honestLaw : ((onePacketModel setup leaks bounds initial horizon scheduler).runBehavioral
        (honestProfile setup leaks bounds initial horizon scheduler assessment)
        targetFuel).map (fun final => sourceReadout setup leaks final.state) =
      (setup.intendedModel.runBehavioral intended sourceFuel).map
        (fun final => setup.protocolReadout final.state))
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (profile : ∀ who,
      (onePacketModel setup leaks bounds initial horizon scheduler).BehavioralPolicy who)
    (dominates : DominatesHonestFrom setup leaks bounds initial horizon scheduler assessment
      retention profile ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
        scheduler).initHistory) :
    PMF.WithinTV ((Fintype.card Player * targetFuel : ℕ) * (1 - retention))
      (((onePacketModel setup leaks bounds initial horizon scheduler).runBehavioral profile
        targetFuel).map
          (readoutExclusion setup leaks bounds initial horizon scheduler parameter utility
            excludedPayoff))
      ((setup.intendedModel.runBehavioral intended sourceFuel).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff)) := by
  let attach := fun readout : Option (State L setup.program.terminalCtx) =>
    (readout, exclusionReadoutUtility setup parameter utility excludedPayoff readout)
  have native : readoutExclusion setup leaks bounds initial horizon scheduler parameter utility
      excludedPayoff = attach ∘ fun final => sourceReadout setup leaks final.state := rfl
  have source : intendedReadoutExclusion setup parameter utility excludedPayoff =
      attach ∘ fun final => setup.protocolReadout final.state := rfl
  rw [native, source, ← PMF.map_comp, ← PMF.map_comp, ← honestLaw, PMF.map_comp,
    PMF.map_comp]
  exact ((onePacket_withinTV_honest setup leaks bounds initial horizon scheduler assessment
    nonnegative le_one profile dominates targetFuel).map _).symm

/-- **The law approximation of the one-packet game.** Along retentions
`retentions n` in `[0, 1]` that tend to one, if at every index as-if-honest
play of `assessments n` has the intended law of typed readouts under
`intended n`, every sequence of profiles dominating as-if-honest play with those
retentions has a joint law of typed readout and exclusion payoff whose
probabilities differ from the intended ones by an error that vanishes,
uniformly over outcomes. The error depends only on the retentions. -/
theorem onePacket_lawApproximation
    (assessments : ℕ → setup.intendedModel.BehavioralAssessment)
    (intended : ℕ → ∀ who, setup.intendedModel.BehavioralPolicy who)
    (sourceFuel targetFuel : Nat)
    (honestLaw : ∀ n, ((onePacketModel setup leaks bounds initial horizon scheduler).runBehavioral
        (honestProfile setup leaks bounds initial horizon scheduler (assessments n))
        targetFuel).map (fun final => sourceReadout setup leaks final.state) =
      (setup.intendedModel.runBehavioral (intended n) sourceFuel).map
        (fun final => setup.protocolReadout final.state))
    (retentions : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ retentions n) (le_one : ∀ n, retentions n ≤ 1)
    (converging : Tendsto retentions atTop (nhds 1))
    (profiles : ℕ → ∀ who,
      (onePacketModel setup leaks bounds initial horizon scheduler).BehavioralPolicy who)
    (dominates : ∀ n, DominatesHonestFrom setup leaks bounds initial horizon scheduler
      (assessments n) (retentions n) (profiles n)
      ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
        scheduler).initHistory) :
    ∃ lawError : ℕ → ℝ, Tendsto lawError atTop (nhds 0) ∧
      ∀ n outcome,
        |((((onePacketModel setup leaks bounds initial horizon scheduler).runBehavioral
            (profiles n) targetFuel).map
            (readoutExclusion setup leaks bounds initial horizon scheduler parameter utility
              excludedPayoff)) outcome).toReal -
          (((setup.intendedModel.runBehavioral (intended n) sourceFuel).map
            (intendedReadoutExclusion setup parameter utility excludedPayoff))
            outcome).toReal| ≤ lawError n := by
  refine ⟨fun n => (Fintype.card Player * targetFuel : ℕ) * (1 - retentions n), ?_,
    fun n outcome => (onePacket_readout_exclusion_withinTV setup leaks bounds initial horizon
      scheduler parameter utility excludedPayoff (assessments n) (intended n) sourceFuel
      targetFuel (honestLaw n) (nonnegative n) (le_one n) (profiles n) (dominates n)).apply
      outcome⟩
  have limit := ((tendsto_const_nhds (x := (1 : ℝ))).sub converging).const_mul
    ((Fintype.card Player * targetFuel : ℕ) : ℝ)
  simpa using limit

end Readout

end Vegas
