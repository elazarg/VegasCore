/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketTrembles
import Vegas.Game.OnePacketExclusionPayoff
import GameTheoryExtensions.Analysis.Protocol.SupportedChoiceContinuation
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # The one-packet law under trembles

The as-if-honest profile plays the as-if-honest choice at every information
state (`Vegas.honestProfile`). A profile of the one-packet game dominates it
with a retention when, at every history the as-if-honest play reaches, every
player's law gives each choice at least that fraction of its as-if-honest mass
(`Vegas.DominatesHonestFrom`); a trembled component of the as-if-honest choice
does so with the fraction of its main law it keeps. Whatever such a profile does
elsewhere, it has a whole-run law within the missing mass in total variation of
the as-if-honest law, from initialization and from every history
(`Vegas.onePacket_withinTV_honest`, `Vegas.onePacket_continuation_withinTV_honest`).
The missing mass is at most the number of players times the fuel times one
minus the retention, uniformly over what the profile does off that support.

At the full intended source budget, where as-if-honest play has its readout law, the
joint law of typed readout and exclusion payoff of every such profile is within
that bound of the intended joint law
(`Vegas.onePacket_readout_exclusion_withinTV`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))
  (initial : PMF (application setup runtime leaks).State) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

section Law

/-- **As-if-honest play.** Every player plays the as-if-honest choice at every
information state of the one-packet game. -/
def honestProfile (assessment : setup.intendedModel.BehavioralAssessment) :
    ∀ who, (onePacketModel setup runtime leaks bounds initial horizon scheduler).BehavioralPolicy
      who :=
  fun who => honestChoice setup runtime leaks bounds initial horizon scheduler assessment who

/-- A profile of the one-packet game dominates as-if-honest play from `start`
with retention `retention` when at every history the as-if-honest continuation
from `start` reaches, every player's law gives each choice at least `retention`
times its as-if-honest mass. -/
def DominatesHonestFrom (assessment : setup.intendedModel.BehavioralAssessment)
    (retention : ℝ)
    (profile : ∀ who,
      (onePacketModel setup runtime leaks bounds initial horizon scheduler).BehavioralPolicy who)
    (start : ((bounds.onePacketMenu runtime leaks).protocol initial horizon
      scheduler).History) : Prop :=
  ∀ fuel history,
    history ∈ ((onePacketModel setup runtime leaks bounds initial horizon
      scheduler).runBehavioralFrom
      (honestProfile setup runtime leaks bounds initial horizon scheduler assessment) fuel
        start).support →
    ∀ who choice,
      retention *
          ((honestProfile setup runtime leaks bounds initial horizon scheduler assessment who
            ((onePacketModel setup runtime leaks bounds initial horizon scheduler).infoOf who
              history.trace)) choice).toReal ≤
        ((profile who ((onePacketModel setup runtime leaks bounds initial horizon
          scheduler).infoOf who
          history.trace)) choice).toReal

/-- **Continuations near as-if-honest play.** From every history, a profile
dominating as-if-honest play from it with retention `retention ∈ [0, 1]` has,
at every fuel, a continuation within `|Player| * fuel * (1 - retention)` in
total variation of the as-if-honest continuation. -/
theorem onePacket_continuation_withinTV_honest
    (assessment : setup.intendedModel.BehavioralAssessment) {retention : ℝ}
    (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (profile : ∀ who,
      (onePacketModel setup runtime leaks bounds initial horizon scheduler).BehavioralPolicy who)
    (start : ((bounds.onePacketMenu runtime leaks).protocol initial horizon
      scheduler).History)
    (dominates : DominatesHonestFrom setup runtime leaks bounds initial horizon scheduler assessment
      retention profile start) (fuel : Nat) :
    PMF.WithinTV ((Fintype.card Player * fuel : ℕ) * (1 - retention))
      ((onePacketModel setup runtime leaks bounds initial horizon scheduler).runBehavioralFrom
        (honestProfile setup runtime leaks bounds initial horizon scheduler assessment) fuel start)
      ((onePacketModel setup runtime leaks bounds initial horizon scheduler).runBehavioralFrom
        profile fuel start) :=
  (InformationModel.runBehavioralFrom_withinTV_of_supported_choices
    (onePacketModel setup runtime leaks bounds initial horizon scheduler) _ profile retention
      nonnegative
    le_one start dominates fuel).mono (one_sub_pow_le_mul nonnegative _)

/-- **The whole run near as-if-honest play.** From initialization, a profile
dominating as-if-honest play with retention `retention ∈ [0, 1]` has a run
within `|Player| * fuel * (1 - retention)` in total variation of the
as-if-honest run. -/
theorem onePacket_withinTV_honest
    (assessment : setup.intendedModel.BehavioralAssessment) {retention : ℝ}
    (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (profile : ∀ who,
      (onePacketModel setup runtime leaks bounds initial horizon scheduler).BehavioralPolicy who)
    (dominates : DominatesHonestFrom setup runtime leaks bounds initial horizon scheduler assessment
      retention profile ((bounds.onePacketMenu runtime leaks).protocol initial horizon
        scheduler).initHistory) (fuel : Nat) :
    PMF.WithinTV ((Fintype.card Player * fuel : ℕ) * (1 - retention))
      ((onePacketModel setup runtime leaks bounds initial horizon scheduler).runBehavioral
        (honestProfile setup runtime leaks bounds initial horizon scheduler assessment) fuel)
      ((onePacketModel setup runtime leaks bounds initial horizon scheduler).runBehavioral
        profile fuel) :=
  onePacket_continuation_withinTV_honest setup runtime leaks bounds initial horizon scheduler
    assessment
    nonnegative le_one profile _ dominates fuel

end Law

section Readout

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- A native history's optional terminal source configuration and actual
fixed-exit payoff, including defaults before a terminal readout is available. -/
def readoutExclusion
    (final : ((bounds.onePacketMenu runtime leaks).protocol initial horizon
      scheduler).History) :
    Option (Config Player L setup.program.terminalCtx) × (Player → ℝ) :=
  (sourceReadout setup runtime leaks final.state,
    exclusionBase setup runtime parameter utility excludedPayoff leaks final.state)

/-- Equality with a complete intended readout law identifies the honest joint
readout and payoff law. Complete readouts follow internally from the canonical
source horizon; no native initialization or success premise is needed. -/
theorem onePacket_honest_readout_exclusion_law
    (assessment : setup.intendedModel.BehavioralAssessment)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) (targetFuel : Nat)
    (honestLaw : ((onePacketModel setup runtime leaks bounds initial horizon
      scheduler).runBehavioral
        (honestProfile setup runtime leaks bounds initial horizon scheduler assessment)
        targetFuel).map (fun final => sourceReadout setup runtime leaks final.state) =
      (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
        (fun final => setup.protocolReadout final.state)) :
    ((onePacketModel setup runtime leaks bounds initial horizon scheduler).runBehavioral
        (honestProfile setup runtime leaks bounds initial horizon scheduler assessment)
        targetFuel).map
        (readoutExclusion setup runtime leaks bounds initial horizon scheduler parameter utility
          excludedPayoff) =
      (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  have sourceSome (final : setup.intendedProtocol.History)
      (supported : final ∈ (setup.intendedModel.runBehavioral intended
        (instructionCount setup.program + 1)).support) :
      ∃ terminal, setup.protocolReadout final.state = some terminal := by
    let certificate := setup.intended_bounded.wellFoundedHistories
    have terminal := setup.intendedModel.runBehavioralTerminalFrom_support_terminal certificate
      intended setup.intendedProtocol.initHistory final (by
        rw [setup.intendedModel.runBehavioralTerminalFrom_initHistory certificate intended
          setup.intended_bounded]
        exact supported)
    change final.state.elim False (ProtocolState.terminal setup.program) at terminal
    cases current : final.state with
    | none => simp only [current, Option.elim_none] at terminal
    | some point =>
        have stopped : ProtocolState.terminal setup.program point := by
          simpa only [current, Option.elim_some] using terminal
        obtain ⟨result, read⟩ :=
          ProtocolState.exists_readout_of_terminal setup.program point stopped
        exact ⟨result, by
          simpa only [Setup.protocolReadout, current, Option.bind_some] using read⟩
  let attach := fun readout : Option (Config Player L setup.program.terminalCtx) =>
    (readout, exclusionReadoutUtility setup parameter utility excludedPayoff readout)
  have source : intendedReadoutExclusion setup parameter utility excludedPayoff =
      attach ∘ fun final => setup.protocolReadout final.state := rfl
  rw [source, ← PMF.map_comp, ← honestLaw, PMF.map_comp]
  apply map_congr_on_support
  intro final supported
  have observed : sourceReadout setup runtime leaks final.state ∈
      (((onePacketModel setup runtime leaks bounds initial horizon scheduler).runBehavioral
        (honestProfile setup runtime leaks bounds initial horizon scheduler assessment)
        targetFuel).map (fun last => sourceReadout setup runtime leaks last.state)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
  rw [honestLaw] at observed
  obtain ⟨original, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp observed
  obtain ⟨terminal, read⟩ := sourceSome original reached
  have nativeRead : sourceReadout setup runtime leaks final.state = some terminal :=
    same.symm.trans read
  apply Prod.ext
  · rfl
  · funext who
    exact exclusionBase_eq_readout_of_readout setup runtime parameter utility excludedPayoff leaks
      final.state terminal nativeRead who

/-- **The readout and exclusion law under trembles.** At the complete intended
source budget, an exact honest readout law gives the intended joint law within
`|Player| * targetFuel * (1 - retention)` for every dominated native profile. -/
theorem onePacket_readout_exclusion_withinTV
    (assessment : setup.intendedModel.BehavioralAssessment)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) (targetFuel : Nat)
    (honestLaw : ((onePacketModel setup runtime leaks bounds initial horizon
      scheduler).runBehavioral
        (honestProfile setup runtime leaks bounds initial horizon scheduler assessment)
        targetFuel).map (fun final => sourceReadout setup runtime leaks final.state) =
      (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
        (fun final => setup.protocolReadout final.state))
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (profile : ∀ who,
      (onePacketModel setup runtime leaks bounds initial horizon scheduler).BehavioralPolicy who)
    (dominates : DominatesHonestFrom setup runtime leaks bounds initial horizon scheduler assessment
      retention profile ((bounds.onePacketMenu runtime leaks).protocol initial horizon
        scheduler).initHistory) :
    PMF.WithinTV ((Fintype.card Player * targetFuel : ℕ) * (1 - retention))
      (((onePacketModel setup runtime leaks bounds initial horizon scheduler).runBehavioral profile
        targetFuel).map
          (readoutExclusion setup runtime leaks bounds initial horizon scheduler parameter utility
            excludedPayoff))
      ((setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff)) := by
  have joint := onePacket_honest_readout_exclusion_law setup runtime leaks bounds initial horizon
    scheduler parameter utility excludedPayoff assessment intended targetFuel honestLaw
  have close := ((onePacket_withinTV_honest setup runtime leaks bounds initial horizon scheduler
    assessment nonnegative le_one profile dominates targetFuel).map
      (readoutExclusion setup runtime leaks bounds initial horizon scheduler parameter utility
        excludedPayoff)).symm
  rw [joint] at close
  exact close

end Readout

end Vegas
