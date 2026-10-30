/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketComponents
import Vegas.Game.OnePacketDebtRouting
import Vegas.Game.SourceDebtContinuation

/-! # Indifference at native decision sites carrying source debt

Own debt is uniform throughout the actual information fiber. Complete native
continuations therefore give every whole policy the same declared exit value.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)
  [Fintype ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
    scheduler).History]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler

/-- One own-debt witness fixes own debt throughout the actual information
fiber, for every source profile. -/
theorem owingAgent_allHistories (profile : BehavioralProfile setup.program) {who : Player}
    (site : (N).InformationSite who)
    (owing : OwingAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    (history : (N).InformationHistory who site.1) :
    DecodedState setup runtime leaks profile (ProtocolState.OwesFailure who setup.program)
      history.1.state := by
  obtain ⟨first, point, decoded, owes⟩ := owing
  let rawSite := (menu).rawSite (initialLaw setup) horizon scheduler who site
  obtain ⟨_witness, _running, response, permitted⟩ := rawSite.2
  have someInfo : site.1.isSome = true := by
    change (some response).isSome = site.1.isSome at permitted
    exact permitted.symm
  obtain ⟨data, input⟩ := Option.isSome_iff_exists.mp someInfo
  exact decodedState_owesFailure_of_infoOf (runtime := runtime) profile
    ⟨first.1, first.2.trans input⟩ decoded owes ⟨history.1, history.2.trans input⟩

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- Every whole-policy deviation at a site carrying own source debt has zero
native base-utility gain, under any assessment at that site. -/
theorem owingAgent_gain_eq_zero
    (completes : CompletesPlay runtime leaks (initialLaw setup) horizon scheduler)
    (certificate : (E).WellFoundedHistories)
    (assessment : (N).BehavioralAssessment) {who : Player}
    (deviation : (N).AssessmentDeviation who)
    (owing : OwingAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt deviation.1)) :
    expect ((N).assessmentComparisonWith ((N).runBehavioralTerminalFrom certificate)
      (fun final => final.state) assessment who deviation).alternative
        (fun state => exclusionBase setup runtime parameter utility excludedPayoff leaks
          state who) -
    expect ((N).assessmentComparisonWith ((N).runBehavioralTerminalFrom certificate)
      (fun final => final.state) assessment who deviation).prescribed
        (fun state => exclusionBase setup runtime parameter utility excludedPayoff leaks
          state who) = 0 := by
  exact exclusionBase_gain_eq_zero_of_owesFailure parameter utility excludedPayoff (menu) horizon
    scheduler completes certificate assessment deviation
    (fun history _supported => owingAgent_allHistories setup runtime leaks bounds horizon scheduler
      (failureProfile setup.program) deviation.1 owing history)

/-- At a site carrying own source debt, every whole continuation policy has
exactly the assessed native continuation value. -/
theorem owingAgent_value_eq
    (completes : CompletesPlay runtime leaks (initialLaw setup) horizon scheduler)
    (certificate : (E).WellFoundedHistories)
    (assessment : (N).BehavioralAssessment) {who : Player} (site : (N).InformationSite who)
    (owing : OwingAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    (alternative : (N).BehavioralPolicy who) :
    (assessment.continuationContext certificate site
      (fun final => exclusionBase setup runtime parameter utility excludedPayoff leaks
        final.state who)).value alternative =
    (assessment.continuationContext certificate site
      (fun final => exclusionBase setup runtime parameter utility excludedPayoff leaks
        final.state who)).value (assessment.strategy who) := by
  apply sub_eq_zero.mp
  have zero := owingAgent_gain_eq_zero setup runtime leaks bounds horizon scheduler parameter
    utility excludedPayoff completes certificate assessment (site, alternative) owing
  simpa only [BehavioralAssessment.continuationContext_value,
    InformationModel.assessmentComparisonWith, InformationModel.assessmentLawWith, expect_map,
    Function.comp_def] using zero

/-- The local-law gain at a site carrying own source debt is exactly zero. -/
theorem owingAgent_localGain_eq_zero
    (completes : CompletesPlay runtime leaks (initialLaw setup) horizon scheduler)
    (assessment : (N).BehavioralAssessment) {who : Player} (site : (N).InformationSite who)
    (owing : OwingAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    (law : PMF ((N).Choice who site.1)) :
    localGain (2 * horizon + 1) (fun final => final.state)
      (exclusionBase setup runtime parameter utility excludedPayoff leaks) assessment site law =
        0 := by
  rw [localGain_eq_sub]
  simp only [localValue_eq_continuationContext (2 * horizon + 1) (fun final => final.state)
    (exclusionBase setup runtime parameter utility excludedPayoff leaks) assessment site
    ((menu).bounded (initialLaw setup) horizon scheduler), BehavioralPolicy.withLaw_eq_self]
  exact sub_eq_zero.mpr (owingAgent_value_eq setup runtime leaks bounds horizon scheduler parameter
    utility excludedPayoff completes ((menu).bounded (initialLaw setup) horizon
      scheduler).wellFoundedHistories assessment site owing
    ((assessment.strategy who).withLaw site.1 law))

end Vegas
