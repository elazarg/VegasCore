/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceOriginalRankTraffic
import Vegas.Game.SourceServiceFirstActivationFactorization

/-! # Original source prefixes and actual first owner inputs

The common all-owner restoration draw remains paired with the actual native
rank endpoint and the same initial parameter. Public scheduler waiting then
reaches the owner's real before-response input. Its channel reads only the
compressed original source observation, and contract completeness gives total
mass on actual inputs. The carrier is auxiliary source data; it is not substituted
for physical private recall or an assumed native posterior.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The actual first-ready-owner input is a source-view channel of the true
original behavioral prefix, retaining the same correlated initial parameter.
The input is recovered from actual own recall after integrating the response
draw; it includes the partial network sample available before that response. -/
theorem sourceServiceFirstTurn_original_first_input_law {Parameter : Type}
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (parameter : State L setup.context → Parameter)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner) :
    ∃ channel : ProtocolView owner setup.program → PMF (application setup leaks).Info,
      (setup.initialLaw.bind fun initial =>
        ((application setup leaks).runUntilHorizon scheduler
          (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
            (normalizeDisclosureProfile setup.program []
              (Revelations.initial setup.context) profile))
          (sourceServiceRankCompleted event.val) horizon
          (.initial (application setup leaks)
            (EventGraphRuntime.State.initial (setup.eventInputs initial)))).bind fun execution =>
          (sourceServiceOriginalPrefixCarrier profile initial event.val execution).bind
            fun original =>
              ((application setup leaks).runUntilHorizon scheduler
                (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
                  (normalizeDisclosureProfile setup.program []
                    (Revelations.initial setup.context) profile))
                (fun final => sourceServiceTurnInput? setup leaks owner event (final.recall owner) ≠
                  none) horizon execution).map fun final =>
                    ((parameter initial, original), sourceServiceTurnInput? setup leaks owner event
                      (final.recall owner))) =
        ((setup.initialLaw.bind fun initial =>
          ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))
            ^[event.val]
            (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map
              fun original => (parameter initial, original)).bind fun carried =>
            (channel (ProtocolView.normalizeDisclosureRecall setup.program (fun view => view.2)
              (ProtocolState.observe owner setup.program carried.2))).map
                fun input => (carried, input)) ∧
      ∀ carried ∈ (setup.initialLaw.bind fun initial =>
          ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))
            ^[event.val]
            (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map
              fun original => (parameter initial, original)).support,
        (channel (ProtocolView.normalizeDisclosureRecall setup.program (fun view => view.2)
          (ProtocolState.observe owner setup.program carried.2))).map Option.isSome =
            PMF.pure true := by
  classical
  let app := application setup leaks
  let normalized := normalizeDisclosureProfile setup.program []
    (Revelations.initial setup.context) profile
  let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    normalized
  let native := fun initial : State L setup.context => app.runUntilHorizon scheduler players
    (sourceServiceRankCompleted event.val) horizon (.initial app
      (EventGraphRuntime.State.initial (setup.eventInputs initial)))
  let prior := setup.initialLaw.bind fun initial => (native initial).bind fun execution =>
    (sourceServiceOriginalPrefixCarrier profile initial event.val execution).map
      fun original => (initial, execution, original)
  let source := fun seed : State L setup.context × app.Execution × ProtocolState setup.program =>
    (parameter seed.1, seed.2.2)
  let observe := fun carried : Parameter × ProtocolState setup.program =>
    ProtocolView.normalizeDisclosureRecall setup.program (fun view => view.2)
      (ProtocolState.observe owner setup.program carried.2)
  let originalLaw := setup.initialLaw.bind fun initial =>
    ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[event.val]
      (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map
        fun original => (parameter initial, original)
  have rankWithin : event.val ≤ (graph setup).order.eventCount := Nat.le_of_lt event.isLt
  have effective (who : Player) : (normalized who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context) :=
    (profile who).normalizeDisclosureFrom_effective setup.program []
      (Revelations.initial setup.context) (fun view => PMF.pure view.2)
  have supported seed (reached : seed ∈ prior.support) :
      seed.1 ∈ setup.initialLaw.support ∧ seed.2.1 ∈ (native seed.1).support := by
    rw [PMF.mem_support_bind_iff] at reached
    obtain ⟨initial, initialSupport, reached⟩ := reached
    rw [PMF.mem_support_bind_iff] at reached
    obtain ⟨execution, reached, restored⟩ := reached
    rw [PMF.support_map] at restored
    obtain ⟨original, restored, equal⟩ := restored
    cases equal
    exact ⟨initialSupport, reached⟩
  have resources seed (reached : seed ∈ prior.support) :=
    (sourceServiceFirstTurn_rank_law (turns := turns) contract timely normalized effective
      seed.1 (supported seed reached).1 event.val rankWithin).1 seed.2.1
        (supported seed reached).2
  have marginal : prior.map source = originalLaw := by
    simpa only [prior, source, native, app, players, normalized, originalLaw, PMF.map_bind,
      PMF.map_comp, Function.comp_def] using
      sourceServiceFirstTurn_original_prefix_joint_law (turns := turns) contract timely profile
        parameter event.val rankWithin
  obtain ⟨noise, trafficLaw⟩ := sourceServiceFirstTurn_original_rank_traffic_law
    (turns := turns) contract timely profile parameter owner event.val rankWithin
  have factor : prior.map (fun seed => (source seed,
      (runtime setup).bindingTraffic leaks owner seed.2.1)) =
        (prior.map source).bind fun carried => (noise (observe carried)).map
          fun extra => (carried, extra) := by
    rw [marginal]
    simpa only [prior, source, native, app, players, normalized, originalLaw, observe,
      PMF.map_bind, PMF.map_comp, Function.comp_def] using trafficLaw
  obtain ⟨channel, law, total⟩ := sourceServiceFirstActivation_input_factorization setup leaks
    contract timely turns normalized owner event owned prior source observe (fun seed => seed.2.1)
    (fun seed reached => (resources seed reached).2)
    (fun seed reached => (resources seed reached).1) noise factor
  refine ⟨channel, ?_, ?_⟩
  · rw [marginal] at law
    simpa only [prior, source, native, app, players, normalized, originalLaw, observe,
      PMF.bind_bind, PMF.bind_map, Function.comp_def] using law
  · intro carried carriedSupport
    exact total carried (by rw [marginal]; exact carriedSupport)

end Vegas
