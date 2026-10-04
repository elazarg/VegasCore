/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstTurnRankFactorization
import Vegas.Game.SourceServiceOriginalPrefixRetraction
import Vegas.Game.DisclosureProfileJointChannel

/-! # One original source carrier and actual traffic at completion ranks

The actual normalized first-turn rank law is followed by the common all-owner
memory lottery. Its original source marginal and traffic channel retain the
same initial parameter, execution, and full traffic sample. The channel reads
the compressed original focal view. Restored histories are auxiliary source
data and do not replace physical native recall.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The real normalized rank execution and one common restoration draw have
the original source prefix law with the same initial parameter and traffic.
The actual effective traffic kernel is derived from runtime rank induction;
its transport through restored memories uses source recall compression. -/
theorem sourceServiceFirstTurn_original_rank_traffic_law {Parameter : Type}
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (parameter : State L setup.context → Parameter) (focal : Player)
    (rank : Nat) (within : rank ≤ (graph setup).order.eventCount) :
    ∃ noise : ProtocolView focal setup.program → PMF _,
      (setup.initialLaw.bind fun initial =>
        ((application setup leaks).runUntilHorizon scheduler
          (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
            (normalizeDisclosureProfile setup.program []
              (Revelations.initial setup.context) profile))
          (sourceServiceRankCompleted rank) horizon
          (.initial (application setup leaks)
            (EventGraphRuntime.State.initial (setup.eventInputs initial)))).bind fun execution =>
              (sourceServiceOriginalPrefixCarrier profile initial rank execution).map
                fun original => ((parameter initial, original),
                  (runtime setup).bindingTraffic leaks focal execution)) =
        (setup.initialLaw.bind fun initial =>
          ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[rank]
            (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map
              fun original => (parameter initial, original)).bind fun carried =>
          (noise (ProtocolView.normalizeDisclosureRecall setup.program (fun view => view.2)
            (ProtocolState.observe focal setup.program carried.2))).map
              fun extra => (carried, extra) := by
  classical
  let app := application setup leaks
  let normalized := normalizeDisclosureProfile setup.program []
    (Revelations.initial setup.context) profile
  have effective (who : Player) : (normalized who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context) :=
    (profile who).normalizeDisclosureFrom_effective setup.program []
      (Revelations.initial setup.context) (fun view => PMF.pure view.2)
  let native := fun initial : State L setup.context => app.runUntilHorizon scheduler
    (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) normalized)
    (sourceServiceRankCompleted rank) horizon
    (.initial app (EventGraphRuntime.State.initial (setup.eventInputs initial)))
  obtain ⟨rankNoise, factor⟩ := sourceServiceFirstTurn_rank_traffic_law (turns := turns)
    contract timely normalized effective parameter focal rank within
  let noise := fun view : ProtocolView focal setup.program => rankNoise (some view)
  let restore : setup.ProtocolState → PMF (ProtocolState setup.program) := fun decoded =>
    match decoded with
    | none => PMF.pure (ProtocolState.entry setup.program
        (setup.initialConfig setup.initialLaw.support_nonempty.choose))
    | some before => profile.restoreDisclosureMemory setup.program []
        (Revelations.initial setup.context) before
  have carrier initial (supported : initial ∈ setup.initialLaw.support) execution
      (reached : execution ∈ (native initial).support) :
      restore (sourceServicePrefix? setup rank execution.application.config) =
        sourceServiceOriginalPrefixCarrier profile initial rank execution := by
    have law := (sourceServiceFirstTurn_rank_law (turns := turns) contract timely normalized
      effective initial supported rank within).2
    have decoded : sourceServicePrefix? setup rank execution.application.config ∈
        (((fun law => law.bind (ProtocolState.behavioralStateStep setup.program normalized))^[rank]
          (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map
            some).support := by
      rw [← law, PMF.support_map]
      exact ⟨execution, reached, rfl⟩
    obtain ⟨before, _beforeSupport, decoderEq⟩ := PMF.support_map .. ▸ decoded
    unfold sourceServiceOriginalPrefixCarrier
    rw [← decoderEq]
  have lifted := congrArg (fun law => law.bind (fun point =>
    (restore point.1.2).map fun original => ((point.1.1, original), point.2))) factor
  have nativeLift :
      ((setup.initialLaw.bind fun initial => (native initial).map fun execution =>
        ((parameter initial, sourceServicePrefix? setup rank execution.application.config),
          (runtime setup).bindingTraffic leaks focal execution)).bind fun point =>
            (restore point.1.2).map fun original => ((point.1.1, original), point.2)) =
        (setup.initialLaw.bind fun initial => (native initial).bind fun execution =>
          (sourceServiceOriginalPrefixCarrier profile initial rank execution).map
            fun original => ((parameter initial, original),
              (runtime setup).bindingTraffic leaks focal execution)) := by
    simp only [PMF.bind_bind, PMF.bind_map]
    apply bind_congr_on_support _
    intro initial supported
    apply bind_congr_on_support _
    intro execution reached
    dsimp only [Function.comp_def]
    rw [carrier initial supported execution reached]
  have registryEq config (supported : config ∈ (setup.initialLaw.map setup.initialConfig).support) :
      config.registry = [] := by
    obtain ⟨initial, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    rfl
  have revelationsEq config
      (supported : config ∈ (setup.initialLaw.map setup.initialConfig).support) :
      (config.revelations : Revelations setup.context) =
        @Revelations.initial Player L setup.context := by
    obtain ⟨initial, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    rfl
  have sourceChannel := normalizeDisclosureProfile_prefix_channel_joint_law setup.program
    profile [] (Revelations.initial setup.context) (setup.initialLaw.map setup.initialConfig)
    registryEq revelationsEq (fun config => parameter config.state) rank focal noise
  have pairedChannel := congrArg
    (PMF.map fun selected => ((selected.1, selected.2.1), selected.2.2)) sourceChannel
  refine ⟨noise, ?_⟩
  change (setup.initialLaw.bind fun initial => (native initial).bind fun execution =>
    (sourceServiceOriginalPrefixCarrier profile initial rank execution).map
      fun original => ((parameter initial, original),
        (runtime setup).bindingTraffic leaks focal execution)) = _
  rw [← nativeLift]
  rw [lifted]
  simpa only [app, normalized, restore, noise, PMF.map_bind, PMF.bind_map, PMF.bind_bind,
    PMF.map_comp, Function.comp_def, Option.map_some, SourceProgram.Setup.initialConfig] using
      pairedChannel

end Vegas
