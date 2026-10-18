/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperAssessedFrameLaw
import Interaction.ReactiveSchedulerStoppedSeed

/-! # The original service seed in the actual assessed helper continuation -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- The actual initialized helper frame has the original service posterior,
even when its material contains a different private preparation or evidence alias. -/
theorem initial_helper_frame_seed_posterior (hidden : Player)
    (material : WitnessedSubmission graph) :
    implementation.posterior (initialHelperFrame hidden material).environmentRecall =
      nativeSeedLaw := by
  let players : Player → app.Policy := fun owner _ _ =>
    PMF.pure (if owner = hidden then ⟨some material⟩ else ⟨none⟩)
  let reference : Seeds := Classical.choice (inferInstance : Nonempty Seeds)
  have reached : initialHelperFrame hidden material ∈
      (app.runRounds (family reference) players 5 initialExecution).support := by
    rw [first_five_rounds]
    simp only [players, PMF.pure_bind, PMF.pure_map]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  exact initial_frame_original_seed_posterior players reference _ reached

open Classical in
/-- Silencing an already-sent helper before original retirement preserves
the joint law of the complete stopped execution and the SAME original seed.
The conditional seed law at each stopping point is the actual updated posterior. -/
theorem assessed_sent_helper_original_stopped_seed_law
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (hidden : Player) (material : WitnessedSubmission graph) (count remaining : Nat)
    (trace : countedProtocol.Trace
      (some ⟨remaining + count, none, initialHelperFrame hidden material⟩))
    (sent : ∃ message ∈ initialPublicPackets (initialHelperFrame hidden material),
      PhaseCount.event? message.payload = some (originalCoordinate hidden)) :
    (nativeSeedLaw.bind fun seed =>
      (app.runUntil (family seed)
        (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        (fun current => current.application.attempt ≠ originalAttempt)
        count (initialHelperFrame hidden material)).map fun next => (seed, next)) =
    (nativeSeedLaw.bind fun seed =>
      (app.runUntil (family seed)
        (Function.update (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
          hidden (fun _ _ => PMF.pure ⟨none⟩))
        (fun current => current.application.attempt ≠ originalAttempt)
        count (initialHelperFrame hidden material)).map fun next => (seed, next)) := by
  classical
  let players := rawMenu.decodeProfile initial horizon scheduler assessment.strategy
  let forced := Function.update players hidden (fun _ _ => PMF.pure ⟨none⟩)
  let stop := fun current : app.Execution => current.application.attempt ≠ originalAttempt
  have actual := app.schedulerMixture_runUntil_joint nativeSeedLaw family players stop
    count (initialHelperFrame hidden material)
  have silent := app.schedulerMixture_runUntil_joint nativeSeedLaw family forced stop
    count (initialHelperFrame hidden material)
  change (implementation.posterior _).bind _ =
    (app.runUntil scheduler players stop count _).bind _ at actual
  change (implementation.posterior _).bind _ =
    (app.runUntil scheduler forced stop count _).bind _ at silent
  rw [initial_helper_frame_seed_posterior] at actual silent
  have same := assessed_sent_helper_original_stopped_law assessment equilibrium hidden count
    remaining _ trace (initial_helper_public_sent hidden material sent)
  change app.runUntil scheduler players stop count _ =
    app.runUntil scheduler forced stop count _ at same
  have joint := actual.trans ((congrArg (fun law => law.bind fun next =>
    (implementation.posterior next.environmentRecall).map (Prod.mk next)) same).trans silent.symm)
  have swapped := congrArg (fun law => law.map Prod.swap) joint
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, Prod.swap] using swapped

open Classical in
/-- At every supported original seed, the incumbent and forced-WAIT helper
have the same stopped physical law. This is disintegrated from the actual
initialized tagged joint, rather than postulated seedwise policy agreement. -/
theorem assessed_sent_helper_fixed_original_stopped_law
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (hidden : Player) (material : WitnessedSubmission graph) (count remaining : Nat)
    (trace : countedProtocol.Trace
      (some ⟨remaining + count, none, initialHelperFrame hidden material⟩))
    (sent : ∃ message ∈ initialPublicPackets (initialHelperFrame hidden material),
      PhaseCount.event? message.payload = some (originalCoordinate hidden))
    (seed : Seeds) (supported : seed ∈ nativeSeedLaw.support) :
    app.runUntil (family seed)
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      (fun current => current.application.attempt ≠ originalAttempt)
      count (initialHelperFrame hidden material) =
    app.runUntil (family seed)
      (Function.update (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        hidden (fun _ _ => PMF.pure ⟨none⟩))
      (fun current => current.application.attempt ≠ originalAttempt)
      count (initialHelperFrame hidden material) := by
  classical
  have joint := assessed_sent_helper_original_stopped_seed_law assessment equilibrium hidden
    material count remaining trace sent
  change bindPairLaw nativeSeedLaw _ = bindPairLaw nativeSeedLaw _ at joint
  apply PMF.ext
  intro final
  have mass := congrArg (fun law => law (seed, final)) joint
  simp only [bindPairLaw_apply] at mass
  have normalized := congrArg (fun value => (nativeSeedLaw seed)⁻¹ * value) mass
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel ((PMF.mem_support_iff _ _).mp supported)
    (PMF.apply_ne_top _ _), one_mul] using normalized

/-- The original seed remains explicit in the full native round law.
Post-retirement observations are killed, but their original seed is retained;
no publication or retry behavior is identified between private aliases. -/
theorem assessed_sent_helper_fixed_original_observation_law
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (hidden : Player) (material : WitnessedSubmission graph) (count remaining : Nat)
    (trace : countedProtocol.Trace
      (some ⟨remaining + count, none, initialHelperFrame hidden material⟩))
    (sent : ∃ message ∈ initialPublicPackets (initialHelperFrame hidden material),
      PhaseCount.event? message.payload = some (originalCoordinate hidden))
    (seed : Seeds) (supported : seed ∈ nativeSeedLaw.support) :
    (app.runRounds (family seed)
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      count (initialHelperFrame hidden material)).map (originalHelperObservation hidden) =
    (app.runRounds (family seed)
      (Function.update (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        hidden (fun _ _ => PMF.pure ⟨none⟩))
      count (initialHelperFrame hidden material)).map (originalHelperObservation hidden) := by
  classical
  obtain ⟨fixed⟩ := initial_helper_frame_native_trace seed hidden material
  have originalFuel := app.raw_trace_horizon initial horizon scheduler
    (countedMenu.toRawTrace initial horizon scheduler trace)
  have fixedFuel := app.raw_trace_horizon initial horizon (family seed) fixed
  have equal : remaining + count = horizon - 5 := by
    change (initialHelperFrame hidden material).environmentRecall.length +
      (remaining + count) = horizon at originalFuel
    change (initialHelperFrame hidden material).environmentRecall.length +
      (horizon - 5) = horizon at fixedFuel
    omega
  have aligned : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining + count, none, initialHelperFrame hidden material⟩) := by
    rw [equal]
    exact fixed
  rw [original_observation_rounds_stopped (family seed) _ hidden count remaining _ aligned,
    original_observation_rounds_stopped (family seed) _ hidden count remaining _ aligned,
    assessed_sent_helper_fixed_original_stopped_law assessment equilibrium hidden material
      count remaining trace sent seed supported]

/-- The same original seed and its full observable continuation remain in
the joint law across private preparation aliases. No new seed draw appears
after conditioning the initialized frame. -/
theorem initial_helper_assessed_original_seed_law
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (hidden : Player) (count : Nat) (bounded : count ≤ 19)
    (first second : WitnessedSubmission graph)
    (firstTrace : countedProtocol.Trace
      (some ⟨horizon - 5, none, initialHelperFrame hidden first⟩))
    (secondTrace : countedProtocol.Trace
      (some ⟨horizon - 5, none, initialHelperFrame hidden second⟩))
    (firstSent : ∃ message ∈ initialPublicPackets (initialHelperFrame hidden first),
      PhaseCount.event? message.payload = some (originalCoordinate hidden))
    (secondSent : ∃ message ∈ initialPublicPackets (initialHelperFrame hidden second),
      PhaseCount.event? message.payload = some (originalCoordinate hidden))
    (packet : app.packet (app.submit (initialCallback hidden).application hidden first) hidden
        ((initialCallback hidden).network.known hidden) first =
      app.packet (app.submit (initialCallback hidden).application hidden second) hidden
        ((initialCallback hidden).network.known hidden) second) :
    (nativeSeedLaw.bind fun seed =>
      ((app.runRounds (family seed)
        (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) count
        (initialHelperFrame hidden first)).map (originalHelperObservation hidden)).map
        fun observation => (seed, observation)) =
    (nativeSeedLaw.bind fun seed =>
      ((app.runRounds (family seed)
        (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) count
        (initialHelperFrame hidden second)).map (originalHelperObservation hidden)).map
        fun observation => (seed, observation)) := by
  let players := rawMenu.decodeProfile initial horizon scheduler assessment.strategy
  let forced := Function.update players hidden (fun _ _ => PMF.pure ⟨none⟩)
  have fuel : (horizon - 5 - count) + count = horizon - 5 := by
    change (128 - 5 - count) + count = 128 - 5
    omega
  have firstAligned : countedProtocol.Trace
      (some ⟨(horizon - 5 - count) + count, none, initialHelperFrame hidden first⟩) := by
    rw [fuel]
    exact firstTrace
  have secondAligned : countedProtocol.Trace
      (some ⟨(horizon - 5 - count) + count, none, initialHelperFrame hidden second⟩) := by
    rw [fuel]
    exact secondTrace
  apply bind_congr_on_support
  intro seed supported
  have firstSame := assessed_sent_helper_fixed_original_observation_law assessment equilibrium
    hidden first count (horizon - 5 - count) firstAligned firstSent seed supported
  have secondSame := assessed_sent_helper_fixed_original_observation_law assessment equilibrium
    hidden second count (horizon - 5 - count) secondAligned secondSent seed supported
  have aliases := initial_helper_original_run_law seed forced hidden
    (by intro past view; dsimp only [forced]; rw [Function.update_self])
    count bounded first second packet
  exact congrArg (fun law => law.map fun observation => (seed, observation))
    (firstSame.trans (aliases.trans secondSame.symm))

end Vegas.Examples.CommitSeedBroadcast
