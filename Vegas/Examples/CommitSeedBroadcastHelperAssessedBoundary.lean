/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperAssessedOriginalSeed

/-! # The original seed and full native information at actual original retirement -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

open Classical in
/-- The immutable original seed and the COMPLETE stopped external observation
are preserved across counted initial preparation aliases. In particular the
focal clock-three record is retained even on the all-admitted retirement branch. -/
theorem initial_helper_assessed_boundary_seed_law
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
      ((app.runUntil (family seed)
        (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        (fun current => current.application.attempt ≠ originalAttempt)
        count (initialHelperFrame hidden first)).map
          (phaseExternalObservation runtime leaks hidden)).map fun observation =>
            (seed, observation)) =
    (nativeSeedLaw.bind fun seed =>
      ((app.runUntil (family seed)
        (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        (fun current => current.application.attempt ≠ originalAttempt)
        count (initialHelperFrame hidden second)).map
          (phaseExternalObservation runtime leaks hidden)).map fun observation =>
            (seed, observation)) := by
  classical
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
  have firstSame := assessed_sent_helper_fixed_original_stopped_law assessment equilibrium
    hidden first count (horizon - 5 - count) firstAligned firstSent seed supported
  have secondSame := assessed_sent_helper_fixed_original_stopped_law assessment equilibrium
    hidden second count (horizon - 5 - count) secondAligned secondSent seed supported
  have aliases := initial_helper_original_stopped_law seed forced hidden
    (by intro past view; dsimp only [forced]; rw [Function.update_self])
    count bounded first second packet
  exact congrArg (fun law => law.map fun observation => (seed, observation))
    ((congrArg (fun law => law.map (phaseExternalObservation runtime leaks hidden)) firstSame).trans
      (aliases.trans (congrArg (fun law => law.map
        (phaseExternalObservation runtime leaks hidden)) secondSame).symm))

end Vegas.Examples.CommitSeedBroadcast
