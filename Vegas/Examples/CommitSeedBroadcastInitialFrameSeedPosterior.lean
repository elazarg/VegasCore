/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialPublicLaw

/-! # The original service posterior at the actual initialized prepared frames -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- The original five-command experiment has not read any service seed.
This identifies the existing scheduler posterior at every actual frame;
it does not replace its memory by a new independent draw. -/
theorem initial_frame_original_seed_posterior (players : Player → app.Policy)
    (reference : Seeds) (frame : app.Execution)
    (reached : frame ∈ (app.runRounds (family reference) players 5 initialExecution).support) :
    implementation.posterior frame.environmentRecall = nativeSeedLaw := by
  have actual := app.schedulerMixture_joint nativeSeedLaw family players 5 initialState
  have actualJoint :
      (nativeSeedLaw.bind fun seed =>
        (app.runRounds (family seed) players 5 initialExecution).map fun next => (next, seed)) =
      bindPairLaw (app.runRounds scheduler players 5 initialExecution)
        (fun next => implementation.posterior next.environmentRecall) := by
    simpa only [initialExecution, implementation, scheduler, bindPairLaw] using actual
  have factor := actualJoint.symm.trans (initial_public_prefix_joint players reference)
  have physical : app.runRounds scheduler players 5 initialExecution =
      app.runRounds (family reference) players 5 initialExecution := by
    have marginal := congrArg (fun law => law.map Prod.fst) factor
    simpa only [bindPairLaw_map_fst] using marginal
  rw [physical] at factor
  apply PMF.ext
  intro seed
  have mass := congrArg (fun law => law (frame, seed)) factor
  simp only [bindPairLaw_apply] at mass
  have normalized := congrArg
    (fun value => ((app.runRounds (family reference) players 5 initialExecution) frame)⁻¹ * value)
    mass
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel ((PMF.mem_support_iff _ _).mp reached)
    (PMF.apply_ne_top _ _), one_mul] using normalized

/-- Continuation from the actual prepared frame uses its derived original
posterior, with the same service seed throughout the existing native runner. -/
theorem initial_frame_original_continuation (initialPlayers players : Player → app.Policy)
    (reference : Seeds) (frame : app.Execution)
    (reached : frame ∈
      (app.runRounds (family reference) initialPlayers 5 initialExecution).support)
    (count : Nat) :
    (nativeSeedLaw.bind fun seed => app.runRounds (family seed) players count frame) =
      app.runRounds scheduler players count frame := by
  have actual := implementation.realize players count frame
  rw [initial_frame_original_seed_posterior initialPlayers reference frame reached] at actual
  have identity (law : PMF app.Execution) : law.map (fun next => next) = law := PMF.map_id law
  simpa only [implementation, scheduler, app.schedulerMixture_runJoint,
    PMF.map_bind, PMF.map_comp, Function.comp_def, identity] using actual

end Vegas.Examples.CommitSeedBroadcast
