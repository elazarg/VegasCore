/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterContinuation
import Vegas.Game.ServiceRosterEvaluation
import Interaction.ReactiveRestrictedContinuation
import Vegas.Game.SourceContinuation

/-! # Initialized source law of the finite roster perturbations

The finite behavioral game, complete physical service plan, and original source
runner have the same complete typed outcome law. The native readout is the
actual guarded readout. Thus initial private inputs and public outcomes remain
jointly distributed, rather than only their separate marginals.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
/-- The full physical service, with arbitrary disclosure timing, has the
original initialized typed source law. -/
theorem roster_plan_sourceReadout_law [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (profile : BehavioralProfile setup.program) :
    ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
        network (rosterPlan setup rosters)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).map
      (fun final => sourceReadout setup leaks (some ⟨0, none, final⟩)) =
      (setup.run profile).map some := by
  let := Fintype.ofFinite Player
  simp_rw [sourceReadout_eq_decode]
  rw [initialLaw, PMF.bind_map, PMF.map_bind, Setup.run, PMF.map_bind]
  apply bind_congr_on_support _
  intro initial supported
  exact run_roster_source_suffix_option_law setup leaks rosters timing network profile initial
    setup.program reveals profile (setup.initialConfig initial)
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program) (initialRefsBefore setup.program) 0
    (CompiledPolicySuffix.whole setup.program profile)
    (ReactiveApplication.Execution.initial (application setup leaks)
      (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)))
    (checkpoint_initial setup leaks reveals initial (openable initial supported)).toPublicCheckpoint
    (fun _ => rfl) MessageNetwork.Satisfies.empty MessageNetwork.SerialsBeforeNext.empty

/-- A complete finite-menu evaluation is the actual complete roster plan.
Coverage is required only at legal histories of that menu. -/
theorem roster_restrict_complete_state
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (menu : (application setup leaks).ResponseMenu)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who, menu.Admissible (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who (players who)) :
    ((menu.information (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).runBehavioral
      (fun who => menu.restrictPolicy (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) who (players who))
      (2 * (rosterPlan setup rosters).length + 1)).map History.state =
      ((initialLaw setup).bind fun state =>
        (runtime setup).runInteractionPlan leaks players network (rosterPlan setup rosters)
          (ReactiveApplication.Execution.initial (application setup leaks) state)).map
        (fun final => some ⟨0, none, final⟩) := by
  rw [InformationModel.runBehavioral, menu.run_restrict_eq_finish _ _ _ players covered
    _ _ (by rfl)]
  have plan := roster_roundsFrom setup leaks rosters network players
    (rosterPlan setup rosters).length (Nat.le_refl _)
  rw [List.take_length] at plan
  rw [← plan]
  simp only [ReactiveApplication.finish, ReactiveApplication.roundsFrom, PMF.map_bind]
  rfl

/-- Every finite fully mixed native approximant has exactly the original
finite source profile's initialized readout law. The fixed event timing laws
and actual passive observations remain in the native execution. -/
theorem rosterPerturbedProfile_readout_law
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (source : (setup.informationModel admission).BehavioralAssessment)
    (mixed : source.IsFullyMixed)
    (timing : TimingLaw setup rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned)) :
    (((rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).runBehavioral
      (rosterPerturbedProfile setup leaks bounds rosters network admission
        source timing) (2 * (rosterPlan setup rosters).length + 1)).map
        (fun final => sourceReadout setup leaks final.state) =
      ((setup.informationModel admission).runBehavioral source.strategy
        (instructionCount setup.program + 1)).map
          (fun final => setup.protocolReadout final.state) := by
  have represented := roster_restrict_complete_state setup leaks rosters network
    (rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters)
    (rosterPolicy setup leaks rosters timing
      (setup.decodeBehavioralProfile admission source.strategy))
    (rosterPolicy_admissible setup leaks bounds rosters network reveals openable admission
      source mixed timing timingFull)
  have observed := congrArg (fun law => law.map (sourceReadout setup leaks)) represented
  simp only [PMF.map_comp, Function.comp_def] at observed
  exact observed.trans ((roster_plan_sourceReadout_law setup leaks rosters timing network
    reveals openable (setup.decodeBehavioralProfile admission source.strategy)).trans
      (setup.runBehavioralFrom_readout admission source.strategy
        (instructionCount setup.program + 1) (setup.executionProtocol admission).initHistory
        (Nat.le_refl _)).symm)

end Vegas
