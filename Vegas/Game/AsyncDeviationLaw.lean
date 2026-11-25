module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphDeviation
public import Vegas.Compile.OpeningSafety
public import Vegas.Game.SourceServiceFacts
public import Vegas.Game.SourceServiceSiteBridge
public import Vegas.Pending.EffectiveOpeningSimulation

@[expose] public section

/-! # Source readout of physical unilateral deviations -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Against first-turn clients, every physical policy of one player has exactly
the terminal source-configuration law of one behavioral source deviation. -/
theorem sourceService_deviation_readout_law
    (setup : Setup (Player := Player) (L := L))
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    (horizon : Nat) (scheduler : (application setup timeouts leaks).Scheduler)
    (delay bound : setup.informationGraph.EventId → Nat) (turns : Nat)
    (contract : AsyncContract timeouts leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ player, (profile player).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (who : Player) (deviation : (application setup timeouts leaks).Policy) :
    ∃ policy : BehavioralPolicy who setup.program,
      ((application setup timeouts leaks).roundsFrom (initialLaw setup) scheduler
        (Function.update (serviceTurnPolicy setup setup.informationDependencies timeouts.duration
          leaks bound turns
          (firstTurnTiming setup turns) profile) who deviation) horizon).map
          (fun final => sourceReadout setup timeouts leaks
            ((application setup timeouts leaks).finished final)) =
        (setup.run (Function.update profile who policy)).map some := by
  let inputs : PMF setup.informationGraph.Inputs := setup.initialLaw.map setup.eventInputs
  let reference : setup.informationGraph.BehavioralProfile :=
    compileEventProfile setup.program profile
  have safe : SafeForeignPublications (g := setup.informationGraph) inputs reference who := by
    intro event owner _ payload binding checks outputEq codeEq node
      input present config reachable ready _ action chosen disclose
    obtain ⟨value, success⟩ :=
      compileEventProfile_supported_opening_succeeds effective input present config reachable
        event ready (outputEq := outputEq) codeEq action chosen disclose
    simp [openingAccepted, node, success]
  have initialized :
      initialLaw setup = inputs.map (EventGraphRuntime.State.initial
        (graph := setup.informationGraph)) :=
    serviceInitialLaw_eq_inputs setup (deps := setup.informationDependencies)
  have inputContract : AsyncContract timeouts leaks (inputs.map EventGraphRuntime.State.initial)
      horizon scheduler delay bound := by
    rw [← initialized]
    exact contract
  obtain ⟨replacement, _, raw⟩ := safePublication_deviation_config_law
    (graph := setup.dataflowGraph) (turns := turns) timeouts leaks scheduler delay bound
    inputs reference inputContract timely who deviation safe
  rw [← initialized] at raw
  let updated := Function.update reference who replacement
  have gameLaw := setup.informationGraph.gameForm_play_map_val
    inputs setup.informationGraph.canonicalScheduler updated
  have graph := sourceReadout_law_of_config_law setup timeouts leaks updated
    (raw.trans gameLaw.symm)
  refine ⟨backtranslateEventPolicy setup.program who replacement, graph.trans ?_⟩
  have compiled := congrArg (PMF.map some)
    (canonical_setup_deviation_law setup profile who replacement)
  simpa only [PMF.map_comp, Function.comp_def, GameTheory.Profile.update, updated, reference,
    inputs] using compiled

end Vegas
