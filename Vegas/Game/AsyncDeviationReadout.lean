module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.AsyncDeviationLaw
public import Vegas.Source.DisclosureBehavioral

@[expose] public section

/-! # Typed outcome of physical unilateral deviations

The asynchronous contract and timely deadlines preserve each source successor
jointly with the deviating player's actual traffic. Guarded source disclosure
normalization retains the complete typed-state and default law against an
unchanged deviation, giving the original source game's outcome.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every raw physical unilateral deviation against compiled first-turn clients
has the typed-state and public-default law of a behavioral source deviation. -/
theorem asyncDeviation_readout_law
    (setup : Setup (Player := Player) (L := L))
    {duration : setup.informationGraph.EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon : Nat} {scheduler : (application setup ⟨duration⟩ leaks).Scheduler}
    {delay bound : setup.informationGraph.EventId → Nat}
    (contract : AsyncContract ⟨duration⟩ leaks (initialLaw setup) horizon scheduler delay bound)
    (timely : AsyncTimely ⟨duration⟩ delay bound) (turns : Nat)
    (original : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup ⟨duration⟩ leaks).Policy) :
    ∃ policy : BehavioralPolicy who setup.program,
      ((application setup ⟨duration⟩ leaks).roundsFrom
        (initialLaw setup) scheduler
        (Function.update (serviceTurnPolicy setup setup.informationDependencies duration leaks
          bound turns
          (firstTurnTiming setup turns) (normalizeDisclosureProfile setup.program original))
          who deviation) horizon).map (fun execution =>
            (sourceReadout setup ⟨duration⟩ leaks
              ((application setup ⟨duration⟩ leaks).finished execution)).map
                (fun final => (final.state, final.defaults))) =
        (setup.run (Function.update original who policy)).map
          (fun final => some (final.state, final.defaults)) := by
  obtain ⟨policy, physical⟩ := sourceService_deviation_readout_law setup ⟨duration⟩ leaks
    horizon scheduler delay bound turns contract timely
    (normalizeDisclosureProfile setup.program original)
    (fun player => BehavioralPolicy.normalizeDisclosures_effective setup.program (original player))
    who deviation
  refine ⟨policy, ?_⟩
  have projected := congrArg (PMF.map (Option.map (fun final => (final.state, final.defaults))))
    physical
  have normalized := congrArg (PMF.map some)
    (setup.run_update_normalizeDisclosures_eq original who policy)
  simp only [PMF.map_comp, Function.comp_def, Option.map_some] at projected normalized
  exact projected.trans normalized

end Vegas
