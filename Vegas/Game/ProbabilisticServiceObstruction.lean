/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveOutage
import Interaction.ReactiveLocalContinuation
import Vegas.Game.RevealServicePayoffs

/-! # Exact source-state preservation under probabilistic physical service

Mixing an arbitrary public runtime controller with a genuine no-service round
removes its sure protected-delivery guarantee. For every nonempty compiled
program, its actual initialization law and every native behavioral profile,
the fixed-horizon typed source readout has positive missing-outcome mass.
This rules out exact source-law preservation before equilibrium incentives are
considered. Pending observations, private preparation, and raw response menus
are unchanged; no packet is hidden or deleted.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A nonempty compiled source program is unfinished at its ordinary
initialization, irrespective of its initial private inputs. -/
theorem serviceSourceReadout_initial_none
    (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
    (deadline : (serviceGraph setup mode).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (event : (serviceGraph setup mode).EventId) (inputs : (serviceGraph setup mode).Inputs) :
    serviceSourceReadout setup mode deadline leaks
      (some ⟨0, none, ReactiveApplication.Execution.initial
        (serviceApplication setup mode deadline leaks) (State.initial inputs)⟩) = none := by
  have unfinished : ¬ (State.initial inputs).config.cut.Terminal := by
    intro terminal
    have member : event ∈ (State.initial inputs).config.cut.completed := by
      rw [terminal]
      exact Finset.mem_univ event
    change event ∈ (∅ : Finset (serviceGraph setup mode).EventId) at member
    simp only [Finset.notMem_empty] at member
  simp only [serviceSourceReadout, Option.bind_some, ReactiveApplication.Execution.initial,
    unfinished, ite_false]

/-- Native physical execution from the actual compiled prior has error at
least the probability that every bounded service opportunity is an outage.
The normal public controller, all RAW policies, and the source terminal law
are arbitrary. The event witness merely says the source program is nonempty. -/
theorem service_outage_totalVariation_lower_bound
    (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
    (deadline : (serviceGraph setup mode).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (event : (serviceGraph setup mode).EventId)
    (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (normal : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy)
    (horizon : Nat) (source : PMF (State L setup.program.terminalCtx)) {error : ℝ}
    (close : PMF.WithinTV error
      (((serviceInitialLaw setup mode).bind fun state =>
        (serviceApplication setup mode deadline leaks).runRounds
          ((serviceApplication setup mode deadline leaks).waitOutageScheduler
            floor nonnegative bounded normal) players horizon
          (ReactiveApplication.Execution.initial _ state)).map fun final =>
            serviceSourceReadout setup mode deadline leaks
              ((serviceApplication setup mode deadline leaks).finished final))
      (source.map some)) :
    floor ^ horizon ≤ error := by
  let app := serviceApplication setup mode deadline leaks
  let observe := fun state : app.State => serviceSourceReadout setup mode deadline leaks
    (some ⟨0, none, ReactiveApplication.Execution.initial app state⟩)
  have never : (((source.map some).toOuterMeasure {none})).toReal = 0 := by
    rw [PMF.toOuterMeasure_map_apply]
    have empty : (fun state : State L setup.program.terminalCtx => some state) ⁻¹'
        ({none} : Set (Option (State L setup.program.terminalCtx))) = ∅ := by
      ext state
      simp
    rw [empty]
    simp
  have missing : ((serviceInitialLaw setup mode).toOuterMeasure
      (observe ⁻¹' {none})).toReal = 1 := by
    rw [(PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr ?_, ENNReal.toReal_one]
    intro state supported
    obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
    exact serviceSourceReadout_initial_none setup mode deadline leaks event _
  have lower := app.waitOutage_initial_totalVariation_lower_bound floor nonnegative bounded
    normal players (serviceInitialLaw setup mode) observe {none} (source.map some)
    never horizon (by exact close)
  change floor ^ horizon * ((serviceInitialLaw setup mode).toOuterMeasure
    (observe ⁻¹' ({none} : Set (Option (State L setup.program.terminalCtx))))).toReal ≤ error
      at lower
  rw [missing, mul_one] at lower
  exact lower

variable [Fintype Player]

/-- The obstruction holds directly for every native behavioral strategy in
every actual response menu, including bounded raw menus. It does not presume
that the strategy is a compiled client or already an equilibrium. -/
theorem service_behavioral_outage_totalVariation_lower_bound
    (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
    (deadline : (serviceGraph setup mode).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (event : (serviceGraph setup mode).EventId)
    (floor : ℝ) (nonnegative : 0 ≤ floor) (bounded : floor ≤ 1)
    (normal : (serviceApplication setup mode deadline leaks).Scheduler)
    (horizon : Nat) (menu : (serviceApplication setup mode deadline leaks).ResponseMenu)
    (profile : GameTheory.Profile (menu.information (serviceInitialLaw setup mode) horizon
      ((serviceApplication setup mode deadline leaks).waitOutageScheduler
        floor nonnegative bounded normal)).behavioralSignature)
    (source : PMF (State L setup.program.terminalCtx)) {error : ℝ}
    (close : PMF.WithinTV error
      (((menu.information (serviceInitialLaw setup mode) horizon
        ((serviceApplication setup mode deadline leaks).waitOutageScheduler
          floor nonnegative bounded normal)).runBehavioral profile (2 * horizon + 1)).map
        (fun final => serviceSourceReadout setup mode deadline leaks final.state))
      (source.map some)) :
    floor ^ horizon ≤ error := by
  let app := serviceApplication setup mode deadline leaks
  let scheduler := app.waitOutageScheduler floor nonnegative bounded normal
  let initial := serviceInitialLaw setup mode
  have represented := menu.run_map_controlSteps initial horizon scheduler profile
    (2 * horizon + 1) (menu.protocol initial horizon scheduler).initHistory
  change ((menu.information initial horizon scheduler).runBehavioral profile
    (2 * horizon + 1)).map ExecutionProtocol.History.state =
      (fun law => law.bind (app.controlStep initial horizon scheduler
        (menu.decodeProfile initial horizon scheduler profile)))^[2 * horizon + 1]
          (PMF.pure none) at represented
  rw [app.iterate_eq_finish initial horizon scheduler
    (menu.decodeProfile initial horizon scheduler profile) (2 * horizon + 1) none
    (by rfl)] at represented
  have readout := congrArg
    (fun law => law.map (serviceSourceReadout setup mode deadline leaks)) represented
  simp only [PMF.map_comp, Function.comp_def, ReactiveApplication.finish,
    PMF.map_bind] at readout
  rw [readout] at close
  apply service_outage_totalVariation_lower_bound setup mode deadline leaks event floor
    nonnegative bounded normal (menu.decodeProfile initial horizon scheduler profile)
    horizon source
  convert close using 1
  simp only [PMF.map_bind, app, scheduler, initial]
  rfl

/-- Exact source-law preservation is impossible for every native strategy,
and therefore for every Nash, perfect Bayesian, or sequential equilibrium,
under this finite-horizon probabilistic service. -/
theorem service_behavioral_outage_not_realized
    (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
    (deadline : (serviceGraph setup mode).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (event : (serviceGraph setup mode).EventId)
    (floor : ℝ) (positive : 0 < floor) (bounded : floor ≤ 1)
    (normal : (serviceApplication setup mode deadline leaks).Scheduler)
    (horizon : Nat) (menu : (serviceApplication setup mode deadline leaks).ResponseMenu)
    (profile : GameTheory.Profile (menu.information (serviceInitialLaw setup mode) horizon
      ((serviceApplication setup mode deadline leaks).waitOutageScheduler
        floor positive.le bounded normal)).behavioralSignature)
    (source : PMF (State L setup.program.terminalCtx)) :
    ((menu.information (serviceInitialLaw setup mode) horizon
      ((serviceApplication setup mode deadline leaks).waitOutageScheduler
        floor positive.le bounded normal)).runBehavioral profile (2 * horizon + 1)).map
      (fun final => serviceSourceReadout setup mode deadline leaks final.state) ≠
        source.map some := by
  intro same
  have close : PMF.WithinTV 0
      (((menu.information (serviceInitialLaw setup mode) horizon
        ((serviceApplication setup mode deadline leaks).waitOutageScheduler
          floor positive.le bounded normal)).runBehavioral profile (2 * horizon + 1)).map
        (fun final => serviceSourceReadout setup mode deadline leaks final.state))
      (source.map some) := by
    rw [same]
    exact PMF.WithinTV.refl _
  exact (not_le_of_gt (pow_pos positive horizon))
    (service_behavioral_outage_totalVariation_lower_bound setup mode deadline leaks event
      floor positive.le bounded normal horizon menu profile source close)

end Vegas
