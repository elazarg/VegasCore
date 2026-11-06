/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealServiceHonestLaw
import Vegas.Game.RevealServiceReference
import Vegas.Game.ConcurrentRevealNash

/-! # The source outcome law of honest clients with concurrent reveals

On the service graph with independent reveals concurrent, the first-turn
clients of the order-blind reference of a disclosing source profile have, under
every public scheduler and the asynchronous service contract, the source law of
the parameter, public values and public defaults. The reference's outcome law
from the initial configurations is that source law, because its canonical run
is the sequential compiled run read in instruction order.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The instruction-order outcome of a reachable terminal sequential run, viewed
on the concurrent-reveal graph, is the outcome of its source configuration. -/
theorem concurrentOutcome_fromSequential (setup : Setup (Player := Player) (L := L))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    {inputs : setup.eventGraph.Inputs} {config : setup.eventGraph.Config}
    (reach : EventGraph.Config.Reachable inputs config) (terminal : config.cut.Terminal) :
    concurrentOutcome setup parameter
        (setup.concurrentRevealGraph.fromSequentialConfig config) =
      some (setup.parameterOutcome parameter (terminalConfig setup.program
        ⟨config, terminal⟩)) := by
  have viewTerminal : (setup.concurrentRevealGraph.fromSequentialConfig config).cut.Terminal :=
    terminal
  have recast := setup.rankedConfig_fromSequentialConfig reach viewTerminal
  have decoded : concurrentRankedRead setup
      (setup.concurrentRevealGraph.fromSequentialConfig config) =
        some (terminalConfig setup.program ⟨config, terminal⟩) := by
    unfold concurrentRankedRead
    rw [ite_eq_left viewTerminal]
    have viaRanked : decodeConfig? setup.program setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) [] (outputEmbedding setup.program)
        (setup.concurrentRevealGraph.fromSequentialConfig config).store
        (Setup.rankedHistory (graph := setup.concurrentRevealGraph)
          (setup.concurrentRevealGraph.fromSequentialConfig config)) =
      decodeConfig? setup.program setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) [] (outputEmbedding setup.program)
        (setup.rankedConfig _ viewTerminal).store (setup.rankedConfig _ viewTerminal).history := by
      congr 1
      funext field
      cases field <;> rfl
    rw [viaRanked, recast]
    exact decodeConfig?_terminal setup.program ⟨config, terminal⟩
  unfold concurrentOutcome
  rw [decoded, Option.map_some]

/-- **The reference's initial outcome law is the source law.** -/
theorem concurrentReference_initial_outcomeLaw (setup : Setup (Player := Player) (L := L))
    (source : BehavioralProfile setup.program) {Parameter : Type}
    (parameter : State L setup.context → Parameter) :
    (serviceInitialLaw setup .concurrentReveals).bind (fun state =>
        outcomeLaw (concurrentReference setup source) (concurrentOutcome setup parameter)
          state.config) =
      (setup.run source).map (fun final => some (setup.parameterOutcome parameter final)) := by
  let compiled : setup.eventGraph.BehavioralProfile := compileEventProfile setup.program source
  have sourceLaw := canonical_setup_law setup source
  rw [← sourceLaw, PMF.map_comp]
  change _ = (setup.concurrentInputs.bind
    (setup.eventGraph.terminalOutcomes setup.eventGraph.canonicalScheduler compiled)).map _
  change _ = ((setup.initialLaw.map fun initial => setup.eventInputs initial).bind
    (setup.eventGraph.terminalOutcomes setup.eventGraph.canonicalScheduler compiled)).map _
  rw [serviceInitialLaw, PMF.bind_map, PMF.map_bind, PMF.bind_map]
  apply bind_congr_on_support _
  intro initial _
  let inputs := setup.eventInputs initial
  have law := setup.concurrentRevealGraph.canonical_fromSequential_config_law
    (setup.concurrentRevealGraph.normalizeProfile compiled) inputs
  have normalized := runPolicies_canonical_normalizeProfile setup.eventGraph_total compiled inputs
  change (setup.concurrentRevealGraph.runPolicies setup.concurrentRevealGraph.canonicalScheduler
    (setup.concurrentRevealGraph.normalizeProfile compiled) inputs).map _ = _
  rw [← law, PMF.map_comp]
  change (setup.eventGraph.runPolicies setup.eventGraph.canonicalScheduler
    (setup.eventGraph.normalizeProfile compiled) inputs).map _ = _
  rw [normalized, ← setup.eventGraph.terminalOutcomes_map_val, PMF.map_comp]
  change _ = PMF.map _ (setup.eventGraph.terminalOutcomes setup.eventGraph.canonicalScheduler
    compiled inputs)
  apply map_congr_on_support _
  intro outcome member
  have reach := setup.eventGraph.run_reachable inputs _ outcome.1
    ((setup.eventGraph.terminalOutcomes_map_val _ compiled inputs) ▸
      (PMF.mem_support_map_iff _ _ _).mpr ⟨outcome, member, rfl⟩)
  exact concurrentOutcome_fromSequential setup parameter reach outcome.2


/-- **Honest clients have the source outcome law under every public scheduler.**
Under the asynchronous service contract, on the service graph with independent
reveals concurrent, the first-turn clients of the order-blind reference of a
disclosing source profile have, read in instruction order, the source law of
the parameter, public values and public defaults. -/
theorem concurrentClients_outcome_law (setup : Setup (Player := Player) (L := L))
    (deadline : (serviceGraph setup .concurrentReveals).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket (serviceGraph setup .concurrentReveals)))
    {horizon turns : Nat}
    {scheduler : (serviceApplication setup .concurrentReveals deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup .concurrentReveals).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup .concurrentReveals deadline) leaks
      (serviceInitialLaw setup .concurrentReveals) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup .concurrentReveals deadline) delay bound)
    (source : BehavioralProfile setup.program)
    (disclosing : ∀ who, Disclosing setup.program (source who))
    {Parameter : Type} (parameter : State L setup.context → Parameter) :
    ((serviceApplication setup .concurrentReveals deadline leaks).roundsFrom
        (serviceInitialLaw setup .concurrentReveals) scheduler
        (serviceReferenceTurnPolicy setup .concurrentReveals deadline leaks bound turns
          (firstTurnTiming setup turns .concurrentReveals) (concurrentReference setup source))
        horizon).map (fun final =>
          (serviceRankedReadout setup .concurrentReveals deadline leaks
            ((serviceApplication setup .concurrentReveals deadline leaks).finished final)).map
            (setup.parameterOutcome parameter)) =
      (setup.run source).map (fun final => some (setup.parameterOutcome parameter final)) := by
  have keyed (left right : (serviceGraph setup .concurrentReveals).Config)
      (same : runKey left = runKey right) :
      concurrentOutcome setup parameter left = concurrentOutcome setup parameter right := by
    unfold concurrentOutcome
    rw [concurrentRankedRead_congr setup same]
  have law := honest_roundsFrom_outcomeLaw (deadline := deadline) (leaks := leaks)
    (turns := turns) contract timely
    (setup.eventGraph.withMode_concurrentReveals_revealsOnlyConcurrent setup.eventGraph_total)
    (fun _ notPublication => setup.eventGraph.withMode_concurrentReveals_leading
      setup.eventGraph_total notPublication)
    (concurrentReference setup source)
      (concurrentReference_readyIndependent setup source disclosing)
    (concurrentReference_opensPublications setup source disclosing)
    (concurrentOutcome setup parameter) keyed (concurrentOutcome_erase setup parameter)
  exact law.trans (concurrentReference_initial_outcomeLaw setup source parameter)

end Vegas
