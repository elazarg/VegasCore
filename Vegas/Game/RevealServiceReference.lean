/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealServiceRankedReadout
import Vegas.Pending.CanonicalKeyPublication
import Vegas.EventGraph.RevealRelaxedScheduling

/-! # The order-blind reference profile of concurrent reveals

Clients on the service graph with independent reveals concurrent compile a
source profile and then read their observation in instruction order. Their graph
profile is ready independent when the source profile discloses at every reveal,
because each compiled opening is the same opening action at every observation.
The instruction-order reader depends only on the order-free final key, so its
law is read from the canonical key law of that profile.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The compiled source profile on the concurrent-reveal service graph, reading
each observation in instruction order. -/
def concurrentReference (setup : Setup (Player := Player) (L := L))
    (source : BehavioralProfile setup.program) :
    (serviceGraph setup .concurrentReveals).BehavioralProfile :=
  (serviceGraph setup .concurrentReveals).normalizeProfile
    (compileEventProfile setup.program source)

/-- **Ready independence of the order-blind reference.** A disclosing source
profile compiles to a reference whose simultaneously ready events commute. -/
theorem concurrentReference_readyIndependent (setup : Setup (Player := Player) (L := L))
    (source : BehavioralProfile setup.program)
    (disclosing : ∀ who, Disclosing setup.program (source who)) :
    ReadyIndependent (concurrentReference setup source) := by
  have opens (who : Player) (event : (serviceGraph setup .concurrentReveals).EventId)
      (actor : (serviceGraph setup .concurrentReveals).actor? event = some who)
      (publication : ((serviceGraph setup .concurrentReveals).outputLayout event).IsPublication)
      (observation : (serviceGraph setup .concurrentReveals).PlayerObservation who)
      (active : who ∉ observation.defaulted) :
      compileEventProfile setup.program source who event actor observation active =
        PMF.pure (EventField.openAction _ publication) :=
    compileEventPolicy_publication setup.program who (source who) (disclosing who) event actor
      publication observation active
  exact (setup.eventGraph.withMode_concurrentReveals_revealsOnlyConcurrent
    setup.eventGraph_total).readyIndependent_normalizeProfile _
    fun who event actor publication left right leftActive rightActive => by
      rw [opens who event actor publication left leftActive,
        opens who event actor publication right rightActive]

/-- The order-blind reference of a disclosing source profile opens every
publication of an active owner. -/
theorem concurrentReference_opensPublications (setup : Setup (Player := Player) (L := L))
    (source : BehavioralProfile setup.program)
    (disclosing : ∀ who, Disclosing setup.program (source who)) :
    OpensPublications (concurrentReference setup source) :=
  fun config event who actor publication active =>
    compileEventPolicy_publication setup.program who (source who) (disclosing who) event actor
      publication _ (fun normalized => active
        ((serviceGraph setup .concurrentReveals).normalizeObservation_defaulted_subset who
          ((serviceGraph setup .concurrentReveals).playerObserve who config)
          normalized))

/-- The complete source configuration read from a concurrent-reveal
configuration in instruction order; unfinished configurations have none. -/
def concurrentRankedRead (setup : Setup (Player := Player) (L := L))
    (config : (serviceGraph setup .concurrentReveals).Config) :
    Option (Config Player L setup.program.terminalCtx) :=
  if config.cut.Terminal then
    Vegas.decodeConfig? setup.program setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) [] (outputEmbedding setup.program) config.store
      (Setup.rankedHistory (graph := serviceGraph setup .concurrentReveals) config)
  else none

/-- The instruction-order reader depends only on the order-free key. -/
theorem concurrentRankedRead_congr (setup : Setup (Player := Player) (L := L))
    {left right : (serviceGraph setup .concurrentReveals).Config}
    (same : runKey left = runKey right) :
    concurrentRankedRead setup left = concurrentRankedRead setup right := by
  have cut : left.cut = right.cut := congrArg Prod.fst same
  have store : left.store = right.store := congrArg (fun key => key.2.1) same
  have records : completionOf left = completionOf right := congrArg (fun key => key.2.2) same
  have history : Setup.rankedHistory left = Setup.rankedHistory right := by
    unfold Setup.rankedHistory
    rw [records]
  unfold concurrentRankedRead
  rw [cut, store, history]

/-- The service's instruction-order readout is the configuration reader at the
native terminal configuration. -/
theorem serviceRankedReadout_some (setup : Setup (Player := Player) (L := L))
    (deadline : (serviceGraph setup .concurrentReveals).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket (serviceGraph setup .concurrentReveals)))
    (control : (serviceApplication setup .concurrentReveals deadline leaks).Control) :
    serviceRankedReadout setup .concurrentReveals deadline leaks (some control) =
      concurrentRankedRead setup control.execution.application.config := rfl

end Vegas
