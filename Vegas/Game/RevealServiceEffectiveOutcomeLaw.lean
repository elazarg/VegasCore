module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.PublicationPolicy
public import Vegas.Game.RevealServiceEffectiveHonestLaw
public import Vegas.Game.RevealServiceOutcomeLaw

@[expose] public section

/-! # Effective-opening clients have the source law

On the service graph with independent reveals concurrent, the effective-opening
reference of a disclosing source profile opens a reveal exactly when the opening
would be accepted. It is ready independent, and it is a twin up to erasure of
the always-open reference, so its outcome law is the always-open reference's.
Its first-turn clients therefore have, read in instruction order, the source law
of the typed terminal state and public default history, under every public
scheduler and the asynchronous contract.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The effective-opening reference of a source profile on the concurrent-reveal
service graph: the compiled profile, opening a reveal exactly when the opening
would be accepted, read in instruction order. -/
def concurrentEffectiveReference (setup : Setup (Player := Player) (L := L))
    (source : BehavioralProfile setup.program) :
    setup.revealRelaxedGraph.BehavioralProfile :=
  setup.revealRelaxedGraph.normalizeProfile
    (effectiveOpening (compileEventProfile setup.program source))

/-- The effective-opening reference is ready independent. -/
theorem concurrentEffectiveReference_readyIndependent
    (setup : Setup (Player := Player) (L := L)) (source : BehavioralProfile setup.program) :
    ReadyIndependent (concurrentEffectiveReference setup source) :=
  (setup.informationGraph.relaxReveals_revealsOnlyConcurrent
    setup.informationGraph_total).readyIndependent_normalizeProfile_of_footprint _
    (effectiveOpening_footprint _)

/-- The effective-opening reference opens a reveal exactly when the opening
would be accepted. -/
theorem concurrentEffectiveReference_decides (setup : Setup (Player := Player) (L := L))
    (source : BehavioralProfile setup.program)
    (config : setup.revealRelaxedGraph.Config)
    (event : setup.revealRelaxedGraph.EventId) (owner : Player) (payload :
      L.Ty)
    (binding : FieldRef setup.revealRelaxedGraph.layout (.binding owner
      payload))
    (checks : List (GuardCheck setup.revealRelaxedGraph.layout payload))
    (outputEq : setup.revealRelaxedGraph.outputLayout event = .publication
      payload)
    (codeEq : cast (congrArg (EventCode setup.revealRelaxedGraph.layout)
      outputEq)
      (setup.revealRelaxedGraph.nodes event) =
        .resolve owner payload binding checks)
    (node : nodeView setup.revealRelaxedGraph event =
      .resolve owner payload binding checks outputEq codeEq)
    (actor : setup.revealRelaxedGraph.actor? event = some owner)
    (active : owner ∉ (setup.revealRelaxedGraph.playerObserve owner
      config).defaulted) :
    concurrentEffectiveReference setup source owner event actor
        (setup.revealRelaxedGraph.playerObserve owner config) active =
      PMF.pure (cast (congrArg EventField.Action outputEq.symm)
        (openingAccepted event config.store)) :=
  normalize_effectiveOpening_publication _ config node actor active

/-- The effective-opening reference of a disclosing source profile is a twin up
to erasure of the always-open reference. -/
theorem concurrentEffectiveReference_twins (setup : Setup (Player := Player) (L := L))
    (source : BehavioralProfile setup.program)
    (disclosing : ∀ who, Disclosing setup.program (source who)) :
    ErasureTwins (concurrentEffectiveReference setup source)
      (concurrentReference setup source) := by
  let G := setup.revealRelaxedGraph
  let base : G.BehavioralProfile := compileEventProfile setup.program source
  have commute : G.normalizeProfile (effectiveOpening base) =
      effectiveOpening (G.normalizeProfile base) := by
    funext who event actor observation active
    unfold normalizeProfile normalizePolicy effectiveOpening
    cases node : nodeView G event <;> rfl
  change ErasureTwins (G.normalizeProfile (effectiveOpening base)) (G.normalizeProfile base)
  rw [commute]
  apply erasureTwins_effectiveOpening_honest
  intro who event actor publication observation active
  have normalizedActive : who ∉ (G.normalizeObservation who observation).defaulted :=
    fun member => active (G.normalizeObservation_defaulted_subset who observation member)
  change base who event actor (G.normalizeObservation who observation) normalizedActive = _
  exact compileEventPolicy_publication setup.program who (source who) (disclosing who) event
    actor publication (G.normalizeObservation who observation) normalizedActive

/-- The effective-opening reference has the always-open reference's outcome law
for every readout that ignores the decisions of defaulted players. -/
theorem concurrentEffectiveReference_outcomeLaw (setup : Setup (Player := Player) (L := L))
    (source : BehavioralProfile setup.program)
    (disclosing : ∀ who, Disclosing setup.program (source who)) {Outcome : Type*}
    (read : setup.revealRelaxedGraph.Config → Outcome)
    (invariant : ∀ config, read config.erase = read config)
    (config : setup.revealRelaxedGraph.Config) :
    outcomeLaw (concurrentEffectiveReference setup source) read config =
      outcomeLaw (concurrentReference setup source) read config :=
  (concurrentEffectiveReference_twins setup source disclosing).runPlan_map_of_erase_invariant
    _ read invariant _ config

/-- **Effective-opening clients have the source state law under every public
scheduler.** Under the asynchronous service contract, on the service graph with
independent reveals concurrent, the first-turn clients of the effective-opening
reference of a disclosing source profile have, read in instruction order, the
source law of every observation of the typed terminal state and public default
history. -/
theorem concurrentEffectiveClients_state_law (setup : Setup (Player := Player) (L := L))
    (duration : setup.revealRelaxedGraph.EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player
      (WitnessedPacket setup.revealRelaxedGraph))
    {horizon turns : Nat}
    {scheduler : (serviceApplication setup setup.revealDependencies duration leaks).Scheduler}
    {delay bound : setup.revealRelaxedGraph.EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup setup.revealDependencies duration) leaks
      (serviceInitialLaw setup setup.revealDependencies) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup setup.revealDependencies duration) delay bound)
    (source : BehavioralProfile setup.program)
    (disclosing : ∀ who, Disclosing setup.program (source who))
    {Outcome : Type*} (read : State L setup.program.terminalCtx × DefaultHistory Player → Outcome) :
    ((serviceApplication setup setup.revealDependencies duration leaks).roundsFrom
        (serviceInitialLaw setup setup.revealDependencies) scheduler
        (turnPolicy (serviceTimeouts setup setup.revealDependencies duration) leaks bound turns
          (firstTurnTiming setup turns setup.revealDependencies)
          (concurrentEffectiveReference setup source))
        horizon).map (fun final =>
          (serviceRankedReadout setup setup.revealDependencies duration leaks
            ((serviceApplication setup setup.revealDependencies duration leaks).finished final)).map
            (fun config => read (config.state, config.defaults))) =
      (setup.run source).map (fun final => some (read (final.state, final.defaults))) := by
  have keyed (left right : setup.revealRelaxedGraph.Config)
      (same : runKey left = runKey right) :
      concurrentStateRead setup read left = concurrentStateRead setup read right := by
    unfold concurrentStateRead
    rw [concurrentRankedRead_congr setup same]
  have law := effective_roundsFrom_outcomeLaw (duration := duration) (leaks := leaks)
    (turns := turns) contract timely
    (setup.informationGraph.relaxReveals_revealsOnlyConcurrent setup.informationGraph_total)
    (fun _ notPublication => setup.informationGraph.relaxReveals_leading
      setup.informationGraph_total notPublication)
    (concurrentEffectiveReference setup source)
    (concurrentEffectiveReference_readyIndependent setup source)
    (concurrentEffectiveReference_decides setup source)
    (concurrentReference setup source)
    (concurrentReference_readyIndependent setup source disclosing)
    (concurrentReference_opensPublications setup source disclosing)
    (concurrentStateRead setup read) keyed (concurrentStateRead_erase setup read)
    (concurrentEffectiveReference_outcomeLaw setup source disclosing _
      (concurrentStateRead_erase setup read))
  exact law.trans (concurrentReference_initial_stateLaw setup source read)

end Vegas
