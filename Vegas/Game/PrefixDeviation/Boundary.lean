module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphObservationEncoding
public import Vegas.Game.SourceServiceCheckpoint
public import Vegas.Game.SourceServiceCompletion
public import Vegas.Pending.ReactiveBindingLikelihood
public import Vegas.Source.IntendedGame

@[expose] public section

/-! # Continuation comparisons at a source-prefix boundary -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def nativeSourceContinuation
    (setup : Setup (Player := Player) (L := L)) (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))
    (horizon : Nat) (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program)
    (reference : setup.informationGraph.BehavioralProfile) (focal : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy)
    (nativePayoff : (serviceApplication setup deps duration leaks).Execution → ℝ)
    (sourcePayoff : setup.informationGraph.Config → ℝ)
    {rank : Nat} {point : setup.informationGraph.Config}
    (frame : SourceResidual setup wholeProfile rank point) :=
  frame.refs.CoversPrefix setup.program rank →
  ∀ {Seed : Type} (prior : PMF Seed) (source : Seed → Config Player L frame.Γ)
    (ghost : Seed → setup.informationGraph.Config),
    (∀ seed ∈ prior.support, @(source seed).revelations = @frame.source.revelations) →
    (∀ seed ∈ prior.support, (source seed).registry = frame.source.registry) →
    (∀ seed ∈ prior.support, SourceCheckpoint setup (source seed) frame.refs rank (ghost seed)) →
    (∀ seed ∈ prior.support, ∃ inputs, (ghost seed).Reachable inputs) →
    (∀ seed ∈ prior.support, ∃ history : setup.intendedProtocol.History,
      history.state = some (frame.lift (ProtocolState.entry frame.program (source seed)))) →
    ∀ (members : Seed → (serviceGraph setup deps).BehavioralProfile),
    (∀ seed ∈ prior.support, (serviceGraph setup deps).SubmitsBindings (members seed)) →
    (∀ seed ∈ prior.support, ∀ owner node actor observation active, rank ≤ node.val →
      members seed owner node actor observation active =
        reference owner node actor observation active) →
    ∀ (execution : Seed → (serviceApplication setup deps duration leaks).Execution),
    let players := fun seed => Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening
          ((serviceGraph setup deps).prefixProfile (members seed)))) focal deviation
    (∀ seed ∈ prior.support,
      CompletionBoundary setup leaks scheduler (players seed) rank (execution seed)) →
    (∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon) →
    (∀ seed ∈ prior.support, runKey (execution seed).application.config =
      runKey ((serviceGraph setup deps).fromSequentialConfig (ghost seed))) →
    ∀ (noise : DecisionView focal frame.Γ → PMF _),
    (prior.map (fun seed => ((source seed, ghost seed),
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, ghost seed))).bind fun hidden =>
        (noise (hidden.1.view focal)).map (fun observed => (hidden, observed))) →
    ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      expect (prior.bind fun seed =>
        (serviceApplication setup deps duration leaks).runToHorizon scheduler (players seed)
          horizon (execution seed)) nativePayoff ≤
        expect (prior.bind fun seed => setup.informationGraph.runPlan
          (setup.informationGraph.policyPlan (Function.update
            (setup.informationGraph.prefixProfile reference) focal policy)
            setup.informationGraph.canonicalScheduler) (eventCount frame.program) (ghost seed))
          sourcePayoff

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def residualAt
    {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}
    {rank : Nat} {origin : setup.informationGraph.Config}
    (frame : SourceResidual setup profile rank origin)
    (source : Config Player L frame.Γ)
    (revelations : @source.revelations = @frame.source.revelations)
    (registry : source.registry = frame.source.registry)
    (ghost : setup.informationGraph.Config)
    (checkpoint : SourceCheckpoint setup source frame.refs rank ghost) :
    SourceResidual setup profile rank ghost where
  Γ := frame.Γ
  names := frame.names
  program := frame.program
  residualProfile := frame.residualProfile
  source := source
  refs := frame.refs
  embedding := frame.embedding
  refsBefore := frame.refsBefore
  aligned := by rw [revelations, registry]; exact frame.aligned
  admitted := frame.admitted
  authentic := frame.authentic
  supports := frame.supports
  disclosing := frame.disclosing
  lift := frame.lift
  commutes := frame.commutes
  steps := frame.steps
  injective := frame.injective
  transport := by
    intro more store history defaults
    rw [registry, revelations]
    exact frame.transport more store history defaults
  checkpoint := checkpoint

end Vegas
