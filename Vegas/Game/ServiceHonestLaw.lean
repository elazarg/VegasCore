/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceFirstTurnCompletion
import Mathlib.Tactic.Convert

/-! # Sequential source law of the first-turn compiler

The public-barrier premise identifies a compiled service graph with the
compiler's sequential graph. Native client and source-reader constructors
respect that equality, preserving the direct asynchronous source law on this
same sequential compiler output. The shared mode parameter adds no concurrent
compiler result; lower graph APIs retain their separate nonordered scope.
-/

noncomputable section
namespace Vegas
open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem mode_predecessors_eq (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) (ordered : (serviceGraph setup mode).BarrierOrdered) :
    (serviceGraph setup mode).order.predecessors = (graph setup).order.predecessors := by
  have graphEq := serviceGraph_eq_sequential setup mode ordered
  have same : HEq (serviceGraph setup mode).order.predecessors
      (graph setup).order.predecessors := by
    rw [graphEq]
  exact eq_of_heq same

/-- First-turn clients preserve the source's full terminal configuration under
the asynchronous service contract in every public-barrier dependency mode. -/
theorem firstTurn_readout_law [Finite Player]
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (profile : BehavioralProfile setup.program)
    (authentic : ∀ who, (profile who).AuthenticDisclosures setup.program) :
    FirstTurnSourceLaw setup mode deadline leaks horizon scheduler bound turns profile := by
  let statement := fun mode : EventGraph.ExecutionMode =>
    ∀ (deadline : (serviceGraph setup mode).EventId → Nat)
      (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
      (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
      (delay bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
      (profile : BehavioralProfile setup.program),
      AsyncContract (serviceRuntime setup mode deadline) leaks (serviceInitialLaw setup mode)
        horizon scheduler delay bound →
      AsyncTimely (serviceRuntime setup mode deadline) delay bound →
      (∀ who, (profile who).AuthenticDisclosures setup.program) →
      FirstTurnSourceLaw setup mode deadline leaks horizon scheduler bound turns profile
  let evaluate := fun
      (predecessors : Fin setup.eventGraph.order.eventCount →
        Finset (Fin setup.eventGraph.order.eventCount)) =>
    ∀ (lower : ∀ {event prior : Fin setup.eventGraph.order.eventCount},
          prior ∈ predecessors event → prior.val < event.val)
      (reads : ∀ event field, field ∈ (setup.eventGraph.nodes event).readFields →
        match field with
        | .inl _ => True
        | .inr producer => producer ∈ predecessors event),
      let compiled : EventGraph Player L := {
        inputCount := setup.eventGraph.inputCount
        order := { eventCount := setup.eventGraph.order.eventCount
                   predecessors := predecessors
                   predecessor_lt := lower }
        inputLayout := setup.eventGraph.inputLayout
        outputLayout := setup.eventGraph.outputLayout
        nodes := setup.eventGraph.nodes
        reads_available := by
          intro event field member
          cases field with
          | inl _ => trivial
          | inr producer => exact reads event (.inr producer) member
        payoffs := setup.eventGraph.payoffs }
      ∀ (deadline : compiled.EventId → Nat)
        (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket compiled))
        (horizon : Nat),
        let runtime : EventGraphRuntime compiled := ⟨deadline⟩
        let app := runtime.reactiveApplication leaks
        ∀ (scheduler : app.Scheduler) (delay bound : compiled.EventId → Nat)
          (turns : Nat) (profile : BehavioralProfile setup.program),
          let initial : PMF (EventGraphRuntime.State compiled) :=
            setup.initialLaw.map fun initial => EventGraphRuntime.State.initial
              (setup.eventInputs initial)
          let canonical : Player → app.Policy := fun who past view =>
            if identity : view.application.who = who then
              match view.application.publicView.ownTurn? who with
              | none => PMF.pure ⟨none⟩
              | some event =>
                  if owned : compiled.actor? event = some who then
                    let observed := id (identity ▸ view.application.observation)
                    if inactive : who ∈ observed.defaulted then PMF.pure ⟨none⟩ else
                      ((compileEventProfile setup.program profile) who event owned observed
                        inactive).map
                          (runtime.canonicalServiceDecision leaks who past view event)
                  else PMF.pure ⟨none⟩
            else PMF.pure ⟨none⟩
          let opportunity : Player → compiled.EventId → app.Policy :=
            fun who event past view =>
              if runtime.eventRecorded leaks past event then app.silentPolicy past view else
              if view.application.publicView.InclusionFitsDeadline runtime bound event then
                (canonical who past view).bind fun response =>
                  if response.transmission = none then app.silentPolicy past view
                  else PMF.pure response
              else app.silentPolicy past view
          let players : Player → app.Policy := fun who past view =>
            match view.application.publicView.ownTurn? who with
            | none => app.silentPolicy past view
            | some event =>
                if owned : compiled.actor? event = some who then
                  ((app.policyMixture (PMF.pure (0 : Fin (turns + 1)))) fun slot =>
                    app.turnScheduledPolicy
                      (fun past view =>
                        if view.application.publicView.ownTurn? who = some event then
                          some (past.countP fun entry => decide
                            (entry.beforeView.application.publicView.ownTurn? who = some event))
                        else none)
                      (some slot) (opportunity who event) app.silentPolicy).policy past view
                else app.silentPolicy past view
          let read : app.ProtocolState → Option (Config Player L setup.program.terminalCtx) :=
            fun state => state.bind fun control =>
              let config := control.execution.application.config
              if config.cut.Terminal then
                decodeConfig? setup.program setup.program
                  (ContextRefs.initial setup.context (outputLayout setup.program))
                  (Revelations.initial setup.context) [] (outputEmbedding setup.program)
                    config.store config.history
              else none
          AsyncContract runtime leaks initial horizon scheduler delay bound →
          AsyncTimely runtime delay bound →
          (∀ who, (profile who).AuthenticDisclosures setup.program) →
          (app.roundsFrom initial scheduler players horizon).map
            (fun execution => read (app.finished execution)) = (setup.run profile).map some
  have representation (selectedMode : EventGraph.ExecutionMode) :
      statement selectedMode ↔
        evaluate (serviceGraph setup selectedMode).order.predecessors := by
    have sourceReads : ∀ event field, field ∈ (setup.eventGraph.nodes event).readFields →
        match field with
        | .inl _ => True
        | .inr producer =>
            producer ∈ (serviceGraph setup selectedMode).order.predecessors event := by
      intro event field member
      cases field with
      | inl _ => trivial
      | inr producer =>
          exact (serviceGraph setup selectedMode).reads_available event (.inr producer)
            (by simpa only [serviceGraph, EventGraph.withMode_nodes] using member)
    dsimp only [statement, evaluate]
    delta FirstTurnSourceLaw serviceTurnPolicy serviceReferenceTurnPolicy firstTurnTiming
    delta serviceTurnFamily serviceReferenceTurnFamily serviceTurn
    delta serviceCanonicalOpportunity serviceReferenceOpportunity serviceCanonicalPolicy
    delta serviceReferencePolicy serviceSourceReadout
    delta serviceApplication serviceRuntime serviceInitialLaw
    delta serviceGraph graph EventGraph.sequentialize EventGraph.withMode
    dsimp (config := { instances := true }) only
    constructor
    · intro law lower reads
      convert law using 1
      congr!
      all_goals
        funext motive value onNone onSome
        cases value <;> rfl
    · intro law
      have specialized := law (serviceGraph setup selectedMode).order.predecessor_lt sourceReads
      convert specialized using 1
      congr!
      all_goals
        funext motive value onNone onSome
        cases value <;> rfl
  have statementEq : statement mode = statement .sequential := by
    calc
      statement mode = evaluate (serviceGraph setup mode).order.predecessors :=
        propext (representation mode)
      _ = evaluate (serviceGraph setup .sequential).order.predecessors :=
        congrArg evaluate (mode_predecessors_eq setup mode ordered)
      _ = statement .sequential := (propext (representation .sequential)).symm
  have sequential : statement .sequential := by
    intro deadline leaks horizon scheduler delay bound turns profile contract timely authentic
    exact firstTurnSourceLaw_of_async (serviceRuntime setup .sequential deadline) leaks scheduler
      delay bound profile contract timely authentic
  have general : statement mode := statementEq.symm ▸ sequential
  exact general deadline leaks horizon scheduler delay bound turns profile contract timely authentic

end Vegas
