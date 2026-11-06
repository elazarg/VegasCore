/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.AsyncDeviationLaw
import Vegas.Source.DisclosureBehavioral
import Mathlib.Tactic.Convert

/-! # Typed outcome of arbitrary physical unilateral deviations

The asynchronous contract and timely deadlines preserve each source successor
jointly with the deviating player's actual traffic. The public-barrier
certificate transports this law to the certified dependency modes. Guarded
source disclosure normalization preserves the complete typed-state/default law
against an unchanged deviation, yielding the original source game's outcome.
-/


noncomputable section
namespace Vegas
open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem native_deviation_mode_transport
    (setup : Setup (Player := Player) (L := L))
    (sequential : ∀ (deadline : (graph setup).EventId → Nat)
      (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
      (horizon : Nat) (scheduler : (application setup ⟨deadline⟩ leaks).Scheduler)
      (delay bound : (graph setup).EventId → Nat) (turns : Nat)
      (profile : BehavioralProfile setup.program),
      AsyncContract (⟨deadline⟩ : EventGraphRuntime (graph setup)) leaks
        (initialLaw setup) horizon scheduler delay bound →
      AsyncTimely (⟨deadline⟩ : EventGraphRuntime (graph setup)) delay bound →
      (∀ who, (profile who).EffectiveDisclosures setup.program []
        (Revelations.initial setup.context)) →
      ∀ (who : Player) (deviation : (application setup ⟨deadline⟩ leaks).Policy),
      ∃ policy : BehavioralPolicy who setup.program,
        ((application setup ⟨deadline⟩ leaks).roundsFrom (initialLaw setup) scheduler
          (Function.update (serviceTurnPolicy setup .sequential deadline leaks bound turns
            (firstTurnTiming setup turns) profile) who deviation) horizon).map
          (fun final => sourceReadout setup ⟨deadline⟩ leaks
            ((application setup ⟨deadline⟩ leaks).finished final)) =
          (setup.run (Function.update profile who policy)).map some)
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy) :
    ∃ policy : BehavioralPolicy who setup.program,
      ((serviceApplication setup mode deadline leaks).roundsFrom
        (serviceInitialLaw setup mode) scheduler
        (Function.update (serviceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) profile) who deviation) horizon).map
          (fun final => serviceSourceReadout setup mode deadline leaks
            ((serviceApplication setup mode deadline leaks).finished final)) =
        (setup.run (Function.update profile who policy)).map some := by
  let statement := fun mode : EventGraph.ExecutionMode =>
    ∀ (deadline : (serviceGraph setup mode).EventId → Nat)
      (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
      (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
      (delay bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
      (profile : BehavioralProfile setup.program),
      AsyncContract (serviceRuntime setup mode deadline) leaks (serviceInitialLaw setup mode)
        horizon scheduler delay bound →
      AsyncTimely (serviceRuntime setup mode deadline) delay bound →
      (∀ who, (profile who).EffectiveDisclosures setup.program []
        (Revelations.initial setup.context)) →
      ∀ (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy),
      ∃ policy : BehavioralPolicy who setup.program,
        ((serviceApplication setup mode deadline leaks).roundsFrom
          (serviceInitialLaw setup mode) scheduler
          (Function.update (serviceTurnPolicy setup mode deadline leaks bound turns
            (firstTurnTiming setup turns mode) profile) who deviation) horizon).map
            (fun final => serviceSourceReadout setup mode deadline leaks
              ((serviceApplication setup mode deadline leaks).finished final)) =
          (setup.run (Function.update profile who policy)).map some
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
          (∀ who, (profile who).EffectiveDisclosures setup.program []
            (Revelations.initial setup.context)) →
          ∀ (who : Player) (deviation : app.Policy),
          ∃ policy : BehavioralPolicy who setup.program,
            (app.roundsFrom initial scheduler (Function.update players who deviation)
              horizon).map (fun execution => read (app.finished execution)) =
              (setup.run (Function.update profile who policy)).map some
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
    delta serviceTurnPolicy serviceReferenceTurnPolicy firstTurnTiming
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
        congrArg evaluate (by
          have graphEq := serviceGraph_eq_sequential setup mode ordered
          have same : HEq (serviceGraph setup mode).order.predecessors
              (graph setup).order.predecessors := by rw [graphEq]
          exact eq_of_heq same)
      _ = statement .sequential := (propext (representation .sequential)).symm
  have general : statement mode := statementEq.symm ▸ sequential
  exact general deadline leaks horizon scheduler delay bound turns profile contract timely
    effective who deviation

end Vegas

namespace Vegas
open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every raw physical unilateral deviation against compiled first-turn clients
has the typed-state/public-default law of a behavioral source deviation. -/
theorem asyncDeviation_readout_law
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (original : BehavioralProfile setup.program)
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy) :
    ∃ policy : BehavioralPolicy who setup.program,
      ((serviceApplication setup mode deadline leaks).roundsFrom
        (serviceInitialLaw setup mode) scheduler
        (Function.update (serviceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) (normalizeDisclosureProfile setup.program original))
          who deviation) horizon).map (fun execution =>
            (serviceSourceReadout setup mode deadline leaks
              ((serviceApplication setup mode deadline leaks).finished execution)).map
                (fun final => (final.state, final.defaults))) =
        (setup.run (Function.update original who policy)).map
          (fun final => some (final.state, final.defaults)) := by
  obtain ⟨policy, physical⟩ := native_deviation_mode_transport setup
    (fun deadline leaks horizon scheduler delay bound turns profile contract timely effective who
        deviation => sourceService_deviation_readout_law setup ⟨deadline⟩ leaks horizon scheduler
          delay bound turns contract timely profile effective who deviation) leaks ordered
    contract timely turns (normalizeDisclosureProfile setup.program original)
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
