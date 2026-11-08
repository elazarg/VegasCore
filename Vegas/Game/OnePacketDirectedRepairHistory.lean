/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDirectedRepairEnvironment
import Vegas.Game.OnePacketDirectedRepairEnvironmentTrace
import Vegas.Game.OnePacketDirectedRepairOwnerResponse
import Vegas.Game.OnePacketDirectedRepairDelivery
import Vegas.Game.OnePacketFilteredPrefix

/-! # Concrete repaired whole histories at forced information -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- An actual image history of a single owner's private binding repair. The
clock and actor are unchanged, with complete operational records and original
submission meanings retained jointly. -/
structure BindingRepairHistory (owner : Player)
    {state : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).State}
    (sourceTrace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace state)
    (control : (application setup timeouts leaks).Control) where
  sourceState : state = some control
  memory : BindingMemory timeouts leaks
  execution : (application setup timeouts leaks).Execution
  trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
    (some ⟨control.remaining, control.actor, execution⟩)
  frame : DirectedBindingFrame (timeouts := timeouts) memory owner control.execution execution
  recorded : memory.RecordsSubmittedBindings timeouts leaks owner control.execution execution
  onlyBindings : memory.shadow.OwnBindings owner
  records : operationalRecord setup timeouts leaks bounds horizon scheduler sourceTrace =
    operationalRecord setup timeouts leaks bounds horizon scheduler trace

/-- Repair an owner's binding submissions throughout an actual clear
forced-information history. The guards are facts solely about original prefixes:
ready disclosure reads are successful and completed bindings have accepted handles. Every image
transition and its one-packet legality are constructed by the induction. -/
theorem repair_binding_history
    (covered : bounds.CoversOutputValues) (focal owner : Player) (other : owner ≠ focal)
    {info : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InfoState focal}
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw
      setup) horizon
      scheduler focal info)
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (decision : info = some (past, view))
    (history : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory focal
      info)
    (final : (application setup timeouts leaks).Control) (current : history.1.state = some final)
    (endpointClear : final.execution.application.config.defaulted = ∅)
    (successful : ∀ (before : (application setup timeouts leaks).Control)
      (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some
        before)),
      TracePrefix prior history.1.trace →
      ∀ (event : (graph setup).EventId) (actor : Player) (payload : L.Ty)
        (binding : EventGraph.FieldRef (graph setup).layout (.binding actor payload))
        (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
        (outputEq : (graph setup).outputLayout event = .publication payload)
        (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes event) = .resolve actor payload binding checks),
        nodeView (graph setup) event = .resolve actor payload binding checks outputEq codeEq →
        before.execution.application.config.cut.Ready event →
        ∃ value, binding.get? before.execution.application.config.store = some (.success value))
    (accepted : ∀ (before : (application setup timeouts leaks).Control)
      (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some
        before)),
      TracePrefix prior history.1.trace → ∀ event actor payload,
      (graph setup).outputLayout event = .binding actor payload →
      event ∈ before.execution.application.config.cut.completed →
      before.execution.application.accepted (.inr event) ≠ none) :
    Nonempty (BindingRepairHistory (timeouts := timeouts) owner history.1.trace final) := by
  classical
  have prefixClear : ∀ {state}
      (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace state),
      TracePrefix prior history.1.trace →
      ReactiveApplication.stateInvariant (app := application setup timeouts leaks)
        (fun native => native.config.defaulted = ∅) state := by
    intro state prior isPrefix
    apply clearRecord_of_tracePrefix (timeouts := timeouts) isPrefix
    rw [current]
    exact endpointClear
  have construct : ∀ {state : (onePacketProtocol setup timeouts leaks bounds horizon
    scheduler).State}
      (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace state),
      TracePrefix prior history.1.trace → ∀ control : (application setup timeouts leaks).Control,
      state = some control → Nonempty (BindingRepairHistory (timeouts := timeouts) owner prior
        control) := by
    intro state prior
    induction prior with
    | start =>
        intro _ control impossible
        cases impossible
    | @extend source target prior joint legal realized ih =>
        intro isPrefix control stateEq
        subst stateEq
        have priorPrefix : TracePrefix prior history.1.trace :=
          (TracePrefix.extend (.refl) joint legal realized).trans isPrefix
        let afterTrace := prior.extend joint legal realized
        have afterPrefix : TracePrefix afterTrace history.1.trace := isPrefix
        cases source with
        | none =>
            change some control ∈ ((initialLaw setup).map fun state => some
              (⟨horizon, none,
                ReactiveApplication.Execution.initial (application setup timeouts leaks) state⟩ :
                  (application setup timeouts leaks).Control)).support at realized
            obtain ⟨state, _, same⟩ := PMF.support_map .. ▸ realized
            cases Option.some.inj same
            let execution := ReactiveApplication.Execution.initial (application setup timeouts
              leaks) state
            let memory := BindingMemory.atRecall timeouts leaks (execution.logs owner)
            refine ⟨{
              sourceState := rfl
              memory := memory
              execution := execution
              trace := afterTrace
              frame := DirectedBindingFrame.atRecall (timeouts := timeouts)
                owner execution
              recorded := ?_
              onlyBindings := ?_
              records := rfl }⟩
            · exact BindingMemory.recordsSubmittedBindings_initial timeouts leaks memory
                owner state state
            · exact BindingShadow.ownBindings_empty owner
        | some before =>
            obtain ⟨image⟩ := ih priorPrefix before rfl
            have beforeClear : before.execution.application.config.defaulted = ∅ :=
              prefixClear prior priorPrefix
            have rawTrace := (bounds.onePacketMenu timeouts leaks).toRawTrace
              (initialLaw setup) horizon scheduler prior
            have clean := (bounds.onePacketMenu_countClean timeouts leaks scheduler).history
              (initialLaw setup) horizon (fun state _ => (countClean_initial timeouts) leaks
                state) prior
            have signed := (signedCommitments_history timeouts) leaks (initialLaw setup)
              (fun state member => by
                obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
                exact ⟨setup.eventInputs initial, rfl⟩) horizon scheduler rawTrace
            have leftBinding := ((reactiveBindingInvariant timeouts) leaks).history
              (initialLaw setup) horizon scheduler
              (fun state member => by
                obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
                exact State.initial_bindingInvariant _) rawTrace
            have rightBinding := ((reactiveBindingInvariant timeouts) leaks).history
              (initialLaw setup) horizon scheduler
              (fun state member => by
                obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
                exact State.initial_bindingInvariant _)
              ((bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon
                scheduler image.trace)
            rcases before with ⟨remaining, actor, original⟩
            cases actor with
            | some actor =>
                have available := legal.2 actor
                cases chosen : joint actor with
                | none =>
                    rw [chosen] at available
                    exact False.elim (available rfl)
                | some response =>
                    rw [chosen] at available
                    change some control ∈ (PMF.pure (some
                      (⟨remaining, none, original.respond (application setup timeouts leaks) actor
                        ((joint actor).getD ⟨none⟩)⟩ : (application setup timeouts
                          leaks).Control))).support
                      at realized
                    rw [chosen, Option.getD_some, PMF.mem_support_pure_iff] at realized
                    cases Option.some.inj realized
                    obtain ⟨targetResponse, nextMemory, nextFrame, nextRecorded, nextOnly,
                        targetTrace, targetRecords⟩ := image.frame.response_trace image.recorded
                      image.onlyBindings remaining actor prior image.trace image.records response
                      available.2 covered other forced decision history current afterTrace
                      afterPrefix
                    refine ⟨{
                      sourceState := rfl
                      memory := nextMemory
                      execution := image.execution.respond (application setup timeouts leaks) actor
                        targetResponse
                      trace := targetTrace
                      frame := nextFrame
                      recorded := nextRecorded
                      onlyBindings := nextOnly
                      records := ?_ }⟩
                    exact targetRecords.symm
            | none =>
                cases remaining with
                | zero =>
                    exact False.elim (legal.1 ⟨rfl, rfl⟩)
                | succ remaining =>
                    change some control ∈ ((scheduler original.environmentRecall
                      (original.observeEnvironment (application setup timeouts leaks))).bind
                        _).support
                        at realized
                    obtain ⟨command, chosen, supported⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
                    obtain ⟨nextOriginal, left, same⟩ := PMF.support_map .. ▸ supported
                    cases Option.some.inj same
                    have nextClear : nextOriginal.application.config.defaulted = ∅ :=
                      prefixClear afterTrace afterPrefix
                    obtain ⟨nextRepaired, right, afterFrame⟩ := image.frame.environment_step
                      beforeClear image.onlyBindings image.recorded
                        clean signed leftBinding rightBinding
                      (successful _ prior priorPrefix) command nextOriginal left nextClear
                      (accepted _ afterTrace afterPrefix)
                    have delivered := afterFrame.deliveredValue_of_successful
                      (by
                      intro event payload binding checks outputEq codeEq turn node
                      exact successful _ afterTrace afterPrefix event owner payload binding checks
                        outputEq codeEq node
                        ((nextOriginal.application.publicView_eventReady event).mp
                          (nextOriginal.application.publicView.ownTurn?_spec owner event turn).1))
                    obtain ⟨_, targetTrace, targetRecords⟩ := image.frame.environment_trace
                      remaining prior image.trace image.records command chosen left right
                      afterFrame.toFrame
                      delivered
                    refine ⟨{
                      sourceState := rfl
                      memory := image.memory
                      execution := nextRepaired
                      trace := targetTrace
                      frame := afterFrame
                      recorded := image.recorded.environmentStep timeouts leaks command
                        nextOriginal nextRepaired left right
                      onlyBindings := image.onlyBindings
                      records := ?_ }⟩
                    exact targetRecords.symm
  exact construct history.1.trace .refl final current

end Vegas
