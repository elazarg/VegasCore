module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketChanceStoppedLaw
public import Vegas.Game.SourceServiceFirstTurnMixture

@[expose] public section

/-! # Exact source kernels of native chance completions -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A reached chance completion has exactly the source one-step law on decoded prefixes. -/
theorem SourceResidual.chance_step_sourceLaw
    {profile : BehavioralProfile setup.program} {rank : Nat} {config : (graph setup).Config}
    (residual : SourceResidual setup profile rank config) (event : (graph setup).EventId)
    (atRank : event.val = rank) (ready : config.cut.Ready event)
    (actorless : (graph setup).actor? event = none)
    (action : (graph setup).Action event) {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank config = some point) :
    (config.step event ready action).map (sourceServicePrefix? setup (rank + 1)) =
      (ProtocolState.behavioralStateStep setup.program profile point).map some := by
  let native : EventGraphRuntime.State (graph setup) :=
    { EventGraphRuntime.State.initial (graph := graph setup) config.inputs with config := config }
  have pointEq := Option.some.inj (residual.decode.symm.trans decoded)
  rcases residual with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, checkpoint⟩
  dsimp only at pointEq
  have counted := aligned.graphSuffix.countEq
  change rank + eventCount program = (graph setup).order.eventCount at counted
  have nextDecode (state : ProtocolState program) (next : (graph setup).Config)
      (read : decodeSourcePrefix? program refs source.registry source.revelations embedding.ref
        1 next.store (decodeHistory setup.program next.history) next.defaults = some state) :
      sourceServicePrefix? setup (rank + 1) next = some (lift state) := by
    unfold sourceServicePrefix? serviceSourcePrefix?
    rw [transport 1, read]
    rfl
  cases program with
  | ret payoffs =>
      have := event.isLt
      simp only [eventCount] at counted
      omega
  | @sample Γ openNames name payload fresh distribution next =>
      let index : Fin (eventCount (.sample name fresh distribution next)) :=
        ⟨0, by simp [eventCount]⟩
      have headRank : (embedding.event index).val = rank := by
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have same : event = embedding.event index := Fin.ext (atRank.trans headRank.symm)
      subst same
      have outputEq : (graph setup).outputLayout (embedding.event index) =
          .publicData payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes (embedding.event index)) =
            .sample payload (compilePublicDist refs distribution) := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toEventGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
      have decodedAction : decodeEventAction setup.program (embedding.event index)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit) = none := by
        have lookup := aligned.actionEq index
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
        simpa [index, outputEq, decodeEventAction] using lookup
      obtain ⟨marker, rfl⟩ : ∃ marker : PUnit,
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) marker :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      cases marker
      have entryStep : ProtocolState.behavioralStateStep (.sample name fresh distribution next)
          residualProfile (ProtocolState.entry _ source) =
          (L.evalDist distribution (sourcePublicEnv source.state)).map (fun value =>
            Sum.inr (ProtocolState.entry next (sampleSuccessor name source value))) :=
        ProtocolState.behavioralStateStep_sample_entry residualProfile source
      rw [← pointEq, commutes, entryStep,
        sample_step config _ ready outputEq refs distribution codeEq source.state
          checkpoint.agrees, PMF.map_comp, PMF.map_comp]
      simp only [PMF.map_comp]
      apply map_congr_on_support
      intro value _
      apply nextDecode
      exact (decodeSourcePrefix?_sample fresh distribution next refs source.registry
        source.revelations embedding.ref 0 _ _ _).trans (congrArg (Option.map Sum.inr)
          ((checkpoint.sample (native := native) name (embedding.event index)
            headRank ready outputEq (fun ref => refsBefore ref index) decodedAction
            value).decode next (fun tail => embedding.ref tail.succ)))
  | @commit Γ openNames name owner payload fresh guard next =>
      let index : Fin (eventCount (.commit name owner fresh guard next)) :=
        ⟨0, by simp [eventCount]⟩
      have headRank : (embedding.event index).val = rank := by
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have same : event = embedding.event index := Fin.ext (atRank.trans headRank.symm)
      have actor : (graph setup).actor? (embedding.event index) = some owner := by
        change (toEventGraph setup.program).actor? (embedding.event index) = some owner
        simpa [index, eventOwner?, eventCount] using aligned.actorEq index
      rw [same, actor] at actorless
      cases actorless
  | @reveal Γ openNames published owner name payload fresh selected unresolved next =>
      let index : Fin (eventCount (.reveal published owner name fresh selected unresolved next)) :=
        ⟨0, by simp [eventCount]⟩
      have headRank : (embedding.event index).val = rank := by
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have same : event = embedding.event index := Fin.ext (atRank.trans headRank.symm)
      have actor : (graph setup).actor? (embedding.event index) = some owner := by
        change (toEventGraph setup.program).actor? (embedding.event index) = some owner
        simpa [index, eventOwner?, eventCount] using aligned.actorEq index
      rw [same, actor] at actorless
      cases actorless

variable {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) (initialLaw setup) horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup timeouts leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

/-- The actual finite native chance phase realizes every source chance successor
with its exact probability at the next clean prefix. -/
theorem counted_chance_stopped_sourceLaw
    (completes : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      (application setup timeouts leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup timeouts leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (event : (graph setup).EventId) (atRank : event.val = rank)
    (actorless : (graph setup).actor? event = none)
    (profile : BehavioralProfile setup.program)
    (residual : SourceResidual setup profile rank control.execution.application.config)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank control.execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    ((N).runBehavioralUntil certificate players
      (fun stop => LateStopped setup timeouts leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) start).map
          (fun final => nativeDecodedState setup timeouts leaks final.state) =
      (ProtocolState.behavioralStateStep setup.program profile point).map some := by
  classical
  let config := control.execution.application.config
  let ready := (ready_iff_rank setup config rank residual.checkpoint.ordered event).mpr atRank
  let action := ((graph setup).nodes event).actionOfActorNone actorless
  let phase := (N).runBehavioralUntil certificate players
    (fun stop => LateStopped setup timeouts leaks bounds horizon scheduler rank stop ∨
      ¬ Clear stop.state) start
  let decode : Option (graph setup).Config → setup.ProtocolState :=
    fun next => next.bind (sourceServicePrefix? setup (rank + 1))
  have configLaw := counted_chance_stopped_configLaw (timeouts := timeouts) completes certificate
    players start current residual.checkpoint.ordered event ready actorless action decoded intended
  have graphLaw := residual.chance_step_sourceLaw event atRank ready actorless action decoded
  calc
    _ = (phase.map (fun final => final.state.map
          (fun next => next.execution.application.config))).map decode := by
      rw [PMF.map_comp]
      apply map_congr_on_support
      intro final supported
      have mapped : final.state.map (fun next => next.execution.application.config) ∈
          (phase.map (fun final => final.state.map
            (fun next => next.execution.application.config))).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
      rw [configLaw, PMF.mem_support_map_iff] at mapped
      obtain ⟨next, sampled, same⟩ := mapped
      cases state : final.state with
      | none =>
          simp only [state, Option.map_none] at same
          cases same
      | some ending =>
          have nextEq : next = ending.execution.application.config := by
            simpa only [state, Option.map_some, Option.some.injEq] using same
          have nextPrefix : ending.execution.application.config.cut.IsPrefix (rank + 1) := by
            rw [config.step_cut event ready action _ (nextEq ▸ sampled)]
            exact residual.checkpoint.ordered.complete_at event ready atRank
          simp only [Function.comp_apply, state, Option.map_some, decode, Option.bind_some,
            nativeDecodedState]
          exact decodedPoint_eq_of_isPrefix nextPrefix
    _ = _ := by
      rw [configLaw, PMF.map_comp]
      simpa only [decode, Function.comp_def, Option.bind_some] using graphLaw

end Vegas
