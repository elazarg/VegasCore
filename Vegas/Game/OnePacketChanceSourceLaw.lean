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
  {timeouts : EventTimeouts setup.informationGraph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}

/-- A reached chance completion has exactly the source one-step law on decoded prefixes. -/
theorem SourceResidual.chance_step_sourceLaw
    {profile : BehavioralProfile setup.program} {rank : Nat} {config :
      setup.informationGraph.Config}
    (residual : SourceResidual setup profile rank config) (event : setup.informationGraph.EventId)
    (_atRank : event.val = rank) (ready : config.cut.Ready event)
    (actorless : setup.informationGraph.actor? event = none)
    (action : setup.informationGraph.Action event) {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank config = some point) :
    (config.step event ready action).map (sourceServicePrefix? setup (rank + 1)) =
      (ProtocolState.behavioralStateStep setup.program profile point).map some := by
  have pointEq := Option.some.inj (residual.decode.symm.trans decoded)
  have actionEq := EventGraph.EventCode.action_eq_of_actor_none
    (setup.informationGraph.nodes event) actorless
    (EventGraph.EventCode.actionOfActorNone (setup.informationGraph.nodes event) actorless) action
  have law := residual.eventStep_law event ready
  rw [EventGraph.eventStep, EventGraph.actionLaw_of_ownerless _ _ actorless,
    PMF.pure_bind, actionEq, pointEq] at law
  exact law

variable {bounds : MessageBounds setup.informationGraph} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) (initialLaw setup) horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup timeouts leaks)
    (fun native : EventGraphRuntime.State setup.informationGraph =>
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
    (event : setup.informationGraph.EventId) (atRank : event.val = rank)
    (actorless : setup.informationGraph.actor? event = none)
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
  let action := (setup.informationGraph.nodes event).actionOfActorNone actorless
  let phase := (N).runBehavioralUntil certificate players
    (fun stop => LateStopped setup timeouts leaks bounds horizon scheduler rank stop ∨
      ¬ Clear stop.state) start
  let decode : Option setup.informationGraph.Config → setup.ProtocolState :=
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
