module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketExtension
public import Interaction.ReactiveResponseEvaluation

@[expose] public section

/-! # Exact assessment transport through audit extension and raw aliases -/

noncomputable section

namespace Vegas.EventGraphRuntime.MessageBounds

open Interaction GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (bounds : MessageBounds graph) (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : PMF (State graph)) (horizon : Nat)
  (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)

private theorem map_transport_law {Index : Type*} {Value : Index → Type*}
    (laws : ∀ info, PMF (Value info)) {first second : Index} (same : first = second) :
    (laws first).map (fun value => Eq.mp (congrArg Value same) value) = laws second := by
  subst second
  exact PMF.map_id _

/-- Every raw action law normalizes to the retained native law at the corresponding information
value, including values outside the equilibrium path. -/
theorem ExtendsOnePacketAssessment.strategy_map
    {source : ((bounds.onePacketMenu timeouts leaks).information initial horizon
      scheduler).BehavioralAssessment}
    {target : ((bounds.rawMenu timeouts leaks).information initial horizon
      scheduler).BehavioralAssessment}
    (extension : bounds.ExtendsOnePacketAssessment timeouts leaks initial horizon scheduler
      source target)
    (who : Player)
    (sourceSite : ((bounds.onePacketMenu timeouts leaks).information initial horizon
      scheduler).InformationSite who)
    (rawInfo : ((bounds.rawMenu timeouts leaks).information initial horizon
      scheduler).InfoState who)
    (same : ((reactiveNormalization timeouts) leaks).info who rawInfo =
      (bounds.onePacketRestriction timeouts leaks initial horizon scheduler).information who
        sourceSite.1) :
    (target.strategy who rawInfo).map (fun choice =>
      Eq.mp (congrArg (((bounds.menu timeouts leaks).information initial horizon
        scheduler).Choice who) same)
        (((reactiveNormalization timeouts) leaks).choice (bounds.rawMenu timeouts leaks)
          (bounds.rawMenu_recall timeouts leaks) initial horizon scheduler who rawInfo choice)) =
    (source.strategy who sourceSite.1).map
      ((bounds.onePacketRestriction timeouts leaks initial horizon scheduler).choice who
        sourceSite.1) := by
  obtain ⟨effective, strategy, _beliefs, canonical, _normalized⟩ := extension
  have projected := ((reactiveNormalization timeouts) leaks).canonicalPolicy_project
    (bounds.rawMenu timeouts leaks) (bounds.rawMenu_recall timeouts leaks)
    (bounds.rawMenu_closed timeouts leaks) initial horizon scheduler who (effective.strategy who)
    rawInfo
  rw [canonical]
  change ((bounds.canonicalRawPolicy timeouts leaks initial horizon scheduler who
    (effective.strategy who)) rawInfo).map _ = _
  calc
    _ = (((bounds.canonicalRawPolicy timeouts leaks initial horizon scheduler who
        (effective.strategy who)) rawInfo).map
          (((reactiveNormalization timeouts) leaks).choice (bounds.rawMenu timeouts leaks)
            (bounds.rawMenu_recall timeouts leaks) initial horizon scheduler who rawInfo)).map
          (fun value => Eq.mp (congrArg (((bounds.menu timeouts leaks).information initial horizon
            scheduler).Choice who) same) value) := (PMF.map_comp _ _ _).symm
    _ = (effective.strategy who (((reactiveNormalization timeouts) leaks).info who rawInfo)).map
          (fun value => Eq.mp (congrArg (((bounds.menu timeouts leaks).information initial horizon
            scheduler).Choice who) same) value) := by
      exact congrArg (fun law => law.map (fun value => Eq.mp
        (congrArg (((bounds.menu timeouts leaks).information initial horizon scheduler).Choice who)
          same) value)) projected
    _ = effective.strategy who
        ((bounds.onePacketRestriction timeouts leaks initial horizon scheduler).information who
          sourceSite.1) := map_transport_law (effective.strategy who) same
    _ = _ := strategy who sourceSite

/-- At corresponding sites, normalizing the raw posterior gives exactly the native posterior
embedded as complete effective histories, retaining the whole normalized history. -/
theorem ExtendsOnePacketAssessment.belief_history_map
    {source : ((bounds.onePacketMenu timeouts leaks).information initial horizon
      scheduler).BehavioralAssessment}
    {target : ((bounds.rawMenu timeouts leaks).information initial horizon
      scheduler).BehavioralAssessment}
    (extension : bounds.ExtendsOnePacketAssessment timeouts leaks initial horizon scheduler
      source target)
    (who : Player)
    (sourceSite : ((bounds.onePacketMenu timeouts leaks).information initial horizon
      scheduler).InformationSite who)
    (rawSite : ((bounds.rawMenu timeouts leaks).information initial horizon
      scheduler).InformationSite who)
    (same : ((reactiveNormalization timeouts) leaks).site (bounds.rawMenu timeouts leaks)
      (bounds.rawMenu_recall timeouts leaks) initial horizon scheduler who rawSite =
      (bounds.onePacketRestriction timeouts leaks initial horizon scheduler).site who sourceSite) :
    (target.belief who rawSite).map (fun history =>
      ((reactiveNormalization timeouts) leaks).history (bounds.rawMenu timeouts leaks)
        (bounds.rawMenu_recall timeouts leaks) initial horizon scheduler history.1) =
    (source.belief who sourceSite).map (fun history =>
      (bounds.onePacketRestriction timeouts leaks initial horizon scheduler).history
        history.1) := by
  obtain ⟨effective, _strategy, beliefs, _canonical, normalized⟩ := extension
  have projected := congrArg (fun law => law.map (fun history => history.1))
    (normalized who rawSite)
  have retained := congrArg (fun law => law.map (fun history => history.1))
    (beliefs who sourceSite)
  let whole := fun site : ((bounds.menu timeouts leaks).information initial horizon
      scheduler).InformationSite who =>
    (effective.belief who site).map (fun history => history.1)
  have sameWhole := congrArg whole same
  simp only [PMF.map_comp] at projected retained
  exact projected.trans (sameWhole.trans retained)

/-- Complete continuations from corresponding legal histories have identical normalized full
history laws. The evaluator's step budget is internal to complete menu evaluation. -/
theorem ExtendsOnePacketAssessment.runFrom_history_map
    {source : ((bounds.onePacketMenu timeouts leaks).information initial horizon
      scheduler).BehavioralAssessment}
    {target : ((bounds.rawMenu timeouts leaks).information initial horizon
      scheduler).BehavioralAssessment}
    (extension : bounds.ExtendsOnePacketAssessment timeouts leaks initial horizon scheduler
      source target)
    (sourceHistory : ((bounds.onePacketMenu timeouts leaks).protocol initial horizon
      scheduler).History)
    (rawHistory : ((bounds.rawMenu timeouts leaks).protocol initial horizon scheduler).History)
    (same : ((reactiveNormalization timeouts) leaks).history (bounds.rawMenu timeouts leaks)
      (bounds.rawMenu_recall timeouts leaks) initial horizon scheduler rawHistory =
      (bounds.onePacketRestriction timeouts leaks initial horizon scheduler).history
        sourceHistory) :
    ((bounds.rawMenu timeouts leaks).runFrom initial horizon scheduler target.strategy
      rawHistory).map
        (((reactiveNormalization timeouts) leaks).history (bounds.rawMenu timeouts leaks)
          (bounds.rawMenu_recall timeouts leaks) initial horizon scheduler) =
    ((bounds.onePacketMenu timeouts leaks).runFrom initial horizon scheduler source.strategy
      sourceHistory).map
        (bounds.onePacketRestriction timeouts leaks initial horizon scheduler).history := by
  obtain ⟨effective, strategy, _beliefs, canonical, _normalized⟩ := extension
  have projects (who : Player) (observed : ((reactiveApplication timeouts) leaks).Info) :
      (target.strategy who observed).map
          (((reactiveNormalization timeouts) leaks).choice (bounds.rawMenu timeouts leaks)
            (bounds.rawMenu_recall timeouts leaks) initial horizon scheduler who observed) =
        effective.strategy who (((reactiveNormalization timeouts) leaks).info who observed) := by
    rw [canonical]
    exact ((reactiveNormalization timeouts) leaks).canonicalPolicy_project
      (bounds.rawMenu timeouts leaks) (bounds.rawMenu_recall timeouts leaks)
      (bounds.rawMenu_closed timeouts leaks) initial horizon scheduler who (effective.strategy who)
      observed
  have projected := ((reactiveNormalization timeouts) leaks).runBehavioral_projection
    (bounds.rawMenu timeouts leaks) (bounds.rawMenu_recall timeouts leaks) initial horizon scheduler
    target.strategy effective.strategy projects (2 * horizon + 1) rawHistory
  have retained :=
    (bounds.onePacketRestriction timeouts leaks initial horizon scheduler).runFrom_law
    source.strategy effective.strategy strategy (2 * horizon + 1) sourceHistory
  rw [same] at projected
  exact projected.trans retained.symm

/-- At corresponding information sites, posterior-averaged complete continuations agree as
normalized full-history laws, including at sites outside the equilibrium path. -/
theorem ExtendsOnePacketAssessment.belief_runFrom_history_map
    {source : ((bounds.onePacketMenu timeouts leaks).information initial horizon
      scheduler).BehavioralAssessment}
    {target : ((bounds.rawMenu timeouts leaks).information initial horizon
      scheduler).BehavioralAssessment}
    (extension : bounds.ExtendsOnePacketAssessment timeouts leaks initial horizon scheduler
      source target)
    (who : Player)
    (sourceSite : ((bounds.onePacketMenu timeouts leaks).information initial horizon
      scheduler).InformationSite who)
    (rawSite : ((bounds.rawMenu timeouts leaks).information initial horizon
      scheduler).InformationSite who)
    (same : ((reactiveNormalization timeouts) leaks).site (bounds.rawMenu timeouts leaks)
      (bounds.rawMenu_recall timeouts leaks) initial horizon scheduler who rawSite =
      (bounds.onePacketRestriction timeouts leaks initial horizon scheduler).site who sourceSite) :
    ((target.belief who rawSite).bind (fun history =>
      (bounds.rawMenu timeouts leaks).runFrom initial horizon scheduler target.strategy
        history.1)).map
          (((reactiveNormalization timeouts) leaks).history (bounds.rawMenu timeouts leaks)
            (bounds.rawMenu_recall timeouts leaks) initial horizon scheduler) =
    ((source.belief who sourceSite).bind (fun history =>
      (bounds.onePacketMenu timeouts leaks).runFrom initial horizon scheduler source.strategy
        history.1)).map
          (bounds.onePacketRestriction timeouts leaks initial horizon scheduler).history := by
  rw [PMF.map_bind, PMF.map_bind]
  exact bind_eq_of_map_eq _ _ _ _
    (extension.belief_history_map bounds timeouts leaks initial horizon scheduler who sourceSite
      rawSite same) _ _
    (fun rawHistory _ sourceHistory _ histories =>
      extension.runFrom_history_map bounds timeouts leaks initial horizon scheduler sourceHistory.1
        rawHistory.1 histories)

end Vegas.EventGraphRuntime.MessageBounds
