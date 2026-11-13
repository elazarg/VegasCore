module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketBeliefWiring
public import Vegas.Game.OnePacketSwapRegular
public import Vegas.Game.SourceDebtObservation

@[expose] public section

/-! # Cleanliness and own debt at projected intended decisions

A native decision that projects to a genuine intended source information site
displays no public default and owes no own source failure in any history of its
information fiber. These are consequences of the source observation, independent
of forcedness, first activation, equilibrium or service assumptions.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler

omit [Fintype Player] in
private theorem input_some_of_projected_intended_site
    {who : Player} (source : setup.intendedModel.InformationSite who)
    (info : (application setup timeouts leaks).Info)
    (projected : source.1 = projectView setup timeouts leaks who info) :
    ∃ past view, info = some (past, view) := by
  cases input : info with
  | none =>
    have sourceNone : source.1 = none := by
      simpa only [input, projectView] using projected
    obtain ⟨_, _, action, offered⟩ := source.2
    change some action ∈ setup.intendedMenu who source.1 at offered
    rw [sourceNone] at offered
    cases (show some action = none from offered)
  | some data => exact ⟨data.1, data.2, rfl⟩

/-- Any decoded point in a native fiber projected to an actual intended source
site has no own source debt and no public exclusion. -/
theorem decoded_invariants_of_projected_intended_site
    (wellFormed : setup.WellFormed)
    {who : Player} (source : setup.intendedModel.InformationSite who)
    (site : (N).InformationSite who)
    (projected : source.1 = projectView setup timeouts leaks who site.1)
    (history : (N).InformationHistory who site.1)
    (point : ProtocolState setup.program)
    (decoded : nativeDecodedState setup timeouts leaks history.1.state = some point) :
    (¬ ProtocolState.OwesFailure who setup.program point) ∧
      ∀ other, ¬ ProtocolState.Excluded other setup.program point := by
  obtain ⟨sourceHistory, _, _⟩ := source.2
  have sourceActive := InformationSite.active setup.intendedModel source sourceHistory
  cases sourceState : sourceHistory.1.state with
  | none =>
    rw [sourceState] at sourceActive
    change False at sourceActive
    exact sourceActive.elim
  | some sourcePoint =>
    have intended := intended_of_history wellFormed sourceHistory.1.trace sourcePoint sourceState
    have sourceStatic : ProtocolState.StaticAt setup.program []
        (Revelations.initial setup.context) sourcePoint := by
      have static := setup.staticState_trace sourceHistory.1.trace
      rw [sourceState] at static
      exact static
    obtain ⟨past, view, input⟩ := input_some_of_projected_intended_site source site.1 projected
    obtain ⟨control, state, observed⟩ := control_of_infoOf (timeouts := timeouts) history.1
      (history.2.trans input)
    rw [state] at decoded
    obtain ⟨rank, ordered, read⟩ := decodedPoint_isPrefix decoded
    have nativeProjection := projectView_observe setup timeouts leaks who control.execution rank
      ordered point read past
    rw [observed] at nativeProjection
    have sourceInfo : source.1 = setup.protocolObserve who (some sourcePoint) := by
      rw [← sourceHistory.2, setup.intended_info, sourceState]
    have projectedHere : source.1 =
        projectView setup timeouts leaks who (some (past, view)) := by
      simpa only [input] using projected
    have sameSome := nativeProjection.symm.trans (projectedHere.symm.trans sourceInfo)
    have same : ProtocolState.observe who setup.program point =
        ProtocolState.observe who setup.program sourcePoint := Option.some.inj sameSome
    constructor
    · exact fun owes => ProtocolState.Intended.not_owesFailure who setup.program sourcePoint
        intended ((ProtocolState.owesFailure_iff_of_observe_eq who setup.program []
          (Revelations.initial setup.context) point sourcePoint (decodedPoint_staticAt decoded)
            sourceStatic same).mp owes)
    · intro other excluded
      exact ProtocolState.not_excluded_of_intended other setup.program sourcePoint intended
        ((ProtocolState.excluded_iff_of_observe_eq other who setup.program point
          sourcePoint same).mp excluded)

/-- Projection to a genuine intended source site forces the displayed public
default set to be empty. -/
theorem clearInput_of_projected_intended_site
    (wellFormed : setup.WellFormed)
    {who : Player} (source : setup.intendedModel.InformationSite who)
    (site : (N).InformationSite who)
    (projected : source.1 = projectView setup timeouts leaks who site.1) :
    ClearInput timeouts leaks site.1 := by
  obtain ⟨past, view, input⟩ := input_some_of_projected_intended_site source site.1 projected
  obtain ⟨history, _, _⟩ := site.2
  obtain ⟨control, state, observed⟩ := control_of_infoOf (timeouts := timeouts) history.1
    (history.2.trans input)
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (timeouts := timeouts)
    (failureProfile setup.program) (bounds.onePacketMenu timeouts leaks) horizon scheduler
      history.1.trace control state
  let point := residual.lift (ProtocolState.entry residual.program residual.source)
  have actual : decodedPoint setup control.execution.application.config = some point :=
    decodedPoint_eq residual
  have decoded : nativeDecodedState setup timeouts leaks history.1.state = some point := by
    rw [state]
    exact actual
  have properties := decoded_invariants_of_projected_intended_site wellFormed source site projected
    history point decoded
  have clear : control.execution.application.config.defaulted = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro other present
    apply properties.2 other
    unfold ProtocolState.Excluded
    rw [ProtocolState.defaulted_eq_defaults, decodedPoint_defaults actual]
    exact present
  refine ⟨past, view, input, ?_⟩
  rw [← observed]
  exact clear

/-- Every decoded history of a native site projected to an intended source
site is free of the deciding player's source debt. -/
theorem siteDebtFree_of_projected_intended_site
    (wellFormed : setup.WellFormed)
    {who : Player} (source : setup.intendedModel.InformationSite who)
    (site : (N).InformationSite who)
    (projected : source.1 = projectView setup timeouts leaks who site.1) :
    SiteDebtFree setup timeouts leaks bounds horizon scheduler site := by
  intro history point decoded
  exact (decoded_invariants_of_projected_intended_site wellFormed source site projected
    history point decoded).1

end Vegas
