/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketIntendedProjection
import Vegas.Game.SourceServicePrefix
import Vegas.Game.SourceServiceFacts
import Vegas.Game.SourcePrefixPublications
import GameTheoryExtensions.Analysis.Protocol.SingleMoverReach
import GameTheory.Math.Probability.Support

/-! # Public default control at decoded actors

The source actor at a decoded prefix is its static instruction owner filtered
by the same complete public default history. At an initialized quiescent
native state, every ready owned event belongs to an active player, so the
filtered actor is its static graph owner.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Any decoded ready point uses the graph's public default filter, including raw states. -/
theorem decodedPoint_actor {setup : Setup (Player := Player) (L := L)} (who : Player)
    {config : (graph setup).Config} {event : (graph setup).EventId}
    (ready : config.cut.Ready event) {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point) :
    ProtocolView.actor who setup.program (ProtocolState.observe who setup.program point) =
      ((graph setup).actor? event).filter (fun owner => decide (owner ∉ config.defaulted)) := by
  unfold decodedPoint at decoded
  split at decoded
  · rename_i ordered
    have current : config.cut.IsPrefix event.val :=
      ⟨event.isLt.le, fun query =>
        setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready _ ready⟩
    have rank : event.val = ordered.choose := current.unique ordered.choose_spec
    have inside : ordered.choose < eventCount setup.program := rank ▸ event.isLt
    have actor := decodeSourcePrefix?_actor who ordered.choose setup.program _ _ _ _ _ _ _ point
      decoded inside
    rw [actor, eventOwner?_eq_actor]
    have same : event = ⟨ordered.choose, inside⟩ := Fin.ext rank
    subst same
    rfl
  · cases decoded

/-- Quiescence makes the static owner of a ready event the decoded source actor. -/
theorem decodedPoint_actor_of_quiescent {setup : Setup (Player := Player) (L := L)}
    (who : Player) {native : EventGraphRuntime.State (graph setup)}
    (quiescent : ∀ event, ¬ native.AutomaticReady event)
    {event : (graph setup).EventId} (ready : native.config.cut.Ready event)
    {point : ProtocolState setup.program}
    (decoded : decodedPoint setup native.config = some point) :
    ProtocolView.actor who setup.program (ProtocolState.observe who setup.program point) =
      (graph setup).actor? event := by
  rw [decodedPoint_actor who ready decoded]
  cases owned : (graph setup).actor? event with
  | none => rfl
  | some owner =>
      have active := native.active_of_ready_owned quiescent ready owned
      simp [Option.filter_some, active]

/-- Initialized raw histories supply the activity needed for the static actor equality. -/
theorem decodedPoint_actor_of_history {setup : Setup (Player := Player) (L := L)}
    {runtime : EventGraphRuntime (graph setup)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (who : Player) {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
    {control : (application setup runtime leaks).Control}
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    {event : (graph setup).EventId} (ready : control.execution.application.config.cut.Ready event)
    {point : ProtocolState setup.program}
    (decoded : decodedPoint setup control.execution.application.config = some point) :
    ProtocolView.actor who setup.program (ProtocolState.observe who setup.program point) =
      (graph setup).actor? event :=
  decodedPoint_actor_of_quiescent who
    (legalFacts setup leaks horizon scheduler control trace).quiescent ready decoded

variable {setup : Setup (Player := Player) (L := L)}

/-- A decoded acting joint gives the choice only to the still-active static owner. -/
theorem actingJoint_of_decoded {config : (graph setup).Config} {event : (graph setup).EventId}
    (ready : config.cut.Ready event) {actor : Player}
    (acts : (graph setup).actor? event = some actor) {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point) (choice : Option (OwnAction Player L))
    (player : Player) :
    actingJoint setup (some point) choice player =
      if actor = player ∧ actor ∉ config.defaulted then choice else none := by
  change (if ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some player then choice else none) = _
  rw [decodedPoint_actor player ready decoded, acts]
  by_cases inactive : actor ∈ config.defaulted <;> by_cases same : actor = player <;>
    simp [Option.filter_some, inactive, same]

/-- A legal intended choice either belongs to an already defaulted owner or is not failing. -/
theorem defaulted_or_not_failing_of_legal {history : setup.intendedProtocol.History}
    {config : (graph setup).Config} {event : (graph setup).EventId}
    (ready : config.cut.Ready event) {actor : Player}
    (acts : (graph setup).actor? event = some actor) {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point) (current : history.state = some point)
    {choice : Option (OwnAction Player L)}
    (legal : setup.intendedProtocol.Legal history.state (actingJoint setup history.state choice)) :
    actor ∈ config.defaulted ∨ ¬ Failing choice := by
  by_cases inactive : actor ∈ config.defaulted
  · exact Or.inl inactive
  · right
    have localLegal := setup.intendedProtocol.legalOption_of_legal legal actor
    have own : actingJoint setup history.state choice actor = choice := by
      rw [current, actingJoint_of_decoded ready acts decoded]
      simp [inactive]
    rw [own] at localLegal
    cases choice with
    | none =>
        exfalso
        apply localLegal
        rw [current]
        change ProtocolView.actor actor setup.program
          (ProtocolState.observe actor setup.program point) = some actor
        rw [decodedPoint_actor actor ready decoded, acts]
        simp [Option.filter_some, inactive]
    | some action =>
        obtain ⟨_, available⟩ := localLegal
        rw [current] at available
        exact ProtocolView.not_failing_of_intendedAvailable actor setup.program _ action available

/-- The opponent factor is one at automatic steps; at an active owned step it is
one for the owner and the owner's action mass for every other player. -/
theorem opponentsStepProb_actingJoint [Fintype Player]
    (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (history : setup.intendedProtocol.History) {config : (graph setup).Config}
    {event : (graph setup).EventId} (ready : config.cut.Ready event) {actor : Player}
    (acts : (graph setup).actor? event = some actor) {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point) (current : history.state = some point)
    (choice : Option (OwnAction Player L))
    (legal : setup.intendedProtocol.Legal history.state (actingJoint setup history.state choice)) :
    setup.intendedModel.opponentsStepProb assessment.strategy who history.trace ⟨_, legal⟩ =
      if actor ∈ config.defaulted then 1 else if actor = who then 1 else
        (((assessment.strategy actor (setup.protocolObserve actor (some point))).map
          Subtype.val) choice).toReal := by
  have joint : ∀ player, actingJoint setup history.state choice player =
      if actor = player ∧ actor ∉ config.defaulted then choice else none := by
    intro player
    rw [current]
    exact actingJoint_of_decoded ready acts decoded choice player
  by_cases inactive : actor ∈ config.defaulted
  · rw [ite_eq_left inactive]
    apply setup.intendedModel.opponentsStepProb_eq_one_of_none assessment.strategy who
      history.trace ⟨_, legal⟩
    intro player
    change actingJoint setup history.state choice player = none
    rw [joint]
    simp [inactive]
  · rw [ite_eq_right inactive]
    have activeJoint : ∀ player, actingJoint setup history.state choice player =
        if actor = player then choice else none := by
      intro player
      rw [joint]
      simp [inactive]
    rw [setup.intendedModel.opponentsStepProb_eq_of_single assessment.strategy who history.trace
      ⟨_, legal⟩ actor fun player different => by
        change actingJoint setup history.state choice player = none
        rw [activeJoint]
        simp [Ne.symm different]]
    split_ifs with same
    · rfl
    · have value : (setup.intendedModel.choicesOfLegal history.trace ⟨_, legal⟩ actor).1 =
          choice := by
        change actingJoint setup history.state choice actor = choice
        rw [activeJoint]
        simp
      have mass := pmf_map_apply_of_injective
        (f := fun picked : setup.intendedModel.Choice actor
          (setup.intendedModel.infoOf actor history.trace) => picked.1)
        (assessment.strategy actor (setup.intendedModel.infoOf actor history.trace))
        Subtype.val_injective (setup.intendedModel.choicesOfLegal history.trace ⟨_, legal⟩ actor)
      rw [value] at mass
      rw [← mass]
      have info : setup.intendedModel.infoOf actor history.trace =
          setup.protocolObserve actor (some point) := by
        rw [setup.intended_info, current]
      rw [info]

end Vegas
