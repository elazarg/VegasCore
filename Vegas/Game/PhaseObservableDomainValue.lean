/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseObservableSourceQuery
import Vegas.Game.PhaseRecoveryDomainValue

/-! # The actual native domain kernel selected by its observable source query -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

/-- The native binding value kernel reads exactly its observable reduced query.
It has the callback type required by the counted service prescription. -/
def phaseObservableDomainValues
    (values : ∀ who info, PMF (setup.CommitRecoveryValueChoice who info))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (_past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) : PMF (L.Val payload) :=
  match phaseVirtualSourceQuery? setup mode runtime leaks plan who event view with
  | none => PMF.pure (L.someValue payload)
  | some info => (values who info).map fun choice =>
      phaseRecoveryDomainValue setup mode event who payload binding choice.1.1

omit [Fintype Player] in
private theorem normalized_typed (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) :
    (setup.commitRecoveryNoMissInformation who info).1.1.1 = info.1.1.1 := by
  unfold Setup.commitRecoveryNoMissInformation
  split
  · exact (setup.commitRecoveryWithAttemptExclusions_controls who
      (setup.commitRecoveryAttemptStart who info)
      (setup.commitRecoverySavedExclusions who info) info).1
  · rfl

private theorem query_typed (who : Player) (event : (serviceGraph setup mode).EventId)
    (view : (phaseApplication runtime leaks).PlayerView)
    (info : setup.commitRecoveryModel.InfoState who)
    (selected : phaseVirtualSourceQuery? setup mode runtime leaks plan who event view = some info) :
    ∃ typed, phaseVirtualSourceView? setup mode runtime leaks who event view = some typed ∧
      info.1.1.1 = some (ProtocolView.eraseHistory who setup.program typed) := by
  unfold phaseVirtualSourceQuery? at selected
  obtain ⟨typed, decoded, rfl⟩ := Option.map_eq_some_iff.mp selected
  refine ⟨typed, decoded, ?_⟩
  change (setup.commitRecoveryNoMissInformation who _).1.1.1.map
    (ProtocolView.eraseHistory who setup.program) = _
  rw [normalized_typed]
  simp only [Setup.commitRecoveryErasedRead, Option.map_some,
    ProtocolView.eraseHistory_idempotent]

private theorem query_value (who : Player) (event : (serviceGraph setup mode).EventId)
    (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (view : (phaseApplication runtime leaks).PlayerView)
    (info : setup.commitRecoveryModel.InfoState who)
    (selected : phaseVirtualSourceQuery? setup mode runtime leaks plan who event view = some info)
    (active : setup.commitRecoveryActive who info.1.1)
    (choice : setup.CommitRecoveryValueChoice who info) :
    phaseRecoveryBindingData setup mode event who payload binding choice.1.1 =
      (.success (phaseRecoveryDomainValue setup mode event who payload binding choice.1.1),
        false) := by
  obtain ⟨typed, decoded, current⟩ := query_typed setup mode runtime leaks plan who event view
    info selected
  unfold phaseVirtualSourceView? at decoded
  split at decoded
  · obtain ⟨original, raw, rfl⟩ := Option.map_eq_some_iff.mp decoded
    apply phaseRecoveryDomainValue_faithful setup mode _ _ who event payload binding _ []
      original raw info _ active choice
    simpa only [ProtocolView.eraseHistory_virtualBindings] using current
  · cases decoded

/-- At every actual initialized ready binding, the callback is the domain law
at the genuine original source decision's exact combined query. Every selected
choice encodes a successful typed payload; the totalization branch is unused. -/
theorem phaseObservableDomainValues_genuine
    (values : ∀ who info, PMF (setup.CommitRecoveryValueChoice who info))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (past : List (phaseApplication runtime leaks).PlayerEntry) :
    ∃ (current : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some current)),
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryModel.infoOf who sourceTrace) ∧
      let info := setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who
          (setup.commitRecoveryModel.infoOf who sourceTrace))
      let observed := control.execution.observe (phaseApplication runtime leaks) who
      phaseVirtualSourceQuery? setup mode runtime leaks plan who event observed = some info ∧
      (values who info).map
          (fun choice => phaseRecoveryBindingData setup mode event who payload binding choice.1.1) =
        (phaseObservableDomainValues setup mode runtime leaks plan values who event payload
          binding past observed).map (fun value => (.success value, false)) := by
  obtain ⟨current, sourceTrace, _actor, _position, decision, selected⟩ :=
    phaseVirtualSourceQuery?_genuine_of_ready_binding setup mode runtime leaks plan maximal
      horizon scheduler trace who event payload binding request
  let info := setup.commitRecoveryErasedInformation who
    (setup.commitRecoveryNoMissInformation who (setup.commitRecoveryModel.infoOf who sourceTrace))
  have active : setup.commitRecoveryActive who info.1.1 := by
    obtain ⟨_, _, action, offered⟩ := decision
    have offeredHere : some action ∈ setup.commitRecoveryModel.menu who info := by
      change some action ∈ setup.commitRecoveryModel.menu who
        (setup.commitRecoveryErasedInformation who (setup.commitRecoveryNoMissInformation who _))
      rw [setup.commitRecoveryErasedInformation_menu, setup.commitRecoveryNoMissInformation_menu]
      exact offered
    exact offeredHere.1
  refine ⟨current, sourceTrace, decision, selected, ?_⟩
  dsimp only [phaseObservableDomainValues]
  rw [selected, PMF.map_comp]
  apply congrArg (PMF.map · (values who info))
  funext choice
  exact query_value setup mode runtime leaks plan who event payload binding _ info selected
    active choice

end Vegas
