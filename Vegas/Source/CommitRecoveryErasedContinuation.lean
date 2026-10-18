/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryErasedStep
import Vegas.Source.CommitRecoveryProjection
import Vegas.Source.SetupProtocolEvaluation
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # Source continuations under erased private-word prescriptions

The original source runner and information histories are retained. The
prescription condition identifies only action laws at the same erased
information. Actual chance, exclusion, restore and close transitions supply
the continuation comparison.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- Terminal semantic readout does not read remembered choices. -/
theorem readout_withHistory : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (past : History Player L),
    readout program (withHistory program point past) = readout program point
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact readout_withHistory next point past
  | _, _, .commit _ _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact readout_withHistory next point past
  | _, _, .reveal _ _ _ _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact readout_withHistory next point past

end ProtocolState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- The actual semantic source state and every owner's erased full query. -/
def commitRecoveryErasedHistory (history : setup.commitRecoveryProtocol.History) :
    setup.commitRecoveryProtocol.State ×
      ((who : Player) → setup.commitRecoveryModel.InfoState who) :=
  (history.state.map CommitRecoveryState.eraseHistory,
    fun who => setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryModel.infoOf who history.trace))

/-- The next erased queries keep all old public signals. Only the private
remembered words and their derived own-play tags are absent. -/
def commitRecoveryNextErasedHistory
    (before : setup.commitRecoveryProtocol.State ×
      ((who : Player) → setup.commitRecoveryModel.InfoState who))
    (next : setup.commitRecoveryProtocol.State) :
    setup.commitRecoveryProtocol.State ×
      ((who : Player) → setup.commitRecoveryModel.InfoState who) :=
  (next, fun who =>
    (((setup.commitRecoveryPrivate who next, setup.commitRecoveryPublic next),
      (((before.2 who).1.1.1.map (ProtocolView.publicOnly who setup.program),
        (before.2 who).1.1.2) :: (before.2 who).1.2)), []))

private theorem erased_private (who : Player) (state : setup.commitRecoveryProtocol.State) :
    setup.commitRecoveryPrivate who (state.map CommitRecoveryState.eraseHistory) =
      (setup.commitRecoveryPrivate who state).map
        (ProtocolView.eraseHistory who setup.program) := by
  cases state with
  | none => rfl
  | some current => exact congrArg some (ProtocolView.eraseHistory_observe who _ _).symm

private theorem erased_public (state : setup.commitRecoveryProtocol.State) :
    setup.commitRecoveryPublic (state.map CommitRecoveryState.eraseHistory) =
      setup.commitRecoveryPublic state := by
  cases state with
  | none => rfl
  | some current =>
      simp only [Option.map_some, commitRecoveryPublic, CommitRecoveryState.eraseHistory,
        ProtocolState.remaining_withHistory]

private theorem erased_readout (state : setup.commitRecoveryProtocol.State) :
    setup.protocolReadout (setup.commitRecoverySourceState
        (state.map CommitRecoveryState.eraseHistory)) =
      setup.protocolReadout (setup.commitRecoverySourceState state) := by
  cases state with
  | none => rfl
  | some current =>
      exact ProtocolState.readout_withHistory setup.program current.point (fun _ => [])

/-- An actual next logical signal depends on the old erased query and actual
next semantic state, without assuming equality of old private signal words. -/
theorem commitRecoveryErasedHistory_extend
    (history : setup.commitRecoveryProtocol.History)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal history.state joint)
    {target : setup.commitRecoveryProtocol.State}
    (realized : target ∈ (setup.commitRecoveryProtocol.step history.state ⟨joint, legal⟩).support) :
    setup.commitRecoveryErasedHistory (history.extend legal realized) =
      setup.commitRecoveryNextErasedHistory (setup.commitRecoveryErasedHistory history)
        (target.map CommitRecoveryState.eraseHistory) := by
  refine Prod.ext rfl ?_
  funext who
  let old := setup.commitRecoveryErasedInformation who
    (setup.commitRecoveryModel.infoOf who history.trace)
  change setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryModel.infoOf who (history.trace.extend joint legal realized)) =
    (((setup.commitRecoveryPrivate who (target.map CommitRecoveryState.eraseHistory),
        setup.commitRecoveryPublic (target.map CommitRecoveryState.eraseHistory)),
      (old.1.1.1.map (ProtocolView.publicOnly who setup.program), old.1.1.2) :: old.1.2), [])
  rw [setup.erased_private, setup.erased_public]
  dsimp only [old]
  rw [InfoSignals.infoOf_extend]
  simp only [commitRecoveryErasedInformation, commitRecoveryModel,
    InfoSignals.withOwnPlayRecall, commitRecoverySignals, List.map_cons, Option.map_map,
    Function.comp_def, ProtocolView.publicOnly_eraseHistory]

private theorem step_erased_state
    {first second : setup.commitRecoveryProtocol.State}
    (same : first.map CommitRecoveryState.eraseHistory =
      second.map CommitRecoveryState.eraseHistory)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (firstLegal : setup.commitRecoveryProtocol.Legal first joint)
    (secondLegal : setup.commitRecoveryProtocol.Legal second joint) :
    (setup.commitRecoveryProtocol.step first ⟨joint, firstLegal⟩).map
        (Option.map CommitRecoveryState.eraseHistory) =
      (setup.commitRecoveryProtocol.step second ⟨joint, secondLegal⟩).map
        (Option.map CommitRecoveryState.eraseHistory) := by
  cases first with
  | none => cases second <;> cases same; rfl
  | some first =>
      cases second with
      | none => cases same
      | some second =>
          have states := Option.some.inj same
          simp only [commitRecoveryProtocol, PMF.map_comp]
          change (first.step joint).map (some ∘ CommitRecoveryState.eraseHistory) =
            (second.step joint).map (some ∘ CommitRecoveryState.eraseHistory)
          rw [← PMF.map_comp, ← PMF.map_comp, ← first.step_eraseHistory,
            ← second.step_eraseHistory, states]

/-- Terminal status cannot depend on a discarded source word. -/
theorem commitRecovery_terminal_eq_of_erased
    {first second : setup.commitRecoveryProtocol.State}
    (same : first.map CommitRecoveryState.eraseHistory =
      second.map CommitRecoveryState.eraseHistory) :
    setup.commitRecoveryProtocol.terminal first ↔ setup.commitRecoveryProtocol.terminal second := by
  cases first with
  | none => cases second <;> cases same; rfl
  | some first =>
      cases second with
      | none => cases same
      | some second =>
          have ranks := congrArg (fun state : CommitRecoveryState setup.program =>
            ProtocolState.remaining setup.program state.point) (Option.some.inj same)
          simp only [CommitRecoveryState.eraseHistory, ProtocolState.remaining_withHistory] at ranks
          change ProtocolState.terminal setup.program first.point ↔
            ProtocolState.terminal setup.program second.point
          rw [← ProtocolState.remaining_zero_iff_terminal,
            ← ProtocolState.remaining_zero_iff_terminal, ranks]

variable [Fintype Player]

private theorem oneStep_erased_history
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) :
    (setup.commitRecoveryModel.runBehavioralFrom profile 1 history).map
        setup.commitRecoveryErasedHistory =
      (setup.commitRecoveryModel.behavioralJoint profile history.trace running).bind fun draw =>
        (setup.commitRecoveryProtocol.step history.state draw).map
          (fun target => setup.commitRecoveryNextErasedHistory
        (setup.commitRecoveryErasedHistory history)
            (target.map CommitRecoveryState.eraseHistory)) := by
  rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ 0 running, PMF.map_bind]
  apply congrArg (PMF.bind _)
  funext draw
  change ((setup.commitRecoveryProtocol.step history.state draw).bindOnSupport
    (fun target realized => PMF.pure (history.extend draw.2 realized))).map
      setup.commitRecoveryErasedHistory = _
  simp only [map_bindOnSupport, PMF.pure_map]
  rw [← pmf_bind_pure_eq_map]
  apply bindOnSupport_eq_bind_of_eq_on_support
  intro target realized
  exact congrArg PMF.pure (setup.commitRecoveryErasedHistory_extend history draw.1 draw.2 realized)

/-- A profile whose actual raw choice laws factor through erased information
has equal complete one-step erased-history laws at equal erased histories. -/
theorem commitRecovery_oneStep_erased_eq
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (erased : ∀ who first second,
      setup.commitRecoveryErasedInformation who first =
          setup.commitRecoveryErasedInformation who second →
        (profile who first).map Subtype.val = (profile who second).map Subtype.val)
    (first second : setup.commitRecoveryProtocol.History)
    (same : setup.commitRecoveryErasedHistory first = setup.commitRecoveryErasedHistory second)
    (running : ¬ setup.commitRecoveryProtocol.terminal first.state) :
    (setup.commitRecoveryModel.runBehavioralFrom profile 1 first).map
        setup.commitRecoveryErasedHistory =
      (setup.commitRecoveryModel.runBehavioralFrom profile 1 second).map
        setup.commitRecoveryErasedHistory := by
  have stateEq := congrArg Prod.fst same
  have secondRunning : ¬ setup.commitRecoveryProtocol.terminal second.state :=
    fun stopped => running ((setup.commitRecovery_terminal_eq_of_erased stateEq).mpr stopped)
  have jointEq :
      (setup.commitRecoveryModel.behavioralJoint profile first.trace running).map Subtype.val =
        (setup.commitRecoveryModel.behavioralJoint profile second.trace secondRunning).map
          Subtype.val := by
    rw [InformationModel.behavioralJoint_map_val, InformationModel.behavioralJoint_map_val]
    congr 1
    funext who
    exact erased who _ _ (congrFun (congrArg Prod.snd same) who)
  rw [setup.oneStep_erased_history profile first running,
    setup.oneStep_erased_history profile second secondRunning]
  apply bind_eq_of_map_eq _ _ Subtype.val Subtype.val jointEq
  intro left _leftSupport right _rightSupport joints
  rcases left with ⟨left, leftLegal⟩
  rcases right with ⟨right, rightLegal⟩
  dsimp only at joints
  subst right
  have raw := setup.step_erased_state stateEq left leftLegal rightLegal
  have mapped := congrArg
    (PMF.map (setup.commitRecoveryNextErasedHistory (setup.commitRecoveryErasedHistory first))) raw
  rw [← same]
  convert mapped using 1 <;> rw [PMF.map_comp] <;> rfl

/-- The original stopped source runner preserves erased histories under an
actual erased-information prescription. The continuation law is derived from
the source kernel, not supplied as an additional comparison hypothesis. -/
theorem commitRecovery_runUntil_erased_eq
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (erased : ∀ who first second,
      setup.commitRecoveryErasedInformation who first =
          setup.commitRecoveryErasedInformation who second →
        (profile who first).map Subtype.val = (profile who second).map Subtype.val)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (stopped : (setup.commitRecoveryProtocol.State ×
      ((who : Player) → setup.commitRecoveryModel.InfoState who)) → Prop) :
    ∀ first second,
      setup.commitRecoveryErasedHistory first = setup.commitRecoveryErasedHistory second →
      (setup.commitRecoveryModel.runBehavioralUntil certificate profile
        (stopped ∘ setup.commitRecoveryErasedHistory) first).map
          setup.commitRecoveryErasedHistory =
        (setup.commitRecoveryModel.runBehavioralUntil certificate profile
          (stopped ∘ setup.commitRecoveryErasedHistory) second).map
            setup.commitRecoveryErasedHistory := by
  classical
  intro first
  induction first using certificate.induction with
  | _ first ih =>
      intro second same
      have terminals := setup.commitRecovery_terminal_eq_of_erased (congrArg Prod.fst same)
      by_cases stop : stopped (setup.commitRecoveryErasedHistory first)
      · have otherStop : stopped (setup.commitRecoveryErasedHistory second) := same ▸ stop
        rw [setup.commitRecoveryModel.runBehavioralUntil_of_stopped certificate profile stop,
          setup.commitRecoveryModel.runBehavioralUntil_of_stopped certificate profile otherStop,
          PMF.pure_map, PMF.pure_map, same]
      by_cases ended : setup.commitRecoveryProtocol.terminal first.state
      · rw [setup.commitRecoveryModel.runBehavioralUntil_of_terminal certificate profile ended,
          setup.commitRecoveryModel.runBehavioralUntil_of_terminal certificate profile
            (terminals.mp ended),
          PMF.pure_map, PMF.pure_map, same]
      have otherGoing : ¬ stopped (setup.commitRecoveryErasedHistory second) :=
        fun yes => stop (same.symm ▸ yes)
      have otherRunning : ¬ setup.commitRecoveryProtocol.terminal second.state :=
        fun yes => ended (terminals.mpr yes)
      rw [setup.commitRecoveryModel.runBehavioralUntil_of_running certificate profile stop ended,
        setup.commitRecoveryModel.runBehavioralUntil_of_running certificate profile
          otherGoing otherRunning,
        PMF.map_bind, PMF.map_bind]
      apply bind_eq_of_map_eq _ _ setup.commitRecoveryErasedHistory
        setup.commitRecoveryErasedHistory
        (setup.commitRecovery_oneStep_erased_eq profile erased first second same ended)
      intro left leftMember right _rightMember sameNext
      exact ih left
        (setup.commitRecoveryModel.mem_support_runBehavioralFrom_one profile ended leftMember).1
        right sameNext

private theorem terminal_eq_until (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (history : setup.commitRecoveryProtocol.History) :
    setup.commitRecoveryModel.runBehavioralTerminalFrom certificate profile history =
      setup.commitRecoveryModel.runBehavioralUntil certificate profile (fun _ => False)
        history := by
  rw [setup.commitRecoveryModel.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate
    profile (fun _ => False)]
  calc
    _ = (setup.commitRecoveryModel.runBehavioralUntil certificate profile (fun _ => False)
        history).bind PMF.pure := by
      apply bind_congr_on_support
      intro final supported
      have ended := setup.commitRecoveryModel.mem_support_runBehavioralUntil certificate profile
        (fun _ => False) history final supported
      exact setup.commitRecoveryProtocol.randomizedBackwardLaw_of_terminal
        (ended.resolve_left (fun impossible => impossible))
    _ = _ := PMF.bind_pure _

/-- The same selected source prescription gives the same entire terminal
semantic/exclusion law after private-word erasure. Accepted failed bindings
remain in the live typed state until the actual restore removes them. -/
theorem commitRecovery_terminal_erased_eq
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (erased : ∀ who first second,
      setup.commitRecoveryErasedInformation who first =
          setup.commitRecoveryErasedInformation who second →
        (profile who first).map Subtype.val = (profile who second).map Subtype.val)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (first second : setup.commitRecoveryProtocol.History)
    (same : setup.commitRecoveryErasedHistory first = setup.commitRecoveryErasedHistory second) :
    (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate profile first).map
        (fun history => history.state.map CommitRecoveryState.eraseHistory) =
      (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate profile second).map
        (fun history => history.state.map CommitRecoveryState.eraseHistory) := by
  have law := setup.commitRecovery_runUntil_erased_eq profile erased certificate (fun _ => False)
    first second same
  simp only [Function.comp_def] at law
  rw [← setup.terminal_eq_until certificate profile first,
    ← setup.terminal_eq_until certificate profile second] at law
  have projected := congrArg (PMF.map Prod.fst) law
  simpa only [PMF.map_comp, Function.comp_def, commitRecoveryErasedHistory] using projected

/-- The actual original source terminal readout and permanent exclusion set
have the same JOINT law. In particular arbitrary source utilities and the
permanent-exclusion payoff can be read from this same joint law. -/
theorem commitRecovery_terminal_readout_excluded_erased_eq
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (erased : ∀ who first second,
      setup.commitRecoveryErasedInformation who first =
          setup.commitRecoveryErasedInformation who second →
        (profile who first).map Subtype.val = (profile who second).map Subtype.val)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (first second : setup.commitRecoveryProtocol.History)
    (same : setup.commitRecoveryErasedHistory first = setup.commitRecoveryErasedHistory second) :
    (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate profile first).map
        (fun history =>
          (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            (setup.commitRecoveryPublic history.state).1)) =
      (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate profile second).map
        (fun history =>
          (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            (setup.commitRecoveryPublic history.state).1)) := by
  have law := setup.commitRecovery_terminal_erased_eq profile erased certificate first second same
  have projected := congrArg (PMF.map (fun state : setup.commitRecoveryProtocol.State =>
    (setup.protocolReadout (setup.commitRecoverySourceState state),
      (setup.commitRecoveryPublic state).1))) law
  simpa only [PMF.map_comp, Function.comp_def, erased_readout, erased_public] using projected

end Setup
end Vegas.SourceProgram
