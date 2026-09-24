/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationHistories
import GameTheoryExtensions.Protocol.StateKernel

/-! # Finite state calculations for the validation source game -/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

def decodeSource : sourceArena.State → SourcePath
  | none => .root
  | some (.inl config) => .drawn (config.state.get .here)
  | some (.inr (.inl config)) =>
      .bound (config.state.get (.there .here)) (config.state.get .here)
  | some (.inr (.inr (.inl config))) =>
      .dummyPublished (config.state.get (.there (.there .here)))
        (config.state.get (.there .here)) (OwnAction.disclosure (config.history false)[1]?)
  | some (.inr (.inr (.inr (.inl config)))) =>
      .secretPublished (config.state.get (.there (.there (.there .here))))
        (config.state.get (.there (.there .here)))
        (OwnAction.disclosure (config.history false)[1]?)
        (OwnAction.disclosure (config.history false)[2]?)
  | some (.inr (.inr (.inr (.inr config)))) =>
      .done (config.state.get (.there (.there (.there (.there .here)))))
        (config.state.get (.there (.there (.there .here))))
        (OwnAction.disclosure (config.history false)[1]?)
        (OwnAction.disclosure (config.history false)[2]?)
        (OwnAction.disclosure (config.history true)[0]?)

@[simp] theorem decodeSource_state (path : SourcePath) : decodeSource path.state = path := by
  cases path <;> rfl

theorem source_state_injective : Function.Injective (History.state (E := sourceArena)) := by
  intro first second same
  obtain ⟨left, leftEq⟩ := source_history_complete first.trace
  obtain ⟨right, rightEq⟩ := source_history_complete second.trace
  change first = left.history at leftEq
  change second = right.history at rightEq
  subst first second
  have paths := congrArg decodeSource same
  simp only [SourcePath.history_state, decodeSource_state] at paths
  exact congrArg SourcePath.history paths

theorem source_info (who : Bool) (history : sourceArena.History) :
    sourceModel.infoOf who history.trace = sourceSetup.protocolObserve who history.state :=
  sourceSetup.protocol_info sourceAdmission who history.trace

def sourceChoice (profile : Profile sourceModel.behavioralSignature) (who : Bool)
    (info : sourceModel.InfoState who) : FinDist (Option (sourceArena.Action who)) :=
  (profile who info).map Subtype.val

def sourceKernel (profile : Profile sourceModel.behavioralSignature) :
    sourceArena.State → FinDist sourceArena.State
  | none => sourceSetup.initialLaw.map (fun state => some (.inl (sourceSetup.initialConfig state)))
  | some (.inl config) =>
      (sourceChoice profile false (some (.inl (config.view false)))).map fun choice =>
        some (.inr (.inl (commitSuccessor 3 rejectingGuard config
          (OwnAction.binding (L := simpleExpr) false 3 .bool choice))))
  | some (.inr (.inl config)) =>
      (sourceChoice profile false (some (.inr (.inl (config.view false))))).map fun choice =>
        some (.inr (.inr (.inl (revealSuccessor 4 .here config
          (OwnAction.disclosure choice)))))
  | some (.inr (.inr (.inl config))) =>
      (sourceChoice profile false (some (.inr (.inr (.inl (config.view false)))))).map fun choice =>
        some (.inr (.inr (.inr (.inl (revealSuccessor 5 (.there (.there (.there .here)))
          config (OwnAction.disclosure choice))))))
  | some (.inr (.inr (.inr (.inl config)))) =>
      (sourceChoice profile true (some (.inr (.inr (.inr (.inl (config.view true))))))).map
        fun choice =>
        some (.inr (.inr (.inr (.inr (revealSuccessor 6
          (.there (.there (.there (.there (.there .here)))))
          config (OwnAction.disclosure choice))))))
  | some (.inr (.inr (.inr (.inr config)))) =>
      FinDist.pure (some (.inr (.inr (.inr (.inr config)))))

theorem source_chooser_kernel (profile : Profile sourceModel.behavioralSignature)
    (history : sourceArena.History) (running : ¬ sourceArena.terminal history.state) :
    (sourceModel.singleMoverChooser sourceSingle
      profile history running).bind (sourceArena.step history.state) =
        sourceKernel profile history.state := by
  have marginal (who : Bool) := sourceModel.singleMoverJoint_marginal
    sourceSingle profile history running who
  have marginalState (who : Bool) :
      (sourceModel.singleMoverJoint sourceSingle profile history running).map
        (fun joint => joint.1 who) =
      (profile who (sourceSetup.protocolObserve who history.state)).map Subtype.val := by
    rw [marginal]
    rw [source_info]
  have project (who : Bool) (f : Option (sourceArena.Action who) → sourceArena.State) :
      (sourceModel.singleMoverChooser sourceSingle profile history running).map
        (fun joint => f (joint.1 who)) =
      (sourceChoice profile who (sourceSetup.protocolObserve who history.state)).map f := by
    exact (FinDist.map_comp f (fun joint => joint.1 who)
      (sourceModel.singleMoverJoint sourceSingle profile history running)).symm.trans
        (congrArg (FinDist.map f) (marginalState who))
  rcases history with ⟨state, trace⟩
  rcases state with _ | state
  · change (sourceModel.singleMoverChooser sourceSingle profile _ running).bind
      (fun _ => sourceKernel profile none) = sourceKernel profile none
    exact FinDist.bind_const _ _
  rcases state with config | config | config | config | config
  all_goals try exact (running trivial).elim
  all_goals
    conv_lhs =>
      arg 2
      ext joint
      simp only [sourceArena, Setup.executionProtocol, Setup.protocolStep,
        sourceSetup, sourceProgram, ProtocolState.step, ProtocolState.entry,
        Sum.elim_inl, Sum.elim_inr, FinDist.map_pure]
  all_goals
    conv_lhs => rw [← FinDist.map_eq_bind]
  all_goals
    dsimp only [sourceKernel]
  · exact project false (fun choice => some (.inr (.inl
      (commitSuccessor 3 rejectingGuard config
        (OwnAction.binding (L := simpleExpr) false 3 .bool choice)))))
  · exact project false (fun choice => some (.inr (.inr (.inl
      (revealSuccessor 4 .here config (OwnAction.disclosure choice))))))
  · exact project false (fun choice => some (.inr (.inr (.inr (.inl
      (revealSuccessor 5 (.there (.there (.there .here))) config
        (OwnAction.disclosure choice)))))))
  · exact project true (fun choice => some (.inr (.inr (.inr (.inr
      (revealSuccessor 6 (.there (.there (.there (.there (.there .here))))) config
        (OwnAction.disclosure choice)))))))

theorem source_run_states (profile : Profile sourceModel.behavioralSignature)
    (fuel : Nat) (history : sourceArena.History) :
    (sourceModel.runSingleMoverBehavioralFrom sourceSingle
      profile fuel history).map History.state =
        (fun law => law.bind (sourceKernel profile))^[fuel] (FinDist.pure history.state) := by
  apply runRandomizedFor_map_state
  · intro state stopped
    rcases state with _ | config | config | config | config | config
    all_goals try contradiction
    rfl
  · exact source_chooser_kernel profile

end VegasTests.SequentialValidation
