/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationSource
import Mathlib.Tactic.DeriveFintype

/-! # Complete source histories of the validation example -/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.SourceProgram GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

theorem sourceSingle (state : sourceArena.State) {first second : Bool}
    (one : sourceArena.active state first) (two : sourceArena.active state second) :
    first = second := sourceSetup.protocol_singleMover sourceAdmission state one two

inductive SourcePath where
  | root
  | drawn (bit : Bool)
  | bound (bit : Bool) (dummy : PublicationResult Bool)
  | dummyPublished (bit : Bool) (dummy : PublicationResult Bool) (first : Bool)
  | secretPublished (bit : Bool) (dummy : PublicationResult Bool) (first second : Bool)
  | done (bit : Bool) (dummy : PublicationResult Bool) (first second guess : Bool)
  deriving DecidableEq, Fintype

def SourcePath.state : SourcePath → sourceSetup.ProtocolState
  | .root => none
  | .drawn bit => some (.inl (startConfig bit))
  | .bound bit dummy => some (.inr (.inl (boundConfig bit dummy)))
  | .dummyPublished bit dummy first => some (.inr (.inr (.inl (dummyConfig bit dummy first))))
  | .secretPublished bit dummy first second =>
      some (.inr (.inr (.inr (.inl (secretConfig bit dummy first second)))))
  | .done bit dummy first second guess =>
      some (.inr (.inr (.inr (.inr (finalConfig bit dummy first second guess)))))

def sourceJoint (who : Bool) (action : OwnAction Bool simpleExpr) :
    ∀ player, Option (sourceArena.Action player) :=
  fun player => if player = who then some action else none

theorem source_draw_legal : sourceArena.Legal SourcePath.root.state (fun _ => none) :=
  ⟨id, fun _ => id⟩

theorem source_bind_legal (bit : Bool) (dummy : PublicationResult Bool) :
    sourceArena.Legal (SourcePath.drawn bit).state
      (sourceJoint false (.commit false 3 .bool dummy)) := by
  refine ⟨id, ?_⟩
  intro who
  cases who <;> cases dummy <;> simp [sourceArena, Setup.executionProtocol, Setup.protocolObserve,
    SourcePath.state, sourceJoint, ProtocolState.observe, ProtocolView.actor,
    ProtocolView.available, sourceSetup, sourceProgram, sourceAdmission,
    CommitmentInterface.forfeiture, CommitmentAdmission.Admits]

theorem source_dummy_legal (bit : Bool) (dummy : PublicationResult Bool) (first : Bool) :
    sourceArena.Legal (SourcePath.bound bit dummy).state
      (sourceJoint false (.reveal false 3 first)) := by
  refine ⟨id, ?_⟩
  intro who
  cases who <;> simp [sourceArena, Setup.executionProtocol, Setup.protocolObserve,
    SourcePath.state, sourceJoint, ProtocolState.observe, ProtocolView.actor,
    ProtocolView.available, sourceSetup, sourceProgram]

theorem source_secret_legal (bit : Bool) (dummy : PublicationResult Bool) (first second : Bool) :
    sourceArena.Legal (SourcePath.dummyPublished bit dummy first).state
      (sourceJoint false (.reveal false 1 second)) := by
  refine ⟨id, ?_⟩
  intro who
  cases who <;> simp [sourceArena, Setup.executionProtocol, Setup.protocolObserve,
    SourcePath.state, sourceJoint, ProtocolState.observe, ProtocolView.actor,
    ProtocolView.available, sourceSetup, sourceProgram]

theorem source_guess_legal (bit : Bool) (dummy : PublicationResult Bool)
    (first second guess : Bool) :
    sourceArena.Legal (SourcePath.secretPublished bit dummy first second).state
      (sourceJoint true (.reveal true 2 guess)) := by
  refine ⟨id, ?_⟩
  intro who
  cases who <;> simp [sourceArena, Setup.executionProtocol, Setup.protocolObserve,
    SourcePath.state, sourceJoint, ProtocolState.observe, ProtocolView.actor,
    ProtocolView.available, sourceSetup, sourceProgram]

theorem source_bind_step (bit : Bool) (dummy : PublicationResult Bool) :
    sourceArena.step (SourcePath.drawn bit).state
      ⟨_, source_bind_legal bit dummy⟩ = FinDist.pure (SourcePath.bound bit dummy).state := by
  simp [sourceArena, Setup.executionProtocol, Setup.protocolStep, SourcePath.state,
    sourceSetup, sourceProgram, ProtocolState.step, sourceJoint, boundConfig,
    OwnAction.binding_commit, ProtocolState.entry]

theorem source_dummy_step (bit : Bool) (dummy : PublicationResult Bool) (first : Bool) :
    sourceArena.step (SourcePath.bound bit dummy).state
      ⟨_, source_dummy_legal bit dummy first⟩ =
        FinDist.pure (SourcePath.dummyPublished bit dummy first).state := by
  simp [sourceArena, Setup.executionProtocol, Setup.protocolStep, SourcePath.state,
    sourceSetup, sourceProgram, ProtocolState.step, sourceJoint, dummyConfig,
    OwnAction.disclosure, ProtocolState.entry]

theorem source_secret_step (bit : Bool) (dummy : PublicationResult Bool) (first second : Bool) :
    sourceArena.step (SourcePath.dummyPublished bit dummy first).state
      ⟨_, source_secret_legal bit dummy first second⟩ =
        FinDist.pure (SourcePath.secretPublished bit dummy first second).state := by
  simp [sourceArena, Setup.executionProtocol, Setup.protocolStep, SourcePath.state,
    sourceSetup, sourceProgram, ProtocolState.step, sourceJoint, secretConfig,
    OwnAction.disclosure, ProtocolState.entry]

theorem source_guess_step (bit : Bool) (dummy : PublicationResult Bool)
    (first second guess : Bool) :
    sourceArena.step (SourcePath.secretPublished bit dummy first second).state
      ⟨_, source_guess_legal bit dummy first second guess⟩ =
        FinDist.pure (SourcePath.done bit dummy first second guess).state := by
  simp [sourceArena, Setup.executionProtocol, Setup.protocolStep, SourcePath.state,
    sourceSetup, sourceProgram, ProtocolState.step, sourceJoint, finalConfig,
    OwnAction.disclosure, ProtocolState.entry]

def SourcePath.depth : SourcePath → Nat
  | .root => 0
  | .drawn _ => 1
  | .bound .. => 2
  | .dummyPublished .. => 3
  | .secretPublished .. => 4
  | .done .. => 5

def SourcePath.trace : (path : SourcePath) → sourceArena.Trace path.state
  | .root => .start
  | .drawn bit => Trace.extend .start (fun _ => none) source_draw_legal (by
      change (SourcePath.drawn bit).state ∈ (sourceSetup.initialLaw.map _).support
      rw [FinDist.support_map]
      refine ⟨initialState bit, ?_, rfl⟩
      rw [show sourceSetup.initialLaw = (FinDist.uniformOfFintype (α := Bool)).map initialState
        from rfl, FinDist.support_map]
      exact ⟨bit, FinDist.mem_support_uniformOfFintype bit, rfl⟩)
  | .bound bit dummy => Trace.extend (SourcePath.drawn bit).trace _ (source_bind_legal bit dummy)
      (by rw [source_bind_step]; exact FinDist.mem_support_pure.mpr rfl)
  | .dummyPublished bit dummy first => Trace.extend (SourcePath.bound bit dummy).trace _
      (source_dummy_legal bit dummy first)
      (by rw [source_dummy_step]; exact FinDist.mem_support_pure.mpr rfl)
  | .secretPublished bit dummy first second =>
      Trace.extend (SourcePath.dummyPublished bit dummy first).trace _
      (source_secret_legal bit dummy first second)
      (by rw [source_secret_step]; exact FinDist.mem_support_pure.mpr rfl)
  | .done bit dummy first second guess =>
      Trace.extend (SourcePath.secretPublished bit dummy first second).trace _
      (source_guess_legal bit dummy first second guess)
      (by rw [source_guess_step]; exact FinDist.mem_support_pure.mpr rfl)
termination_by path => path.depth
decreasing_by all_goals simp [depth]

def SourcePath.history (path : SourcePath) : sourceArena.History := ⟨path.state, path.trace⟩

@[simp] theorem SourcePath.history_state (path : SourcePath) : path.history.state = path.state := by
  rfl

theorem source_active_joint {state : sourceArena.State}
    (joint : ∀ player, Option (sourceArena.Action player)) (legal : sourceArena.Legal state joint)
    (who : Bool) (active : sourceArena.active state who) :
    ∃ action, joint = sourceJoint who action ∧ action ∈ sourceArena.available state who := by
  obtain ⟨action, chosen⟩ := LegalOption.exists_eq_some_of_active (joint who)
    (sourceArena.legalOption_of_legal legal who) active
  refine ⟨action, ?_, ?_⟩
  · funext other
    by_cases same : other = who
    · subst other; simpa [sourceJoint] using chosen
    · have inactive : ¬ sourceArena.active state other := fun acts =>
        same (sourceSetup.protocol_singleMover sourceAdmission state acts active)
      simpa [sourceJoint, same] using LegalOption.eq_none_of_inactive (joint other)
        (sourceArena.legalOption_of_legal legal other) inactive
  · have available := legal.2 who
    rw [chosen] at available
    exact available.2

theorem SourcePath.step_complete (path : SourcePath)
    (joint : ∀ player, Option (sourceArena.Action player))
    (legal : sourceArena.Legal path.history.state joint) (target : sourceArena.State)
    (supported : target ∈ (sourceArena.step path.history.state ⟨joint, legal⟩).support) :
    ∃ next : SourcePath, path.history.extend legal supported = next.history := by
  cases path with
  | root =>
      have empty : joint = fun _ => none := by
        funext who
        exact LegalOption.eq_none_of_inactive (joint who)
          (sourceArena.legalOption_of_legal legal who) (by change ¬ False; exact id)
      subst joint
      change target ∈ (sourceSetup.initialLaw.map _).support at supported
      obtain ⟨initial, member, rfl⟩ := FinDist.support_map .. ▸ supported
      change initial ∈ ((FinDist.uniformOfFintype (α := Bool)).map initialState).support at member
      obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ member
      refine ⟨.drawn bit, ?_⟩
      simp only [history, trace, History.extend]
      rfl
  | drawn bit =>
      obtain ⟨action, same, available⟩ := source_active_joint joint legal false rfl
      change ∃ choice : PublicationResult Bool,
        CommitmentAdmission.forfeiture.Admits choice ∧ action = .commit false 3 .bool choice
        at available
      obtain ⟨dummy, _permitted, rfl⟩ := available
      subst joint
      change target ∈ (sourceArena.step (drawn bit).state ⟨_, legal⟩).support at supported
      rw [source_bind_step] at supported
      cases FinDist.mem_support_pure.mp supported
      refine ⟨.bound bit dummy, ?_⟩
      simp only [history, trace, History.extend]
  | bound bit dummy =>
      obtain ⟨action, same, available⟩ := source_active_joint joint legal false rfl
      change ∃ disclose : Bool, action = .reveal false 3 disclose at available
      obtain ⟨first, rfl⟩ := available
      subst joint
      change target ∈ (sourceArena.step (bound bit dummy).state ⟨_, legal⟩).support at supported
      rw [source_dummy_step] at supported
      cases FinDist.mem_support_pure.mp supported
      refine ⟨.dummyPublished bit dummy first, ?_⟩
      simp only [history, trace, History.extend]
  | dummyPublished bit dummy first =>
      obtain ⟨action, same, available⟩ := source_active_joint joint legal false rfl
      change ∃ disclose : Bool, action = .reveal false 1 disclose at available
      obtain ⟨second, rfl⟩ := available
      subst joint
      change target ∈ (sourceArena.step (dummyPublished bit dummy first).state
        ⟨_, legal⟩).support at supported
      rw [source_secret_step] at supported
      cases FinDist.mem_support_pure.mp supported
      refine ⟨.secretPublished bit dummy first second, ?_⟩
      simp only [history, trace, History.extend]
  | secretPublished bit dummy first second =>
      obtain ⟨action, same, available⟩ := source_active_joint joint legal true rfl
      change ∃ disclose : Bool, action = .reveal true 2 disclose at available
      obtain ⟨guess, rfl⟩ := available
      subst joint
      change target ∈ (sourceArena.step (secretPublished bit dummy first second).state
        ⟨_, legal⟩).support at supported
      rw [source_guess_step] at supported
      cases FinDist.mem_support_pure.mp supported
      refine ⟨.done bit dummy first second guess, ?_⟩
      simp only [history, trace, History.extend]
  | done bit dummy first second guess => exact (legal.1 trivial).elim

theorem source_history_complete : ∀ {state} (trace : sourceArena.Trace state),
    ∃ path : SourcePath, (⟨state, trace⟩ : sourceArena.History) = path.history
  | _, .start => ⟨.root, by
      simp only [SourcePath.history, SourcePath.trace, SourcePath.state]
      rfl⟩
  | _, .extend (source := before) earlier joint legal supported => by
      obtain ⟨path, same⟩ := source_history_complete earlier
      have complete (history : sourceArena.History)
          (represented : ∃ path : SourcePath, history = path.history)
          (joint : ∀ player, Option (sourceArena.Action player))
          (legal : sourceArena.Legal history.state joint) (target : sourceArena.State)
          (supported : target ∈ (sourceArena.step history.state ⟨joint, legal⟩).support) :
          ∃ next : SourcePath, history.extend legal supported = next.history := by
        obtain ⟨path, rfl⟩ := represented
        exact path.step_complete joint legal target supported
      exact complete ⟨before, earlier⟩ ⟨path, same⟩ joint legal _ supported

def sourceInfoRemaining {who : Bool} : sourceModel.InfoState who → Nat
  | none => 5
  | some (.inl _) => 4
  | some (.inr (.inl _)) => 3
  | some (.inr (.inr (.inl _))) => 2
  | some (.inr (.inr (.inr (.inl _)))) => 1
  | some (.inr (.inr (.inr (.inr _)))) => 0

theorem source_info_remaining (who : Bool) (history : sourceArena.History) :
    sourceInfoRemaining (sourceModel.infoOf who history.trace) =
      sourceSetup.protocolRemaining history.state := by
  obtain ⟨path, same⟩ := source_history_complete history.trace
  change history = path.history at same
  subst history
  cases path <;> simp only [SourcePath.history, SourcePath.trace]
  all_goals rfl

theorem sourceAntichain : sourceModel.DecisionInformationAntichain := by
  intro who site first second joint legal target supported fuel reaches
  have one := sourceSetup.protocol_history_length sourceAdmission first.1.trace
  have two := sourceSetup.protocol_history_length sourceAdmission second.1.trace
  have same : sourceSetup.protocolRemaining first.1.state =
      sourceSetup.protocolRemaining second.1.state := by
    rw [← source_info_remaining who, ← source_info_remaining who, first.2, second.2]
  have grows := reaches.trace_length_le
  change first.1.trace.length + 1 ≤ second.1.trace.length at grows
  omega

end VegasTests.SequentialValidation
