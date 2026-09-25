/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingGame
import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion
import GameTheoryExtensions.Protocol.StateKernel
import Mathlib.Tactic.DeriveFintype

/-! # Complete histories of the actual two-reveal source protocol -/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

abbrev sourceArena := sourceSetup.executionProtocol sourceAdmission
abbrev sourceModel := sourceSetup.informationModel sourceAdmission

def startConfig (bit : Bool) := sourceSetup.initialConfig (initialState bit)
def guessConfig (bit guess : Bool) :=
  revealSuccessor 2 (.there .here) (startConfig bit) guess
def finalConfig (bit guess disclose : Bool) :=
  revealSuccessor 3 (.there .here) (guessConfig bit guess) disclose

@[simp] theorem guess_publication (bit guess : Bool) :
    (guessConfig bit guess).state.get .here =
      if guess then .success true else .failure := by
  cases bit <;> cases guess <;> decide

@[simp] theorem secret_publication (bit guess disclose : Bool) :
    (finalConfig bit guess disclose).state.get .here =
      if disclose then .success bit else .failure := by
  cases bit <;> cases guess <;> cases disclose <;> decide

theorem sourceSingle (state : sourceArena.State) {first second : Player}
    (one : sourceArena.active state first) (two : sourceArena.active state second) :
    first = second := sourceSetup.protocol_singleMover sourceAdmission state one two

inductive SourcePath where
  | root
  | drawn (bit : Bool)
  | guessed (bit guess : Bool)
  | done (bit guess disclose : Bool)
  deriving DecidableEq, Fintype

def SourcePath.state : SourcePath → sourceSetup.ProtocolState
  | .root => none
  | .drawn bit => some (.inl (startConfig bit))
  | .guessed bit guess => some (.inr (.inl (guessConfig bit guess)))
  | .done bit guess disclose => some (.inr (.inr (finalConfig bit guess disclose)))

def sourceJoint (who : Player) (action : OwnAction Player simpleExpr) :
    ∀ player, Option (sourceArena.Action player) :=
  fun player => if player = who then some action else none

theorem source_draw_legal : sourceArena.Legal SourcePath.root.state (fun _ => none) :=
  ⟨id, fun _ => id⟩

theorem source_guess_legal (bit guess : Bool) :
    sourceArena.Legal (SourcePath.drawn bit).state
      (sourceJoint bob (.reveal bob 1 guess)) := by
  refine ⟨id, ?_⟩
  intro who
  fin_cases who <;> simp [sourceArena, Setup.executionProtocol, Setup.protocolObserve,
    SourcePath.state, sourceJoint, ProtocolState.observe, ProtocolView.actor,
    ProtocolView.available, sourceSetup, sourceProgram, alice, bob, watcher]

theorem source_opening_legal (bit guess disclose : Bool) :
    sourceArena.Legal (SourcePath.guessed bit guess).state
      (sourceJoint alice (.reveal alice 0 disclose)) := by
  refine ⟨id, ?_⟩
  intro who
  fin_cases who <;> simp [sourceArena, Setup.executionProtocol, Setup.protocolObserve,
    SourcePath.state, sourceJoint, ProtocolState.observe, ProtocolView.actor,
    ProtocolView.available, sourceSetup, sourceProgram, alice, bob, watcher]

theorem source_guess_step (bit guess : Bool) :
    sourceArena.step (SourcePath.drawn bit).state ⟨_, source_guess_legal bit guess⟩ =
      FinDist.pure (SourcePath.guessed bit guess).state := by
  simp [sourceArena, Setup.executionProtocol, Setup.protocolStep, SourcePath.state,
    sourceSetup, sourceProgram, ProtocolState.step, sourceJoint, guessConfig,
    OwnAction.disclosure, ProtocolState.entry]

theorem source_opening_step (bit guess disclose : Bool) :
    sourceArena.step (SourcePath.guessed bit guess).state
      ⟨_, source_opening_legal bit guess disclose⟩ =
      FinDist.pure (SourcePath.done bit guess disclose).state := by
  simp [sourceArena, Setup.executionProtocol, Setup.protocolStep, SourcePath.state,
    sourceSetup, sourceProgram, ProtocolState.step, sourceJoint, finalConfig,
    OwnAction.disclosure, ProtocolState.entry]

def SourcePath.depth : SourcePath → Nat
  | .root => 0
  | .drawn _ => 1
  | .guessed .. => 2
  | .done .. => 3

def SourcePath.trace : (path : SourcePath) → sourceArena.Trace path.state
  | .root => .start
  | .drawn bit => Trace.extend .start (fun _ => none) source_draw_legal (by
      change (SourcePath.drawn bit).state ∈ (sourceSetup.initialLaw.map _).support
      rw [FinDist.support_map]
      refine ⟨initialState bit, ?_, rfl⟩
      rw [show sourceSetup.initialLaw = (FinDist.uniformOfFintype (α := Bool)).map initialState
        from rfl, FinDist.support_map]
      exact ⟨bit, FinDist.mem_support_uniformOfFintype bit, rfl⟩)
  | .guessed bit guess => Trace.extend (SourcePath.drawn bit).trace _
      (source_guess_legal bit guess)
      (by rw [source_guess_step]; exact FinDist.mem_support_pure.mpr rfl)
  | .done bit guess disclose => Trace.extend (SourcePath.guessed bit guess).trace _
      (source_opening_legal bit guess disclose)
      (by rw [source_opening_step]; exact FinDist.mem_support_pure.mpr rfl)
termination_by path => path.depth
decreasing_by all_goals simp [depth]

def SourcePath.history (path : SourcePath) : sourceArena.History := ⟨path.state, path.trace⟩

@[simp] theorem SourcePath.history_state (path : SourcePath) :
    path.history.state = path.state := rfl

theorem source_active_joint {state : sourceArena.State}
    (joint : ∀ player, Option (sourceArena.Action player)) (legal : sourceArena.Legal state joint)
    (who : Player) (active : sourceArena.active state who) :
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
      obtain ⟨action, same, available⟩ := source_active_joint joint legal bob rfl
      change ∃ guess : Bool, action = .reveal bob 1 guess at available
      obtain ⟨guess, rfl⟩ := available
      subst joint
      change target ∈ (sourceArena.step (drawn bit).state ⟨_, legal⟩).support at supported
      rw [source_guess_step] at supported
      cases FinDist.mem_support_pure.mp supported
      refine ⟨.guessed bit guess, ?_⟩
      simp only [history, trace, History.extend]
  | guessed bit guess =>
      obtain ⟨action, same, available⟩ := source_active_joint joint legal alice rfl
      change ∃ disclose : Bool, action = .reveal alice 0 disclose at available
      obtain ⟨disclose, rfl⟩ := available
      subst joint
      change target ∈ (sourceArena.step (guessed bit guess).state ⟨_, legal⟩).support at supported
      rw [source_opening_step] at supported
      cases FinDist.mem_support_pure.mp supported
      refine ⟨.done bit guess disclose, ?_⟩
      simp only [history, trace, History.extend]
  | done bit guess disclose => exact (legal.1 trivial).elim

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

instance : Finite sourceArena.History :=
  Finite.of_surjective SourcePath.history (fun history => by
    obtain ⟨path, same⟩ := source_history_complete history.trace
    exact ⟨path, same.symm⟩)

instance : Fintype sourceArena.History := Fintype.ofFinite _
instance (who : Player) (site : sourceModel.InformationSite who) :
    Fintype (sourceModel.InformationHistory who site.1) := by classical infer_instance

def sourceInfoRemaining {who : Player} : sourceModel.InfoState who → Nat
  | none => 3
  | some (.inl _) => 2
  | some (.inr (.inl _)) => 1
  | some (.inr (.inr _)) => 0

theorem source_info_remaining (who : Player) (history : sourceArena.History) :
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

theorem source_info (who : Player) (history : sourceArena.History) :
    sourceModel.infoOf who history.trace = sourceSetup.protocolObserve who history.state :=
  sourceSetup.protocol_info sourceAdmission who history.trace

def decodeSource : sourceArena.State → SourcePath
  | none => .root
  | some (.inl config) => .drawn ((config.state.get .here).getD false)
  | some (.inr (.inl config)) =>
      .guessed ((config.state.get (.there .here)).getD false)
        (OwnAction.disclosure (config.history bob)[0]?)
  | some (.inr (.inr config)) =>
      .done ((config.state.get (.there (.there .here))).getD false)
        (OwnAction.disclosure (config.history bob)[0]?)
        (OwnAction.disclosure (config.history alice)[0]?)

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

end VegasTests.MonitoredGuessing
