/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Expr.Simple
import Vegas.Game.SourcePhaseGame
import Vegas.Game.CompiledRuntimePhases
import Vegas.Game.RecoveryInitialCheckpoint
import Vegas.Game.RevealService
import Interaction.ReactiveProtocol
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Source-ordered omission information before a concurrent native callback

The earlier source owner omits according to its private bit. The later source
owner observes that omission before its first commitment. An actual initialized
maximal-phase execution can activate the later owner before the earlier owner
has acted, with identical callback information for both bits. Thus these two
families of reached inputs admit no common information decoder. This is an
obstruction to matching all interleavings in that way, not a Nash impossibility
or a claim about a scheduler satisfying a complete service contract.
-/

noncomputable section

namespace Vegas.Examples.SourcePhaseInformation

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

inductive Player where
  | early
  | late
  deriving DecidableEq, Fintype

open Player

def context : SourceCtx Player simpleExpr := [(0, .privateInput early .bool)]

private def guard {Γ : SourceCtx Player simpleExpr} (who : Player) (name : VarId) :
    SourceGuard simpleExpr Γ who name .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by simp
  code := .constBool true
  reads := fun cell => nomatch cell

def suffix : SourceProgram Player simpleExpr ((1, .commitment early .bool) :: context) {1} :=
  .commit 2 late (by decide) (guard late 2) <|
  .reveal 3 early 1 (by decide) (.there .here) (by decide) <|
  .reveal 4 late 2 (by decide) (.there .here) (by decide) <|
  .ret []

def program : SourceProgram Player simpleExpr context ∅ :=
  .commit 1 early (by decide) (guard early 1) suffix

def sourceInitial (bit : Bool) : State simpleExpr context :=
  Env.cons bit (Env.empty _)

def setup : Setup (Player := Player) (L := simpleExpr) where
  context := context
  namesNodup := by decide
  initialLaw := (PMF.uniformOfFintype Bool).map sourceInitial
  obligations := ∅
  program := program
  accounts := rfl
  exitTransfers := fun _ => 0

private def sourceEntry (bit : Bool) : CommitRecoveryState program :=
  .atPoint (ProtocolState.entry program (setup.initialConfig (sourceInitial bit))) ∅ 0

private def earlyMove (bit : Bool) : CommitRecoveryMove Player simpleExpr :=
  ⟨.commit early 1 .bool (if bit then .success false else .failure), !bit⟩

private def sourceJoint (bit : Bool) : Player → Option (CommitRecoveryMove Player simpleExpr)
  | early => some (earlyMove bit)
  | late => none

private def sourceResult (bit : Bool) : ProtocolState program × Finset Player :=
  (Sum.inr (ProtocolState.entry suffix (commitSuccessor 1 (guard early 1)
    (setup.initialConfig (sourceInitial bit))
      (if bit then .success false else .failure))), if bit then ∅ else {early})

private def sourceAfter (bit : Bool) : CommitRecoveryState program :=
  ((sourceEntry bit).install (sourceResult bit) (Finset.empty_subset _)).close

private theorem source_after_excluded (bit : Bool) :
    (sourceAfter bit).excluded = if bit then ∅ else {early} := by
  exact CommitRecoveryState.close_excluded _

private theorem source_after_actor (bit : Bool) :
    ProtocolState.actor program (sourceAfter bit).point = some late := by
  have unfinished : ¬ ((sourceEntry bit).install (sourceResult bit)
      (Finset.empty_subset _)).Finished := by
    change ¬ (true = true ∧ 3 = 2)
    decide
  have committing : ProtocolState.atCommit program ((sourceEntry bit).install (sourceResult bit)
      (Finset.empty_subset _)).saved = true := rfl
  simp only [sourceAfter, CommitRecoveryState.close, unfinished, ite_false, committing, ite_true]
  rfl

private theorem source_draw_legal : setup.commitRecoveryProtocol.Legal none (fun _ => none) :=
  ⟨fun impossible => impossible, fun _ impossible => impossible⟩

private theorem source_draw_supported (bit : Bool) : some (sourceEntry bit) ∈
    (setup.commitRecoveryProtocol.step none ⟨fun _ => none, source_draw_legal⟩).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨sourceInitial bit, ?_, rfl⟩
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨bit, PMF.mem_support_uniformOfFintype bit, rfl⟩

private theorem source_move_legal (bit : Bool) :
    setup.commitRecoveryProtocol.Legal (some (sourceEntry bit)) (sourceJoint bit) := by
  refine ⟨fun impossible => impossible, ?_⟩
  intro who
  cases who with
  | late => exact fun impossible => Player.noConfusion (Option.some.inj impossible.1)
  | early =>
    refine ⟨⟨rfl, Finset.notMem_empty _⟩, ?_⟩
    refine ⟨⟨_, ?_, rfl⟩, ?_⟩
    · cases bit <;> trivial
    · change (earlyMove bit).missing = true → (earlyMove bit).action.IsFailure
      cases bit <;> simp [earlyMove, OwnAction.IsFailure]

private theorem source_move_supported (bit : Bool) : some (sourceAfter bit) ∈
    (setup.commitRecoveryProtocol.step (some (sourceEntry bit))
      ⟨sourceJoint bit, source_move_legal bit⟩).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨sourceAfter bit, ?_, rfl⟩
  change sourceAfter bit ∈ ((sourceEntry bit).step (sourceJoint bit)).support
  let law := ProtocolState.recoveryStep program (sourceEntry bit).point
    (sourceEntry bit).excluded (sourceJoint bit)
  let monotone := fun result supported => ProtocolState.recoveryStep_excluded_monotone program
    (sourceEntry bit).point (sourceEntry bit).excluded (sourceJoint bit) result supported
  have raw : sourceResult bit ∈ law.support := by
    cases bit <;> simp [law, sourceEntry, CommitRecoveryState.atPoint,
      ProtocolState.recoveryStep, ProtocolState.entry, program, sourceJoint, earlyMove,
      CommitRecoveryMove.missed, sourceResult]
  have lifted : sourceResult bit ∈ ((pmfToSubtype law monotone).map Subtype.val).support := by
    rw [map_val_pmfToSubtype]
    exact raw
  obtain ⟨result, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp lifted
  have aligned : result = ⟨sourceResult bit, Finset.empty_subset _⟩ := Subtype.ext same
  change sourceAfter bit ∈ ((pmfToSubtype law monotone).map _).support
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, by rw [aligned]; rfl⟩

def sourceTrace (bit : Bool) : setup.commitRecoveryProtocol.Trace (some (sourceAfter bit)) :=
  .extend (.extend .start (fun _ => none) source_draw_legal (source_draw_supported bit))
    (sourceJoint bit) (source_move_legal bit) (source_move_supported bit)

/-- Both reached source inputs are the later owner's first commitment in
generation zero; its public exclusion coordinate distinguishes the draws. -/
theorem source_information_ne : setup.commitRecoveryModel.infoOf late (sourceTrace true) ≠
    setup.commitRecoveryModel.infoOf late (sourceTrace false) := by
  intro same
  have excluded := congrArg (fun information : setup.commitRecoveryModel.InfoState late =>
    information.1.1.2.1) same
  change (sourceAfter true).excluded = (sourceAfter false).excluded at excluded
  rw [source_after_excluded, source_after_excluded] at excluded
  change (∅ : Finset Player) = {early} at excluded
  have impossible : early ∈ (∅ : Finset Player) := by
    rw [excluded]
    exact Finset.mem_singleton_self _
  exact Finset.notMem_empty early impossible

theorem source_late_active (bit : Bool) :
    setup.commitRecoveryProtocol.active (some (sourceAfter bit)) late := by
  refine ⟨source_after_actor bit, ?_⟩
  rw [source_after_excluded]
  cases bit <;> simp

abbrev compiled := serviceGraph setup .concurrent
abbrev runtime := serviceRuntime setup .concurrent (fun _ => 10)
abbrev plan := compiledRuntimePhasePlan program .concurrent

def leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket compiled) :=
  fun _ _ => PMF.pure ∅

abbrev app := phaseApplication runtime leaks

def nativeInitial : PMF app.State :=
  setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)

def scheduler : app.Scheduler := fun _ _ => PMF.pure (.activate late)

private def nativeEntry (bit : Bool) : app.Control :=
  ⟨1, none, ReactiveApplication.Execution.initial app
    (PhaseRuntimeState.initial plan (encodeInputs (sourceInitial bit)))⟩

private def callback (bit : Bool) : app.Control :=
  ⟨0, some late, { (nativeEntry bit).execution with
    environmentRecall := [⟨(nativeEntry bit).execution.observeEnvironment app, .activate late⟩] }⟩

private theorem native_draw_legal : (app.protocol nativeInitial 1 scheduler).Legal none
    (fun _ => none) := ⟨fun impossible => impossible, fun _ impossible => by cases impossible⟩

private theorem native_draw_supported (bit : Bool) : some (nativeEntry bit) ∈
    ((app.protocol nativeInitial 1 scheduler).step none
      ⟨fun _ => none, native_draw_legal⟩).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨_, ?_, rfl⟩
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨sourceInitial bit, ?_, rfl⟩
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨bit, PMF.mem_support_uniformOfFintype bit, rfl⟩

private theorem native_idle_legal (bit : Bool) : (app.protocol nativeInitial 1 scheduler).Legal
    (some (nativeEntry bit)) (fun _ => none) := by
  exact ⟨by change ¬ (1 = 0 ∧ none = none); simp, fun _ impossible => by cases impossible⟩

private theorem callback_supported (bit : Bool) : some (callback bit) ∈
    ((app.protocol nativeInitial 1 scheduler).step (some (nativeEntry bit))
      ⟨fun _ => none, native_idle_legal bit⟩).support := by
  change some (callback bit) ∈ (app.transition nativeInitial 1 scheduler
    (some (nativeEntry bit)) (fun _ => none)).support
  have observed (pending : List (Message Player (CommitAttemptPacket compiled))) :
      app.observePending late pending = PMF.pure ∅ := rfl
  simp only [ReactiveApplication.transition, nativeEntry, scheduler, PMF.pure_bind,
    ReactiveApplication.Execution.environmentStep, observed, PMF.pure_map,
    MessageNetwork.learn_empty, PMF.mem_support_pure_iff]
  rfl

def nativeTrace (bit : Bool) : (app.protocol nativeInitial 1 scheduler).Trace
    (some (callback bit)) :=
  .extend (.extend .start (fun _ => none) native_draw_legal (native_draw_supported bit))
    (fun _ => none) (native_idle_legal bit) (callback_supported bit)

private theorem initial_public_eq :
    (State.initial (graph := compiled) (encodeInputs (sourceInitial true))).publicView =
      (State.initial (graph := compiled) (encodeInputs (sourceInitial false))).publicView := by
  unfold State.publicView
  congr 1
  apply EventGraph.publicObserve_congr
  · rfl
  · intro field publicField
    cases field with
    | inl input =>
      fin_cases input
      change False at publicField
      exact publicField.elim
    | inr event => rfl

private theorem initial_player_eq :
    (State.initial (graph := compiled) (encodeInputs (sourceInitial true))).playerView late =
      (State.initial (graph := compiled) (encodeInputs (sourceInitial false))).playerView late := by
  unfold State.playerView
  rw [initial_public_eq]
  congr 1
  · apply EventGraph.playerObserve_congr
    · rfl
    · intro field visible
      cases field with
      | inl input =>
        fin_cases input
        change early = late at visible
        cases visible
      | inr event => rfl
  · funext slot
    rw [State.initial_candidate, State.initial_candidate]
    cases slot with
    | initial input => fin_cases input; rfl
    | prepared serial => rfl

/-- The actual reached first native callback contains no information about
the earlier owner's private bit, before that owner has acted. -/
theorem native_information_eq :
    (app.information nativeInitial 1 scheduler).infoOf late (nativeTrace true) =
      (app.information nativeInitial 1 scheduler).infoOf late (nativeTrace false) := by
  change (app.signals nativeInitial 1 scheduler).infoOf late (nativeTrace true) =
    (app.signals nativeInitial 1 scheduler).infoOf late (nativeTrace false)
  rw [app.info, app.info]
  change some ([], _) = some ([], _)
  congr 2
  unfold ReactiveApplication.Execution.observe
  congr 1
  change (PhaseRuntimeState.initial plan (encodeInputs (sourceInitial true))).playerView late =
    (PhaseRuntimeState.initial plan (encodeInputs (sourceInitial false))).playerView late
  rw [phaseInitial_eq_raw, phaseInitial_eq_raw]
  change (_, _) = (_, _)
  congr 1
  · exact initial_player_eq
  · unfold PhaseRuntimeState.publicView
    rw [initial_public_eq]
    rfl

/-- These two actual source/native input families cannot be related by one
player-local information decoder. No service-validity or Nash claim is made. -/
theorem no_source_information_decoder :
    ¬ ∃ decode : (app.information nativeInitial 1 scheduler).InfoState late →
        setup.commitRecoveryModel.InfoState late,
      ∀ bit, decode ((app.information nativeInitial 1 scheduler).infoOf late (nativeTrace bit)) =
        setup.commitRecoveryModel.infoOf late (sourceTrace bit) := by
  rintro ⟨decode, correct⟩
  exact source_information_ne ((correct true).symm.trans
    ((congrArg decode native_information_eq).trans (correct false)))

end Vegas.Examples.SourcePhaseInformation
