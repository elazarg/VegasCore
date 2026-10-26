/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseSurvivingSourceView
import Vegas.Game.SourcePhaseCursor
import Vegas.Game.SourcePhaseRevealCursor
import Vegas.Game.PhaseObservableSourceQuery
import Vegas.Game.CompiledRuntimePhases
import Vegas.Game.PhaseSourcePolicy
import Interaction.ReactiveMenuPolicy
import Vegas.Game.PhaseRecoveryBindingComponent
import Vegas.Pending.PhaseBindingPolicy
import Vegas.Pending.PhaseOpeningPolicy
import Vegas.Pending.PhaseOncePolicy
import Vegas.Game.CommitRecoveryGlobalWordDensity
import Vegas.Source.CommitRecoveryInitialInputs
import Vegas.Source.CommitRecoveryPublicScan
import Vegas.Game.CommitRecoveryAncillaryBelief

/-! # Full surviving source information for physical phase clients

The decoder uses the player's complete typed source view and the actual numeric
public source chronology. Equality of these observable records determines every
original private signal and own-play tag while the observer survives. Retired
choices are retained; no erased or no-miss source policy is substituted.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem initialized_prefix {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    match state with
    | none => trace.length = 0
    | some _ => ∃ inputs : State L setup.context,
        ∃ prior : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
          (ProtocolState.entry setup.program (setup.initialConfig inputs)) ∅ 0)),
          prior.length = 1 ∧ TracePrefix prior trace := by
  induction trace with
  | start => rfl
  | @extend source target earlier joint legal reached ih =>
      cases source with
      | none =>
          obtain ⟨inputs, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          refine ⟨inputs, earlier.extend joint legal reached, ?_, .refl⟩
          change earlier.length + 1 = 1
          rw [ih]
      | some before =>
          obtain ⟨next, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          obtain ⟨inputs, prior, length, retained⟩ := ih
          exact ⟨inputs, prior, length, retained.extend joint legal reached⟩

private theorem initialized_information_eq (who : Player)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (left : setup.commitRecoveryProtocol.Trace leftState)
    (right : setup.commitRecoveryProtocol.Trace rightState)
    (leftLength : left.length = 1) (rightLength : right.length = 1)
    (views : setup.commitRecoveryPrivate who leftState =
      setup.commitRecoveryPrivate who rightState)
    (controls : setup.commitRecoveryPublic leftState = setup.commitRecoveryPublic rightState) :
    setup.commitRecoveryModel.infoOf who left = setup.commitRecoveryModel.infoOf who right := by
  cases left with
  | start => cases leftLength
  | extend leftPrior leftJoint leftLegal leftSupport =>
      cases leftPrior with
      | extend prior joint legal supported => simp only [Trace.length] at leftLength; omega
      | start =>
          cases right with
          | start => cases rightLength
          | extend rightPrior rightJoint rightLegal rightSupport =>
              cases rightPrior with
              | extend prior joint legal supported =>
                  simp only [Trace.length] at rightLength
                  omega
              | start =>
                  have choices (joint : Player → Option (CommitRecoveryMove Player L))
                      (legal : setup.commitRecoveryProtocol.Legal none joint) :
                      joint who = none := by
                    cases selected : joint who with
                    | none => rfl
                    | some move =>
                        have offered := legal.2 who
                        rw [selected] at offered
                        exact offered.1.elim
                  simp only [commitRecoveryModel, InfoSignals.withOwnPlayRecall_infoOf]
                  simp only [InfoSignals.infoOf_extend, InfoSignals.ownPlay_extend,
                    choices _ leftLegal, choices _ rightLegal, InfoSignals.infoOf_start]
                  exact Prod.ext (Prod.ext (Prod.ext views controls) rfl) rfl

/-- Literal current source observations and numeric public chronology determine
all original information at surviving histories, including voided own choices. -/
theorem commitRecovery_information_eq_of_view_and_addresses (who : Player)
    (first second : CommitRecoveryState setup.program)
    (left : setup.commitRecoveryProtocol.Trace (some first))
    (right : setup.commitRecoveryProtocol.Trace (some second))
    (leftSurvives : who ∉ first.excluded) (rightSurvives : who ∉ second.excluded)
    (views : ProtocolState.observe who setup.program first.point =
      ProtocolState.observe who setup.program second.point)
    (addresses : setup.recoveryAddressWord left = setup.recoveryAddressWord right) :
    setup.commitRecoveryModel.infoOf who left = setup.commitRecoveryModel.infoOf who right := by
  have publicWord : setup.attemptPublicRecall who left = setup.attemptPublicRecall who right := by
    apply setup.commitRecovery_publicRecall_eq_of_numeric who first second left right
      leftSurvives rightSurvives
    · rw [← ProtocolView.publicPadding_observe, ← ProtocolView.publicPadding_observe, views]
    · rw [setup.commitRecovery_publicRecall_addresses,
        setup.commitRecovery_publicRecall_addresses, addresses]
  obtain ⟨leftInput, leftPrior, leftLength, leftRetained⟩ := setup.initialized_prefix left
  obtain ⟨rightInput, rightPrior, rightLength, rightRetained⟩ := setup.initialized_prefix right
  have original := ProtocolState.sourceObserve_base_eq_of_observe_eq who setup.program
    first.point second.point views
  obtain ⟨_, sameLeft, leftBase, _⟩ := setup.commitRecovery_base_of_prefix _ leftPrior rfl
    left leftRetained
  obtain ⟨_, sameRight, rightBase, _⟩ := setup.commitRecovery_base_of_prefix _ rightPrior rfl
    right rightRetained
  cases Option.some.inj sameLeft
  cases Option.some.inj sameRight
  simp only [CommitRecoveryState.atPoint, ProtocolState.base_entry,
    initialConfig] at leftBase rightBase
  rw [leftBase, rightBase] at original
  have entries := ProtocolState.observe_entry_congr who setup.program
    (setup.initialConfig leftInput) (setup.initialConfig rightInput) (Prod.ext original rfl)
  have initialInfo := setup.initialized_information_eq who leftPrior rightPrior
    leftLength rightLength (congrArg some entries) (by
      simp only [commitRecoveryPublic, CommitRecoveryState.atPoint,
        ProtocolState.remaining_entry])
  have initialCoordinate :
      (setup.recoveryJointRecall leftPrior).map (fun joint => joint who) =
        (setup.recoveryJointRecall rightPrior).map (fun joint => joint who) :=
    setup.commitRecovery_coordinate_eq_of_info_eq who leftPrior rightPrior initialInfo
  have coordinate := setup.commitRecovery_coordinate_eq_of_public_and_own_history who _ _
    leftPrior rightPrior (leftLength.trans rightLength.symm) initialCoordinate left right
    leftRetained rightRetained publicWord leftSurvives rightSurvives
    (congrArg some (ProtocolState.history_eq_of_observe who setup.program _ _ views))
  apply setup.commitRecovery_info_eq_of_observed_prefixes who _ _ leftPrior rightPrior
    (leftLength.trans rightLength.symm) _ initialInfo left right leftRetained rightRetained
    publicWord coordinate
  exact Prod.ext entries (Prod.ext entries rfl)

/-- A candidate is a genuine surviving initialized source history with exactly
these local records. No hidden source state is selected by the physical player. -/
def sourceInformationCandidates (who : Player)
    (view : SourceProgram.ProtocolView who setup.program)
    (addresses : List (Option Nat × (Finset Player × Nat × Nat))) :
    Set setup.commitRecoveryProtocol.History :=
  {history | ∃ current, history.state = some current ∧ who ∉ current.excluded ∧
    ProtocolState.observe who setup.program current.point = view ∧
      setup.recoveryAddressWord history.trace = addresses}

/-- Every candidate gives the same full source information. This is the
justification for the representative decoder, before any policy is queried. -/
theorem sourceInformationCandidates_constant (who : Player)
    (view : SourceProgram.ProtocolView who setup.program)
    (addresses : List (Option Nat × (Finset Player × Nat × Nat)))
    (left right : setup.commitRecoveryProtocol.History)
    (leftMember : left ∈ setup.sourceInformationCandidates who view addresses)
    (rightMember : right ∈ setup.sourceInformationCandidates who view addresses) :
    setup.commitRecoveryModel.infoOf who left.trace =
      setup.commitRecoveryModel.infoOf who right.trace := by
  obtain ⟨first, firstState, firstSurvives, firstView, firstAddresses⟩ := leftMember
  obtain ⟨second, secondState, secondSurvives, secondView, secondAddresses⟩ := rightMember
  rcases left with ⟨leftState, leftTrace⟩
  rcases right with ⟨rightState, rightTrace⟩
  dsimp only at firstState secondState
  subst leftState
  subst rightState
  exact setup.commitRecovery_information_eq_of_view_and_addresses who first second
    leftTrace rightTrace firstSurvives secondSurvives (firstView.trans secondView.symm)
    (firstAddresses.trans secondAddresses.symm)

open Classical in
/-- Read full original information from complete local source records. An
unrealized record has no source information; realized fibers are constant. -/
def sourceInformation? (who : Player)
    (view : SourceProgram.ProtocolView who setup.program)
    (addresses : List (Option Nat × (Finset Player × Nat × Nat))) :
    Option (setup.commitRecoveryModel.InfoState who) :=
  if existsCandidate : (setup.sourceInformationCandidates who view addresses).Nonempty then
    some (setup.commitRecoveryModel.infoOf who existsCandidate.choose.trace)
  else none

/-- The local representative reads the literal information of every genuine
surviving source history with those records, rather than an erased policy key. -/
theorem sourceInformation?_of_history (who : Player)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (survives : who ∉ current.excluded) :
    setup.sourceInformation? who (ProtocolState.observe who setup.program current.point)
        (setup.recoveryAddressWord trace) = some (setup.commitRecoveryModel.infoOf who trace) := by
  classical
  have existsCandidate : (setup.sourceInformationCandidates who
      (ProtocolState.observe who setup.program current.point)
      (setup.recoveryAddressWord trace)).Nonempty :=
    ⟨⟨some current, trace⟩, current, rfl, survives, rfl, rfl⟩
  unfold sourceInformation?
  rw [dite_eq_left existsCandidate]
  exact congrArg some (setup.sourceInformationCandidates_constant who _ _
    existsCandidate.choose ⟨some current, trace⟩ existsCandidate.choose_spec
      ⟨current, rfl, survives, rfl, rfl⟩)

/-- Query one original observation-local source policy at the full reconstructed
information. Only an unrealized key is completed by silence. -/
def sourcePhaseChoiceLaw (who : Player)
    (policy : setup.commitRecoveryModel.BehavioralPolicy who)
    (view : SourceProgram.ProtocolView who setup.program)
    (addresses : List (Option Nat × (Finset Player × Nat × Nat))) :
    PMF (Option (CommitRecoveryMove Player L)) :=
  match setup.sourceInformation? who view addresses with
  | none => PMF.pure none
  | some info => (policy info).map Subtype.val

theorem sourcePhaseChoiceLaw_of_history (who : Player)
    (policy : setup.commitRecoveryModel.BehavioralPolicy who)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (survives : who ∉ current.excluded) :
    setup.sourcePhaseChoiceLaw who policy (ProtocolState.observe who setup.program current.point)
        (setup.recoveryAddressWord trace) =
      (policy (setup.commitRecoveryModel.infoOf who trace)).map Subtype.val := by
  unfold sourcePhaseChoiceLaw
  rw [setup.sourceInformation?_of_history who current trace survives]

end Vegas.SourceProgram.Setup



namespace Vegas.SourcePhaseClient

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (serviceGraph setup .sequential))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket (serviceGraph setup .sequential)))
  (bounds : MessageBounds (serviceGraph setup .sequential))

local notation "app" => phaseApplication runtime leaks

/-- Encode one queried source move using the original guarded physical binding
and opening encoders. A source omission emits silence. Malformed observations
are completed by legal silence without changing either source or runtime menus. -/
def moveResponse (who : Player) (event : (serviceGraph setup .sequential).EventId)
    (move : Option (CommitRecoveryMove Player L)) : (app).Policy := fun past view =>
  match nodeView (serviceGraph setup .sequential) event with
  | .bind owner payload outputEq _ =>
      if same : owner = who then
        if move.elim false (·.missing) then PMF.pure ⟨none⟩ else
          PhaseCount.phaseBindingPolicy runtime leaks bounds who event payload
            (fun _ _ => PMF.pure (phaseRecoveryBindingData setup .sequential event who payload
              (by simpa only [same] using outputEq) move).1) past view
      else PMF.pure ⟨none⟩
  | .resolve owner payload binding _ _ _ =>
      if same : owner = who then
        PhaseCount.phaseOpeningPolicy runtime leaks bounds who event payload
          (same ▸ binding)
          (fun _ _ => PMF.pure (OwnAction.disclosure (move.map (·.action)))) past view
      else PMF.pure ⟨none⟩
  | .sample .. => PMF.pure ⟨none⟩

/-- The actual encoders are one-packet legal for every input and every proposed
move. No source-history or semantic-correspondence premise establishes legality. -/
theorem moveResponse_covered (who : Player)
    (event : (serviceGraph setup .sequential).EventId)
    (move : Option (CommitRecoveryMove Player L))
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈ (moveResponse setup runtime leaks bounds who event move
      past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  classical
  cases node : nodeView (serviceGraph setup .sequential) event with
  | bind owner payload outputEq codeEq =>
      simp only [moveResponse, node] at supported
      split at supported
      · split at supported
        · cases (PMF.mem_support_pure_iff _ _).mp supported
          exact PhaseCount.silence_onePacket runtime leaks bounds who past view
        · exact PhaseCount.phaseBindingPolicy_covered runtime leaks bounds who event payload
            _ past view response supported
      · cases (PMF.mem_support_pure_iff _ _).mp supported
        exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [moveResponse, node] at supported
      split at supported
      · exact PhaseCount.phaseOpeningPolicy_covered runtime leaks bounds who event payload _
          _ past view response supported
      · cases (PMF.mem_support_pure_iff _ _).mp supported
        exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  | sample payload law outputEq codeEq =>
      simp only [moveResponse, node] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact PhaseCount.silence_onePacket runtime leaks bounds who past view

/-- The source uses its maximal commitment partition, including actual retries. -/
abbrev plan := compiledRuntimePhasePlan setup.program .sequential

/-- Physical first-opportunity clients begin from the unchanged source prior. -/
def initial : PMF (app).State :=
  setup.initialLaw.map fun inputs => PhaseRuntimeState.initial (plan setup) (encodeInputs inputs)

/-- Read the current prefix through public failure owners. Bindings preserve
the maximal entry checkpoint; each completed reveal saves its own source rank. -/
def currentAddresses (event : (serviceGraph setup .sequential).EventId)
    (view : PhasePublicView (serviceGraph setup .sequential)) :
    List (Option Nat × (Finset Player × Nat × Nat)) :=
  let low := view.attempt.phase
  let inherited := (view.retired.map fun record => record.2.sourceFailureFootprint.2).foldr
    (fun owners rest => owners ∪ rest) ∅
  view.sourcePublicAddressWord (plan setup) low ++
    (List.range (event.val - low)).map fun index =>
      let rank := low + index + 1
      (some rank, inherited ∪ view.native.sourceFailureFootprint.1 rank,
        view.attempt.generation,
        if ((serviceGraph setup .sequential).outputLayout event).IsPublication then rank else low)

private theorem currentAddresses_read
    (state : PhaseRuntimeState (serviceGraph setup .sequential))
    (event : (serviceGraph setup .sequential).EventId) :
    currentAddresses setup event state.publicView =
      state.sourcePublicAddressWord (plan setup) state.attempt.phase ++
        (List.range (event.val - state.attempt.phase)).map (fun index =>
          let rank := state.attempt.phase + index + 1
          (some rank, PhaseRuntimeState.archivedFailureOwners state.retired ∪
            state.current.native.failureOwnersBefore rank, state.generation,
            if ((serviceGraph setup .sequential).outputLayout event).IsPublication then rank
              else state.attempt.phase)) := by
  have archives :
      ((state.retired.map fun record => (record.attempt, record.state.publicView)).map
        fun record => record.2.sourceFailureFootprint.2).foldr (fun a b => a ∪ b) ∅ =
        PhaseRuntimeState.archivedFailureOwners state.retired := by
    simp only [List.map_map, List.foldr_map, Function.comp_def, State.sourceFailureFootprint_read,
      State.sourceFailureFootprint, PhaseRuntimeState.archivedFailureOwners]
  dsimp only [currentAddresses]
  rw [PhaseRuntimeState.sourcePublicAddressWord_read (plan setup) state]
  simp only [PhaseRuntimeState.publicView, archives, State.sourceFailureFootprint_read,
    State.sourceFailureFootprint]
  rfl

theorem currentAddresses_binding_read
    (state : PhaseRuntimeState (serviceGraph setup .sequential))
    (event : (serviceGraph setup .sequential).EventId) (who : Player) (payload : L.Ty)
    (binding : (serviceGraph setup .sequential).outputLayout event = .binding who payload) :
    currentAddresses setup event state.publicView =
      state.sourceCurrentAddressWord (plan setup) event.val := by
  rw [currentAddresses_read]
  simp only [PhaseRuntimeState.sourceCurrentAddressWord, binding, EventField.IsPublication,
    ite_false]

theorem currentAddresses_reveal_read
    (state : PhaseRuntimeState (serviceGraph setup .sequential))
    (event : (serviceGraph setup .sequential).EventId) (payload : L.Ty)
    (publication : (serviceGraph setup .sequential).outputLayout event = .publication payload) :
    currentAddresses setup event state.publicView =
      state.sourceCurrentRevealAddressWord (plan setup) event.val := by
  rw [currentAddresses_read]
  simp only [PhaseRuntimeState.sourceCurrentRevealAddressWord, publication,
    EventField.IsPublication, ite_true]

/-- The complete source information is computed from the player's masked current
view and public source chronology. No hidden physical execution is an argument. -/
def information? (who : Player) (event : (serviceGraph setup .sequential).EventId)
    (view : (app).PlayerView) : Option (setup.commitRecoveryModel.InfoState who) :=
  (phaseSurvivingSourceView? setup .sequential runtime leaks who event view).bind fun typed =>
    setup.sourceInformation? who typed
      (currentAddresses setup event view.application.2)

def choiceLaw (who : Player) (policy : setup.commitRecoveryModel.BehavioralPolicy who)
    (event : (serviceGraph setup .sequential).EventId) (view : (app).PlayerView) :
    PMF (Option (CommitRecoveryMove Player L)) :=
  match information? setup runtime leaks who event view with
  | none => PMF.pure none
  | some info => (policy info).map Subtype.val

open Classical in
/-- Query the source policy only at the first callback of an actual attempt-event.
A silent omission is recorded just as a transmission is; repeat callbacks never
resample it. Every branch uses only the player's own recall and current view. -/
def policy (who : Player) (source : setup.commitRecoveryModel.BehavioralPolicy who) :
    (app).Policy := fun past view =>
  match requestedEvent setup .sequential who view.application.2 with
  | none => PMF.pure ⟨none⟩
  | some event =>
      if PhaseCount.ResponseRecorded runtime leaks who ⟨view.application.2.attempt, event⟩ past then
        PMF.pure ⟨none⟩
      else (choiceLaw setup runtime leaks who source event view).bind fun move =>
        moveResponse setup runtime leaks bounds who event move past view

theorem policy_covered (who : Player) (source : setup.commitRecoveryModel.BehavioralPolicy who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈ (policy setup runtime leaks bounds who source past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  classical
  unfold policy at supported
  split at supported
  · cases (PMF.mem_support_pure_iff _ _).mp supported
    exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  · split at supported
    · cases (PMF.mem_support_pure_iff _ _).mp supported
      exact PhaseCount.silence_onePacket runtime leaks bounds who past view
    · obtain ⟨move, _drawn, member⟩ := (PMF.mem_support_bind_iff ..).mp supported
      exact moveResponse_covered setup runtime leaks bounds who _ move past view response member

theorem policy_raw_covered (who : Player)
    (source : setup.commitRecoveryModel.BehavioralPolicy who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈ (policy setup runtime leaks bounds who source past view).support) :
    response ∈ (PhaseCount.rawMenu runtime leaks bounds).actions who past view :=
  ((PhaseCount.mem_onePacketActions runtime leaks bounds who past view response).mp
    (policy_covered setup runtime leaks bounds who source past view response supported)).1

/-- Each compiled strategy depends on exactly one source player's policy. -/
def compilePolicy (horizon : Nat) (scheduler : (app).Scheduler) (who : Player)
    (source : setup.commitRecoveryModel.BehavioralPolicy who) :
    ((PhaseCount.rawMenu runtime leaks bounds).information (initial setup runtime leaks)
      horizon scheduler).BehavioralPolicy who :=
  (PhaseCount.rawMenu runtime leaks bounds).restrictPolicy (initial setup runtime leaks)
    horizon scheduler who (policy setup runtime leaks bounds who source)

def compileProfile (horizon : Nat) (scheduler : (app).Scheduler)
    (source : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∀ who, ((PhaseCount.rawMenu runtime leaks bounds).information (initial setup runtime leaks)
      horizon scheduler).BehavioralPolicy who :=
  fun who => compilePolicy setup runtime leaks bounds horizon scheduler who (source who)

/-- A source unilateral replacement changes only its actual physical client. -/
theorem compileProfile_update (horizon : Nat) (scheduler : (app).Scheduler)
    (source : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (who : Player)
    (replacement : setup.commitRecoveryModel.BehavioralPolicy who) :
    compileProfile setup runtime leaks bounds horizon scheduler
        (Function.update source who replacement) =
      Function.update (compileProfile setup runtime leaks bounds horizon scheduler source) who
        (compilePolicy setup runtime leaks bounds horizon scheduler who replacement) := by
  funext owner
  by_cases same : owner = who
  · subst owner
    simp only [compileProfile, Function.update_self]
  · simp only [compileProfile, Function.update_of_ne same]

/-- Forgetting the finite raw-menu witness preserves the complete response law
at every local physical input, including unrealized and deviating inputs. -/
theorem compilePolicy_map_val (horizon : Nat) (scheduler : (app).Scheduler) (who : Player)
    (source : setup.commitRecoveryModel.BehavioralPolicy who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    ((compilePolicy setup runtime leaks bounds horizon scheduler who source)
      (some (past, view))).map Subtype.val =
      (policy setup runtime leaks bounds who source past view).map some :=
  (PhaseCount.rawMenu runtime leaks bounds).restrictPolicy_map_val
    (initial setup runtime leaks) horizon scheduler who _ past view
      (policy_raw_covered setup runtime leaks bounds who source past view)

theorem policy_first (who : Player) (source : setup.commitRecoveryModel.BehavioralPolicy who)
    (event : (serviceGraph setup .sequential).EventId)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (selected : requestedEvent setup .sequential who view.application.2 = some event)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks who
      ⟨view.application.2.attempt, event⟩ past)
    (info : setup.commitRecoveryModel.InfoState who)
    (read : information? setup runtime leaks who event view = some info) :
    policy setup runtime leaks bounds who source past view =
      (source info).bind fun choice =>
        moveResponse setup runtime leaks bounds who event choice.val past view := by
  simp only [policy, selected, ite_eq_right first, choiceLaw, read, PMF.bind_map]
  rfl

theorem policy_recorded (who : Player)
    (source : setup.commitRecoveryModel.BehavioralPolicy who)
    (event : (serviceGraph setup .sequential).EventId)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (selected : requestedEvent setup .sequential who view.application.2 = some event)
    (recorded : PhaseCount.ResponseRecorded runtime leaks who
      ⟨view.application.2.attempt, event⟩ past) :
    policy setup runtime leaks bounds who source past view = PMF.pure ⟨none⟩ := by
  simp only [policy, selected, ite_eq_left recorded]

/-- Every actual binding request reads a genuine full source decision, including
current omissions by earlier owners in this maximal attempt. No decoder or
source-information equality is supplied by the caller. -/
theorem information_binding_of_history (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (initial setup runtime leaks) horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup .sequential).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .sequential).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ (current : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some current)),
      current.excluded = control.execution.application.current.excluded ∧
      ProtocolState.actor setup.program current.point = some who ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryModel.infoOf who sourceTrace) ∧
      information? setup runtime leaks who event (control.execution.observe app who) =
        some (setup.commitRecoveryModel.infoOf who sourceTrace) := by
  obtain ⟨current, sourceTrace, excluded, _generation, _controls, actor, decision, decoded,
      addresses⟩ := phase_ready_binding_current_source setup runtime leaks (plan setup)
    (compiledRuntimePhasePlan_maximal setup.program .sequential) horizon scheduler trace who
    event payload binding request
  have survives : who ∉ current.excluded := by
    rw [excluded]
    exact request.2.2.2.2
  have numbers : currentAddresses setup event control.execution.application.publicView =
      setup.recoveryAddressWord sourceTrace :=
    by
      have localRead := currentAddresses_binding_read setup control.execution.application
        event who payload binding
      exact localRead.trans addresses.symm
  refine ⟨current, sourceTrace, excluded, actor, decision, ?_⟩
  unfold information?
  rw [decoded, Option.bind_some]
  change setup.sourceInformation? who (ProtocolState.observe who setup.program current.point)
    (currentAddresses setup event control.execution.application.publicView) = _
  rw [numbers]
  exact setup.sourceInformation?_of_history who current sourceTrace survives

/-- Every actual opening request reads full original source information. Earlier
failed foreign openings and all retired own words remain represented literally. -/
theorem information_reveal_of_history (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (initial setup runtime leaks) horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup .sequential).EventId) (payload : L.Ty)
    (publication : (serviceGraph setup .sequential).outputLayout event = .publication payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ (current : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some current)),
      current.excluded = control.execution.application.current.excluded ∧
      ProtocolState.actor setup.program current.point = some who ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryModel.infoOf who sourceTrace) ∧
      information? setup runtime leaks who event (control.execution.observe app who) =
        some (setup.commitRecoveryModel.infoOf who sourceTrace) := by
  obtain ⟨current, sourceTrace, excluded, _generation, _controls, actor, decision, decoded,
      addresses⟩ := phase_ready_reveal_current_source setup runtime leaks (plan setup)
    (compiledRuntimePhasePlan_maximal setup.program .sequential) horizon scheduler trace who
    event payload publication request
  have survives : who ∉ current.excluded := by
    rw [excluded]
    exact request.2.2.2.2
  have numbers : currentAddresses setup event control.execution.application.publicView =
      setup.recoveryAddressWord sourceTrace := by
    have localRead := currentAddresses_reveal_read setup control.execution.application
      event payload publication
    exact localRead.trans addresses.symm
  refine ⟨current, sourceTrace, excluded, actor, decision, ?_⟩
  unfold information?
  rw [decoded, Option.bind_some]
  change setup.sourceInformation? who (ProtocolState.observe who setup.program current.point)
    (currentAddresses setup event control.execution.application.publicView) = _
  rw [numbers]
  exact setup.sourceInformation?_of_history who current sourceTrace survives

/-- All actual requested strategic events have an exact local full-information
source query. This includes arbitrary raw predecessor histories. -/
theorem information_of_history (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (initial setup runtime leaks) horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup .sequential).EventId)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    ∃ (current : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some current)),
      current.excluded = control.execution.application.current.excluded ∧
      ProtocolState.actor setup.program current.point = some who ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryModel.infoOf who sourceTrace) ∧
      information? setup runtime leaks who event (control.execution.observe app who) =
        some (setup.commitRecoveryModel.infoOf who sourceTrace) := by
  cases node : nodeView (serviceGraph setup .sequential) event with
  | bind owner payload outputEq codeEq =>
      have same : owner = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans request.2.2.2.1)
      subst owner
      exact information_binding_of_history setup runtime leaks horizon scheduler trace who event
        payload outputEq request
  | resolve owner payload binding checks outputEq codeEq =>
      exact information_reveal_of_history setup runtime leaks horizon scheduler trace who event
        payload outputEq request
  | sample payload law outputEq codeEq =>
      have acting := request.2.2.2.1
      rw [nodeView_sample_actor outputEq codeEq] at acting
      cases acting

/-- At every actual first callback the client queries the unmodified source
policy at exact full source information, then uses the actual physical encoder.
This describes the response law; failed openings may have the same physical
encoding and are not asserted to retain an exited owner's private intent. -/
theorem policy_first_of_history (horizon : Nat) (scheduler : (app).Scheduler) {control}
    (trace : ((app).protocol (initial setup runtime leaks) horizon scheduler).Trace (some control))
    (who : Player) (source : setup.commitRecoveryModel.BehavioralPolicy who)
    (event : (serviceGraph setup .sequential).EventId)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks who
      ⟨control.execution.application.attempt, event⟩ (control.execution.recall who)) :
    ∃ (current : CommitRecoveryState setup.program)
      (sourceTrace : setup.commitRecoveryProtocol.Trace (some current)),
      current.excluded = control.execution.application.current.excluded ∧
      ProtocolState.actor setup.program current.point = some who ∧
      policy setup runtime leaks bounds who source (control.execution.recall who)
          (control.execution.observe app who) =
        (source (setup.commitRecoveryModel.infoOf who sourceTrace)).bind fun choice =>
          moveResponse setup runtime leaks bounds who event choice.val
            (control.execution.recall who) (control.execution.observe app who) := by
  obtain ⟨current, sourceTrace, excluded, actor, _decision, read⟩ :=
    information_of_history setup runtime leaks horizon scheduler trace who event request
  have actualTrace : ((app).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial (plan setup)))
      horizon scheduler).Trace (some control) := by
    rw [PMF.map_comp]
    exact trace
  obtain ⟨inputs, valid⟩ := phaseNativeInvariant_history runtime leaks (plan setup)
    (setup.initialLaw.map encodeInputs) horizon scheduler actualTrace
  refine ⟨current, sourceTrace, excluded, actor, ?_⟩
  exact policy_first setup runtime leaks bounds who source event _ _
    (requestedEvent_of_request setup .sequential _ valid who event request) first _ read

end Vegas.SourcePhaseClient
