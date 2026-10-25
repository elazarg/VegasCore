/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryComparisonContinuationValue
import Vegas.Game.OnePacketSiteLinearity

/-! # Source values across a completed intended event -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

/-- A completed failed event in a genuine native history retains its owner's
source obligation, independently of any future service guarantee. -/
theorem decodedDebt_of_failed_event
    (history : (NP).History) (control : (application setup leaks).Control)
    (current : history.state = some control) (event : (graph setup).EventId)
    (completed : event ∈ control.execution.application.config.cut.completed)
    (who : Player) (owned : (graph setup).actor? event = some who)
    (failed : StoreEventFailed control.execution.application.config.store event) :
    DecodedState setup leaks (failureProfile setup.program)
      (ProtocolState.OwesFailure who setup.program) history.state := by
  let valid : (application setup leaks).ServiceInvariant scheduler
      (fun execution => SourceFailureRecord (failureProfile setup.program)
        execution.application.config) :=
    { respond := fun execution actor response holds => by
        rw [((runtime setup).reactive_respond_application leaks execution actor response).1]
        exact holds
      environment := fun execution next command holds _chosen reached =>
        holds.step (environmentStep_configStep setup leaks execution next command reached) }
  have record := valid.history (initialLaw setup) horizon (fun state supported => by
    obtain ⟨initial, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact SourceFailureRecord.initial setup (failureProfile setup.program) initial)
    ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      (current ▸ history.trace))
  obtain ⟨rank, residual, holds⟩ := record
  rw [current]
  exact ⟨rank, residual, holds event completed who owned failed⟩

/-- A recorded completion point includes the successful intended source
checkpoint and the predicate used to select that point. -/
theorem completionPoint_spec
    (rank : Nat) (fresh : (application setup leaks).Control → Prop)
    (history : (NP).History) (point : ProtocolState setup.program)
    (somePoint : completionPoint setup leaks bounds horizon scheduler rank fresh history =
      some point) :
    ∃ control : (application setup leaks).Control, history.state = some control ∧
      control.execution.application.config.cut.IsPrefix (rank + 1) ∧
      sourceServicePrefix? setup (rank + 1) control.execution.application.config = some point ∧
      ProtocolState.Intended setup.program point ∧ fresh control := by
  classical
  unfold completionPoint at somePoint
  split at somePoint
  · cases somePoint
  · rename_i control state
    split at somePoint
    · rename_i ordered
      split at somePoint
      · rename_i next decoded
        split at somePoint
        · rename_i good
          cases Option.some.inj somePoint
          exact ⟨control, state, ordered, decoded, good⟩
        · cases somePoint
      · cases somePoint
    · cases somePoint

/-- Before the next source event completes, the configuration remains fixed.
Consequently an intended start has no earlier public-exclusion or own-debt stop. -/
theorem debtStopped_eq_bind_eventPhase
    (certificate : (NP).WellFoundedHistories)
    (players : ∀ who, (N).BehavioralPolicy who) (who : Player)
    (start : (NP).History) (control : (application setup leaks).Control)
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank control.execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    let phase := fun history : (NP).History =>
      LateStopped setup leaks bounds horizon scheduler rank history ∨ ¬ Clear history.state
    let stopped := fun history : (NP).History => ¬ Clear history.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) history.state
    (N).runBehavioralUntil certificate players stopped start =
      ((N).runBehavioralUntil certificate players phase start).bind
        ((N).runBehavioralUntil certificate players stopped) := by
  classical
  intro phase stopped
  let inside := fun history : (NP).History => phase history ∨
    ∃ before : (application setup leaks).Control, history.state = some before ∧
      before.execution.application.config = control.execution.application.config
  have safe : ∀ history, inside history → ¬ phase history → ¬ stopped history := by
    intro history holds going
    obtain ⟨before, state, configEq⟩ := holds.resolve_left going
    have pointDecoded : decodedPoint setup before.execution.application.config = some point := by
      rw [configEq]
      exact (decodedPoint_eq_of_isPrefix ordered).trans decoded
    have clear : Clear history.state := by
      rw [state]
      exact exclusionEvidence_of_decodedIntended
        ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
          scheduler (state ▸ history.trace)) pointDecoded intended
    rintro (unclear | owed)
    · exact unclear clear
    · rw [state] at owed
      obtain ⟨found, ⟨residual⟩, holds⟩ := owed
      exact ProtocolState.Intended.not_owesFailure who setup.program point intended
        (holds point
          ((decodedPoint_eq_of_isPrefix residual.checkpoint.ordered).symm.trans pointDecoded))
  have preserve : ∀ history next, inside history → ¬ phase history →
      ¬ (NP).terminal history.state →
      next ∈ ((N).runBehavioralFrom players 1 history).support → inside next := by
    intro history next holds going running member
    obtain ⟨before, state, configEq⟩ := holds.resolve_left going
    obtain ⟨joint, realized⟩ := onePacket_step_transition bounds players running member
    rw [state] at realized
    obtain ⟨after, afterState, _⟩ := (application setup leaks).transition_recall_prefix
      (initialLaw setup) horizon scheduler before next.state joint realized
    have beforeOrdered : before.execution.application.config.cut.IsPrefix rank := by
      rw [configEq]
      exact ordered
    rcases (transition_configStep (initialLaw setup) horizon scheduler before after joint
      (afterState ▸ realized)).prefix rank beforeOrdered with same | advanced
    · exact Or.inr ⟨after, afterState, same.trans configEq⟩
    · exact Or.inl (Or.inl ⟨after, afterState, advanced⟩)
  suffices splitting : ∀ history, inside history →
      (N).runBehavioralUntil certificate players stopped history =
        ((N).runBehavioralUntil certificate players phase history).bind
          ((N).runBehavioralUntil certificate players stopped) from
    splitting start (Or.inr ⟨control, current, rfl⟩)
  intro history
  induction history using certificate.induction with
  | _ history ih =>
  intro holds
  by_cases halted : phase history
  · rw [(N).runBehavioralUntil_of_stopped certificate players halted, PMF.pure_bind]
  by_cases ended : (NP).terminal history.state
  · rw [(N).runBehavioralUntil_of_terminal certificate players ended,
      (N).runBehavioralUntil_of_terminal certificate players ended, PMF.pure_bind,
      (N).runBehavioralUntil_of_terminal certificate players ended]
  rw [(N).runBehavioralUntil_of_running certificate players (safe history holds halted) ended,
    (N).runBehavioralUntil_of_running certificate players halted ended, PMF.bind_bind]
  apply bind_congr_on_support
  intro next member
  exact ih next ((N).mem_support_runBehavioralFrom_one players ended member).1
    (preserve history next holds halted ended member)

theorem runUntil_after_localLaw_eq
    (certificate : (NP).WellFoundedHistories) (actsOnce : (N).ActsOnceWhereItMatters)
    (players : ∀ who, (N).BehavioralPolicy who) (who : Player)
    [DecidableEq ((N).InfoState who)] (info : (N).InfoState who)
    (law : PMF ((N).Choice who info)) (phase stopped : (NP).History → Prop)
    (history : (NP).History) (observed : (N).infoOf who history.trace = info)
    (active : (NP).active history.state who) (running : ¬ (NP).terminal history.state)
    (going : ¬ phase history)
    (final : (NP).History)
    (member : final ∈ ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) players who
        ((players who).withLaw info law)) phase history).support) :
    (N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) players who
          ((players who).withLaw info law)) stopped final =
      (N).runBehavioralUntil certificate players stopped final := by
  classical
  rw [(N).runBehavioralUntil_of_running certificate _ going running,
    PMF.mem_support_bind_iff] at member
  obtain ⟨next, nextMember, reached⟩ := member
  have reachesFinal := historyReaches_of_mem_runBehavioralUntil (N) certificate _ phase next
    final reached
  rw [(N).runBehavioralFrom_succ_of_not_terminal _ 0 running,
    PMF.mem_support_bind_iff] at nextMember
  obtain ⟨draw, _, stepped⟩ := nextMember
  rw [PMF.mem_support_bindOnSupport_iff] at stepped
  obtain ⟨target, realized, nextEq⟩ := stepped
  change next ∈ (PMF.pure _).support at nextEq
  rw [PMF.mem_support_pure_iff] at nextEq
  subst nextEq
  refine (N).runBehavioralUntil_congr certificate stopped final fun later reaches nonterminal
    player => ?_
  by_cases same : player = who
  · subst player
    rw [Profile.update_same]
    obtain ⟨choice, _⟩ := law.support_nonempty
    obtain ⟨_firstFuel, firstReach⟩ := reachesFinal
    obtain ⟨_secondFuel, secondReach⟩ := reaches
    have within := firstReach.trans secondReach
    have first := (N).withLaw_eq_commit_after_actsOnce actsOnce (players who) info law choice
      observed active draw.2 realized later within nonterminal
    have second := (N).withLaw_eq_commit_after_actsOnce actsOnce (players who) info
      (players who info) choice observed active draw.2 realized later within nonterminal
    rw [BehavioralPolicy.withLaw_eq_self] at second
    exact first.trans second.symm
  · rw [Profile.update_of_ne _ _ same]

end Vegas.RecoveryOnePacket
