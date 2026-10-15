/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryStoppedSourceLaw
import Vegas.Game.OnePacketDebtFreeResponse
import Vegas.Game.OnePacketPrescribedCompletion
import Vegas.Game.OnePacketCompletionLaw

/-! # Source-value kernels of prescribed play under actual recovery service -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : (recoveryApplication (runtime setup) leaks).Scheduler}
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon recoveryScheduler delay)
  (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon recoveryScheduler
    bound)
  (timely : (runtime setup).AsyncTimely delay bound)
  (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)

local notation "scheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))

include initialized nativeLaw opportunity inclusion timely completes in
private theorem recovery_canonical_binding_sourceLaw
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : (E).Trace (some ⟨remaining, some who, execution⟩))
    (clear : PublicExclusionRecord (RecoveryState.mk execution.application ∅))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (action : (graph setup).Action event) {value : L.Val payload}
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      PublicationResult (L.Val payload)) = .success value)
    (member : (runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action ∈
        bounds.onePacketActions (runtime setup) leaks who (execution.recall who)
          (execution.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action).transmission = some material)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (start : (E).History)
    (current : start.state = some ⟨remaining, none,
      execution.respond (application setup leaks) who
        ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
          (execution.observe (application setup leaks) who) event action)⟩) :
    ((N).runBehavioralUntil certificate players
      (fun history => LateStopped setup leaks bounds horizon scheduler rank history ∨
        ¬ Clear history.state) start).map
        (fun history => nativeDecodedState setup leaks history.state) =
      (ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action)).map some := by
  obtain ⟨serial, slot⟩ := onePacket_canonicalFreshSlot_exists trace who
  have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
      (PublicationResult.success value : PublicationResult (L.Val payload)) := by
    rw [← successful]
    simp only [cast_cast, cast_eq]
  have canonical := (runtime setup).canonicalServiceDecision_binding leaks who
    (execution.recall who) (execution.observe (application setup leaks) who) event payload outputEq
    codeEq node serial slot (.success value)
  have sends := submits
  rw [actionEq, canonical] at sends
  cases Option.some.inj sends
  have fresh := canonicalFreshSlot_spec who
    (execution.observe (application setup leaks) who).application serial slot
  have after : (⟨.commitment event (who, .prepared serial), some ⟨payload, value⟩⟩ :
      Submission (graph setup)).candidateAfter who
        (execution.observe (application setup leaks) who).application.candidates
        (.prepared serial) =
      .openable ⟨payload, value⟩ := by
    simp [Submission.candidateAfter, fresh]
  have law := recovery_firstActivation_commitment_sourceLaw initialized nativeLaw inclusion
    opportunity timely completes certificate players trace clear event turn never node
      ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) event action)
      member _ submits rfl after ordered decoded start current
  have sourceEq : sourceOfValue setup event outputEq value =
      decodeEventAction setup.program event action := by
    rw [actionEq]
    rfl
  simpa only [sourceEq] using law

include initialized nativeLaw opportunity inclusion timely completes in
private theorem recovery_canonical_sourceLaw
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : (E).Trace (some ⟨remaining, some who, execution⟩))
    (clear : PublicExclusionRecord (RecoveryState.mk execution.application ∅))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    (action : (graph setup).Action event)
    (bindSuccess : ∀ owner payload outputEq codeEq,
      nodeView (graph setup) event = .bind owner payload outputEq codeEq →
        ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
          PublicationResult (L.Val payload)) = .success value)
    (discloseSuccess : ∀ owner payload binding checks outputEq codeEq,
      nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
        (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = true)
    (member : (runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action ∈
        bounds.onePacketActions (runtime setup) leaks who (execution.recall who)
          (execution.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action).transmission = some material)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (start : (E).History)
    (current : start.state = some ⟨remaining, none,
      execution.respond (application setup leaks) who
        ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
          (execution.observe (application setup leaks) who) event action)⟩) :
    ((N).runBehavioralUntil certificate players
      (fun history => LateStopped setup leaks bounds horizon scheduler rank history ∨
        ¬ Clear history.state) start).map
        (fun history => nativeDecodedState setup leaks history.state) =
      (ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action)).map some := by
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      have noActor := nodeView_sample_actor outputEq codeEq
      rw [owned] at noActor
      cases noActor
  | bind owner payload outputEq codeEq =>
      have same : owner = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst owner
      obtain ⟨value, successful⟩ := bindSuccess who payload outputEq codeEq node
      exact recovery_canonical_binding_sourceLaw initialized nativeLaw opportunity inclusion
        timely completes certificate players trace clear event turn never node action successful
        member material submits ordered decoded start current
  | resolve owner payload binding checks outputEq codeEq =>
      have same : owner = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst owner
      exact recovery_firstActivation_disclosure_sourceLaw initialized nativeLaw inclusion
        opportunity timely completes certificate players trace clear event turn never node action
        (discloseSuccess who payload binding checks outputEq codeEq node) material submits ordered
        decoded start current

include initialized nativeLaw opportunity inclusion timely completes in
private theorem recovery_committed_canonical_sourceLaw
    [∀ player, DecidableEq ((N).InfoState player)]
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (history : (E).History)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (clear : PublicExclusionRecord (RecoveryState.mk execution.application ∅))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    (action : (graph setup).Action event)
    (bindSuccess : ∀ owner payload outputEq codeEq,
      nodeView (graph setup) event = .bind owner payload outputEq codeEq →
        ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
          PublicationResult (L.Val payload)) = .success value)
    (discloseSuccess : ∀ owner payload binding checks outputEq codeEq,
      nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
        (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = true)
    (member : (runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action ∈
        bounds.onePacketActions (runtime setup) leaks who (execution.recall who)
          (execution.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action).transmission = some material)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (info : (N).InfoState who)
    (observed : (N).infoOf who history.trace = info)
    (choice : (N).Choice who info)
    (selected : choice.1 = some ((runtime setup).canonicalServiceDecision leaks who
      (execution.recall who) (execution.observe (application setup leaks) who) event action)) :
    ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) players who
        ((players who).commit info choice))
      (fun stop => LateStopped setup leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) history).map
        (fun stop => nativeDecodedState setup leaks stop.state) =
      (ProtocolState.step setup.program point
        (fun _ => decodeEventAction setup.program event action)).map some := by
  classical
  subst observed
  have trace : (E).Trace (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  have going : ¬ (LateStopped setup leaks bounds horizon scheduler rank history ∨
      ¬ Clear history.state) := by
    rintro (⟨control, state, prefixed⟩ | notClear)
    · rw [current] at state
      cases Option.some.inj state
      exact Nat.succ_ne_self rank (isPrefix_unique prefixed ordered)
    · apply notClear
      rw [current]
      exact clear
  have running : ¬ (E).terminal history.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  rw [(N).runBehavioralUntil_of_running certificate _ going running, PMF.map_bind]
  calc
    _ = ((N).runBehavioralFrom
        (Profile.update (sig := (N).behavioralSignature) players who
          ((players who).commit ((N).infoOf who history.trace) choice)) 1 history).bind
        (fun _ => (ProtocolState.step setup.program point
          (fun _ => decodeEventAction setup.program event action)).map some) := by
      refine bind_congr_on_support _ fun next stepped => ?_
      have committedStep := (menu).run_commit_response (initialLaw setup) horizon scheduler players
        history who remaining execution current choice _ selected
      have nextState : next.state = some ⟨remaining, none, execution.respond
          (application setup leaks) who ((runtime setup).canonicalServiceDecision leaks who
            (execution.recall who) (execution.observe (application setup leaks) who) event
            action)⟩ := by
        have inLaw : next.state ∈ (PMF.pure (α := (application setup leaks).ProtocolState)
            (some ⟨remaining, none, execution.respond (application setup leaks) who
              ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
                (execution.observe (application setup leaks) who) event action)⟩)).support := by
          rw [← committedStep, PMF.support_map]
          exact ⟨next, by convert stepped, rfl⟩
        exact (PMF.mem_support_pure_iff _ _).mp inLaw
      exact recovery_canonical_sourceLaw initialized nativeLaw opportunity inclusion timely
        completes certificate _ trace clear event turn never action bindSuccess discloseSuccess
        member material submits ordered decoded next nextState
    _ = _ := by rw [PMF.bind_const]


include initialized nativeLaw opportunity inclusion timely completes in
/-- Installing the source-main choice at an actual clear first callback gives the
source behavioral step at its decoded intended point. Both binding and disclosure
use the actual recovery service, with arbitrary continuation policies. -/
theorem recovery_firstActivation_honest_sourceLaw
    [∀ player, DecidableEq ((N).InfoState player)]
    (wellFormed : setup.WellFormed)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (history : (E).History)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (clear : PublicExclusionRecord (RecoveryState.mk execution.application ∅))
    (event : (graph setup).EventId)
    (pending : pendingEvent setup leaks who (some (execution.recall who,
      execution.observe (application setup leaks) who)) = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (info : (N).InfoState who) (observed : (N).infoOf who history.trace = info) :
    ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) players who
        ((players who).withLaw info
          (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler source who info)))
      (fun stop => LateStopped setup leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) history).map
        (fun stop => nativeDecodedState setup leaks stop.state) =
      (ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile source.strategy) point).map some := by
  classical
  have infoEq : (N).infoOf who history.trace =
      some (execution.recall who, execution.observe (application setup leaks) who) := by
    change ((menu).signals (initialLaw setup) horizon scheduler).infoOf who history.trace = _
    rw [(menu).info, current]
    simp [ReactiveApplication.observe]
  have atSite := observed.symm.trans infoEq
  subst atSite
  have trace : (E).Trace (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  have turn := (pendingEvent_spec pending).1
  have forced : ForcedState setup leaks who (some ⟨remaining, some who, execution⟩) :=
    ⟨rank, point, ordered, decoded, forcedPoint_of_intended who intendedPoint⟩
  have notOwed : ∀ found, decodedPoint setup execution.application.config = some found →
      ¬ ProtocolState.OwesFailure who setup.program found := by
    intro found foundDecoded
    have same := Option.some.inj
      (((decodedPoint_eq_of_isPrefix ordered).trans decoded).symm.trans foundDecoded)
    subst found
    exact ProtocolState.Intended.not_owesFailure who setup.program point intendedPoint
  have transmits := canonicalTransmitsAt_of_debtFree wellFormed trace who forced notOwed event
    pending
  have fits := recovery_firstActivation_inclusionFits initialized nativeLaw opportunity timely
    ((menu).toRawTrace (initialLaw setup) horizon scheduler trace) rfl clear event turn never
  have retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound :=
    retainsCoveredCanonical_of_adequate bounds covers capacity horizon scheduler bound
  have going : ¬ (LateStopped setup leaks bounds horizon scheduler rank history ∨
      ¬ Clear history.state) := by
    rintro (⟨control, state, prefixed⟩ | notClear)
    · rw [current] at state
      cases Option.some.inj state
      exact Nat.succ_ne_self rank (isPrefix_unique prefixed ordered)
    · apply notClear
      rw [current]
      exact clear
  have running : ¬ (E).terminal history.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have active : (E).active history.state who := by
    rw [current]
    rfl
  have actsOnce :=
    ((menu).decisionRecall (initialLaw setup) horizon scheduler).actsOnceWhereItMatters
  rw [← asIfHonest_bind_step_eq_behavioralStateStep source who execution ordered decoded
      intendedPoint turn (execution.recall who),
    (N).runBehavioralUntil_update_withLaw_eq_bind certificate actsOnce players who (players who)
      _ _ _ history observed going running active,
    PMF.map_bind]
  change ((honestResponse setup leaks source who (execution.recall who)
      (execution.observe (application setup leaks) who)).map
        (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
          (some (execution.recall who,
            execution.observe (application setup leaks) who)))).bind _ = _
  unfold honestResponse
  rw [turn]
  dsimp only
  rw [PMF.bind_map, PMF.bind_map, PMF.map_bind]
  refine bind_congr_on_support _ fun choice supported => ?_
  have encodes := asIfHonestProfile_encodes source who execution rank ordered point decoded
    (execution.recall who) event turn choice supported
  rcases choice with _ | action
  · simp at encodes
  cases encoded : encodeEventAction? setup.program event action with
  | none => simp [encoded] at encodes
  | some graphAction =>
      have success := asIfHonestProfile_success source who execution rank ordered point decoded
        (execution.recall who) action supported
      obtain ⟨material, submits⟩ := Option.ne_none_iff_exists'.mp
        (transmits action graphAction encoded success.1 success.2)
      have commits : action.CommitsValue := by
        cases action with
        | commit owner name payload result =>
            cases result with
            | failure => exact (success.1 owner name payload rfl).elim
            | success value => exact ⟨value, rfl⟩
        | reveal => trivial
      have bindSuccess : ∀ owner payload outputEq codeEq,
          nodeView (graph setup) event = .bind owner payload outputEq codeEq →
            ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) graphAction :
              PublicationResult (L.Val payload)) = .success value := by
        intro owner payload outputEq _codeEq _node
        obtain ⟨value, rfl⟩ := encodeEventAction?_commitsValue setup.program event action commits
          graphAction encoded owner payload outputEq
        exact ⟨value, by simp⟩
      have discloseSuccess : ∀ owner payload binding checks outputEq codeEq,
          nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
            (cast (congrArg EventGraph.EventField.Action outputEq) graphAction : Bool) = true := by
        intro _owner payload _binding _checks outputEq _codeEq _node
        exact encodeEventAction?_discloses setup.program event action success.2 graphAction
          encoded payload outputEq
      have effective : EffectiveDecision event graphAction := by
        unfold EffectiveDecision
        cases node : nodeView (graph setup) event with
        | bind owner payload outputEq codeEq =>
            obtain ⟨value, successful⟩ := bindSuccess owner payload outputEq codeEq node
            refine ⟨value, ?_⟩
            rw [← successful]
            simp
        | sample | resolve => trivial
      have offered := canonical_mem_onePacket_of_pending bounds trace who event turn
        (pendingEvent_spec pending).2.2.2 graphAction
        (retains trace who event graphAction turn (pendingEvent_spec pending).2.2.2 fits effective
          (by rw [submits]; simp))
      have selected : (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
          (some (execution.recall who, execution.observe (application setup leaks) who))
          ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
            (execution.observe (application setup leaks) who) event graphAction)).1 =
          some ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
            (execution.observe (application setup leaks) who) event graphAction) := by
        unfold responseChoice
        simp only [offered, ↓reduceDIte]
      have law := recovery_committed_canonical_sourceLaw initialized nativeLaw opportunity
        inclusion timely completes certificate players history current clear event turn never
        graphAction bindSuccess discloseSuccess offered material submits ordered decoded _
        observed _ selected
      have decodeEq := decodeEventAction_encodeEventAction?_eq_some setup.program event action
        graphAction encoded
      simpa only [Function.comp_apply, Option.bind_some, encoded, decodeEq] using law


include initialized nativeLaw opportunity inclusion timely completes in
/-- The prescribed tremble perturbs the actual first-callback source kernel by at most
six times its scale times the payoff bound. -/
theorem recovery_firstActivation_prescribed_sourceKernel
    [∀ player, DecidableEq ((N).InfoState player)]
    (wellFormed : setup.WellFormed)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (history : (E).History)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (clear : PublicExclusionRecord (RecoveryState.mk execution.application ∅))
    (event : (graph setup).EventId)
    (pending : pendingEvent setup leaks who (some (execution.recall who,
      execution.observe (application setup leaks) who)) = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (info : (N).InfoState who) (observed : (N).infoOf who history.trace = info)
    {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (value : Option (ProtocolState setup.program) → ℝ)
    {payoffBound : ℝ} (bounded : ∀ state, |value state| ≤ payoffBound) :
    |expect ((N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) players who
          ((players who).withLaw info
            (slotPrescribedComponent setup leaks bounds (initialLaw setup) horizon scheduler source
              scale nonnegative le_one who info)))
        (fun stop => LateStopped setup leaks bounds horizon scheduler rank stop ∨
          ¬ Clear stop.state) history)
        (fun stop => value (nativeDecodedState setup leaks stop.state)) -
      expect (ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile source.strategy) point) (fun next => value (some next))| ≤
      6 * scale * payoffBound := by
  classical
  have infoEq : (N).infoOf who history.trace =
      some (execution.recall who, execution.observe (application setup leaks) who) := by
    change ((menu).signals (initialLaw setup) horizon scheduler).infoOf who history.trace = _
    rw [(menu).info, current]
    simp [ReactiveApplication.observe]
  have atSite := observed.symm.trans infoEq
  subst atSite
  have going : ¬ (LateStopped setup leaks bounds horizon scheduler rank history ∨
      ¬ Clear history.state) := by
    rintro (⟨control, state, prefixed⟩ | notClear)
    · rw [current] at state
      cases Option.some.inj state
      exact Nat.succ_ne_self rank (isPrefix_unique prefixed ordered)
    · apply notClear
      rw [current]
      exact clear
  have running : ¬ (E).terminal history.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have active : (E).active history.state who := by
    rw [current]
    rfl
  have actsOnce :=
    ((menu).decisionRecall (initialLaw setup) horizon scheduler).actsOnceWhereItMatters
  have boundNonneg : 0 ≤ payoffBound := (abs_nonneg (value (some point))).trans (bounded _)
  have valueBounded : ∀ stop : (E).History,
      |value (nativeDecodedState setup leaks stop.state)| ≤ payoffBound := fun stop => bounded _
  have targetBounded :
      |expect (ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile source.strategy) point)
        (fun next => value (some next))| ≤ payoffBound :=
    expect_abs_le_of_bounded boundNonneg (fun next => bounded _)
  have mainLaw := recovery_firstActivation_honest_sourceLaw initialized nativeLaw opportunity
    inclusion timely completes wellFormed covers capacity source certificate players history
    current clear event pending never ordered decoded intendedPoint _ observed
  have mainEq := congrArg (fun law => expect law value) mainLaw
  simp only [expect_map, Function.comp_def] at mainEq
  rw [(N).runBehavioralUntil_update_withLaw_eq_bind certificate actsOnce players who (players who)
      _ _ _ history observed going running active,
    expect_bind_tower_bounded _ _ _ valueBounded] at mainEq
  rw [(N).runBehavioralUntil_update_withLaw_eq_bind certificate actsOnce players who (players who)
      _ _ _ history observed going running active,
    expect_bind_tower_bounded _ _ _ valueBounded]
  exact abs_expect_slotTrembledChoice_sub_le nonnegative le_one who _ _ _ _ _
    (fun choice => expect_abs_le_of_bounded boundNonneg valueBounded) targetBounded mainEq


include initialized nativeLaw opportunity inclusion timely completes in
/-- At an actual clear first callback the prescribed component preserves the source
continuation value up to six times the tremble scale times the payoff bound. -/
theorem recovery_firstActivation_prescribed_sourceValue
    [∀ player, DecidableEq ((N).InfoState player)]
    (wellFormed : setup.WellFormed)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (history : (E).History)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (clear : PublicExclusionRecord (RecoveryState.mk execution.application ∅))
    (event : (graph setup).EventId)
    (pending : pendingEvent setup leaks who (some (execution.recall who,
      execution.observe (application setup leaks) who)) = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (info : (N).InfoState who) (observed : (N).infoOf who history.trace = info)
    {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (beneficiary : Player)
    {payoffBound : ℝ}
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout beneficiary| ≤
        payoffBound) :
    |expect ((N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) players who
          ((players who).withLaw info
            (slotPrescribedComponent setup leaks bounds (initialLaw setup) horizon scheduler source
              scale nonnegative le_one who info)))
        (fun stop => LateStopped setup leaks bounds horizon scheduler rank stop ∨
          ¬ Clear stop.state) history)
        (fun stop => (nativeDecodedState setup leaks stop.state).elim 0
          (sourcePointValue setup parameter utility excludedPayoff
            (setup.intendedOpeningProfile source.strategy) beneficiary)) -
      sourcePointValue setup parameter utility excludedPayoff
        (setup.intendedOpeningProfile source.strategy) beneficiary point| ≤
      6 * scale * payoffBound := by
  have boundNonneg : 0 ≤ payoffBound :=
    (abs_nonneg
      (exclusionReadoutUtility setup parameter utility excludedPayoff none beneficiary)).trans
      (readoutBounded none)
  have sourceBounded : ∀ next,
      |sourcePointValue setup parameter utility excludedPayoff
        (setup.intendedOpeningProfile source.strategy) beneficiary next| ≤ payoffBound := by
    intro next
    unfold sourcePointValue
    exact expect_abs_le_of_bounded boundNonneg readoutBounded
  have bounded : ∀ state : Option (ProtocolState setup.program),
      |state.elim 0 (sourcePointValue setup parameter utility excludedPayoff
        (setup.intendedOpeningProfile source.strategy) beneficiary)| ≤ payoffBound := by
    intro state
    cases state with
    | none => simpa using boundNonneg
    | some next => exact sourceBounded next
  have estimate := recovery_firstActivation_prescribed_sourceKernel initialized nativeLaw
    opportunity inclusion timely completes wellFormed covers capacity source certificate players
    history current clear event pending never ordered decoded intendedPoint info observed
    nonnegative le_one _ bounded
  simpa only [Option.elim_some,
    expect_sourcePointValue_behavioralStateStep setup parameter utility excludedPayoff
      (setup.intendedOpeningProfile source.strategy) beneficiary readoutBounded point]
    using estimate


end Vegas
