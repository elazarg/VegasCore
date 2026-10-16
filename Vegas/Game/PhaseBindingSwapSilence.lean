/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingSwapKey
import Vegas.Game.PhaseBindingWordOmission
import Vegas.Game.PhaseTimingBindingNoise
import Vegas.Game.PhaseBindingNonmissingLaw
import Vegas.Pending.PhaseBindingSlotHistory

/-! # Original omission and guarded timing silence across hidden input changes -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks

open Classical in
private theorem timing_missing_law (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (option : LateOption bounds.candidateCount)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed source who event payload
      binding option past view).map (fun response => response.transmission.isNone) =
      match option with
      | none => PMF.pure true
      | some serial =>
          if serial.val ∈ PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
              past view then
            (source.strategy who (setup.commitRecoveryClearInformation wellFormed who
              (phaseSourceView? setup mode runtime leaks who event view))).map
                (fun choice => CommitRecoveryMove.missed choice.1)
          else PMF.pure true := by
  cases option with
  | none =>
      rw [phaseRecoveryTimingPolicy_wait, PMF.pure_map]
      rfl
  | some serial =>
      rw [phaseRecoveryTimingPolicy, phaseRecoveryTimingTaggedLaw, PMF.map_comp, PMF.map_comp]
      change ((source.strategy who (setup.commitRecoveryClearInformation wellFormed who
          (phaseSourceView? setup mode runtime leaks who event view))).map
        (fun choice => (phaseBindingTimingResponse setup mode runtime leaks bounds who event payload
          (some serial) past view
            (phaseRecoveryBindingData setup mode event who payload binding
      choice.1)).transmission.isNone)) = _
      dsimp only
      by_cases eligible : serial.val ∈ PhaseCount.phaseBindingSlots runtime leaks bounds who event
          payload past view
      · rw [ite_eq_left eligible]
        apply map_congr_on_support
        intro choice _drawn
        have flag := phaseRecoveryBindingData_missing setup mode who event payload binding choice.1
        unfold phaseBindingTimingResponse
        rw [← flag]
        cases missing : (phaseRecoveryBindingData setup mode event who payload binding choice.1).2
          <;> simp only [Bool.false_eq_true, ↓reduceIte, eligible,
            phaseBindingResponse, Option.isNone_none, Option.isNone_some]
      · rw [ite_eq_right eligible]
        have constant (choice : setup.commitRecoveryModel.Choice who
            (setup.commitRecoveryClearInformation wellFormed who
              (phaseSourceView? setup mode runtime leaks who event view))) :
            (phaseBindingTimingResponse setup mode runtime leaks bounds who event payload
              (some serial) past view
                (phaseRecoveryBindingData setup mode event who payload binding
                  choice.1)).transmission.isNone = true := by
          unfold phaseBindingTimingResponse
          split <;> simp only [eligible, ↓reduceIte, Option.isNone_none]
        simp only [constant]
        exact PMF.map_const _ _

variable (plan : RuntimePhasePlan (serviceGraph setup mode)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- A genuine swapped binding callback has exactly the SAME guarded serial
set. This uses actual menu legality and candidate freshness, not a claim about
whole raw-menu cardinality or fixed private inputs. -/
theorem phaseBindingSlots_swap_of_histories
    (swap : HiddenSwap (serviceGraph setup mode)) (remaining : Nat) (who : Player)
    (original : (app).Execution)
    (trace : (E).Trace (some ⟨remaining, some who, original⟩))
    (swappedTrace : (E).Trace (some ⟨remaining, some who, swap.phaseExecution original⟩))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : original.application.SeedRequest who ⟨original.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (original.recall who),
      PhaseCount.event? message.payload ≠ some ⟨original.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
        ((swap.phaseExecution original).recall who)
          ((swap.phaseExecution original).observe app who) =
      PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
        (original.recall who) (original.observe app who) := by
  classical
  let inputs := setup.initialLaw.map encodeInputs
  have firstTrace : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some ⟨remaining, some who, original⟩) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have secondTrace : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some ⟨remaining, some who, swap.phaseExecution original⟩) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact swappedTrace
  have secondUnsent : ∀ message ∈ (app).outputs ((swap.phaseExecution original).recall who),
      PhaseCount.event? message.payload ≠ some ⟨original.application.attempt, event⟩ := by
    change ∀ message ∈ (app).outputs ((original.recall who).map swap.phaseEntry), _
    rw [swap.phaseOutputs_entry]
    exact unsent
  rw [PhaseCount.phaseBindingSlots_eq_fresh_of_history runtime leaks bounds menu plan inputs
    horizon scheduler _ secondTrace who event payload binding request secondUnsent values,
    PhaseCount.phaseBindingSlots_eq_fresh_of_history runtime leaks bounds menu plan inputs
      horizon scheduler _ firstTrace who event payload binding request unsent values]
  apply Finset.filter_congr
  intro serial _inside
  change swapCandidate (swap.raw (who, .prepared serial))
    (original.application.current.native.candidates.lookup (who, .prepared serial)) = .fresh ↔ _
  exact swapCandidate_eq_fresh_iff _ _

/-- Under one fixed timing option, the NON-RAW binding silence law is identical
at two genuine hidden-swap callbacks. Source omissions remain fresh draws, and
accepted typed failure is not classified as an omission. -/
theorem phaseSourceTimingPolicy_binding_silence_swap
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (n : Nat) (swap : HiddenSwap (serviceGraph setup mode)) (remaining : Nat) (who : Player)
    (original : (app).Execution)
    (trace : (E).Trace (some ⟨remaining, some who, original⟩))
    (swappedTrace : (E).Trace (some ⟨remaining, some who, swap.phaseExecution original⟩))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : original.application.SeedRequest who ⟨original.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (original.recall who),
      PhaseCount.event? message.payload ≠ some ⟨original.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (clear : original.application.current.excluded = ∅)
    (option : LateOption bounds.candidateCount) :
    (phaseSourceTimingPolicy setup mode runtime leaks bounds wellFormed (approximation.sequence n)
      option who (original.recall who) (original.observe app who)).map
        (fun response => response.transmission.isNone) =
      (phaseSourceTimingPolicy setup mode runtime leaks bounds wellFormed (approximation.sequence n)
        option who ((swap.phaseExecution original).recall who)
          ((swap.phaseExecution original).observe app who)).map
            (fun response => response.transmission.isNone) := by
  let inputs := setup.initialLaw.map encodeInputs
  have firstRaw := (menu).toRawTrace initial horizon scheduler trace
  have secondRaw := (menu).toRawTrace initial horizon scheduler swappedTrace
  have firstCounted : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some ⟨remaining, some who, original⟩) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact firstRaw
  have secondCounted : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some ⟨remaining, some who, swap.phaseExecution original⟩) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact secondRaw
  obtain ⟨_, firstValid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    firstCounted
  obtain ⟨_, secondValid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
      scheduler
    secondCounted
  rw [phaseSourceTimingPolicy_binding setup mode runtime leaks bounds wellFormed _ option original
    firstValid who event payload binding request,
    phaseSourceTimingPolicy_binding setup mode runtime leaks bounds wellFormed _ option _
      secondValid
      who event payload binding request,
    timing_missing_law, timing_missing_law]
  have slots := phaseBindingSlots_swap_of_histories setup mode runtime leaks bounds plan horizon
    scheduler swap remaining who original trace swappedTrace event payload binding request unsent
      values
  have missing := phaseBindingWord_missing_eq_of_histories setup mode runtime leaks bounds plan
    horizon scheduler finite wellFormed target approximation maximal n who event payload binding
      ⟨remaining, some who, original⟩ ⟨remaining, some who, swap.phaseExecution original⟩ trace
        swappedTrace clear clear request.2.2.1 request.2.2.1
  cases option with
  | none => rfl
  | some serial => rw [slots, missing]

end Vegas
