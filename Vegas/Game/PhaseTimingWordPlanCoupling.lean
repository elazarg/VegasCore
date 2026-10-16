/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordPlan
import Vegas.Game.PhaseTimingKeyProperties
import Vegas.Game.PhaseTimingBindingKey
import GameTheoryExtensions.Analysis.Protocol.FreeKeyedPoolObservation
import Vegas.Game.PhaseTimingPoolPlan
import Vegas.Game.PhaseCommitTimingWordPolicy

/-! # Original owner words under actual finite timing plans -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound


/-- At two genuine played clear inputs, one original finite plan selects
both prescribed channels or the SAME timing option for every latent word.
Only the actual erased key is compared; no response-law premise is used. -/
theorem phaseTimingWordPlanPolicy_paired_of_key
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (fallback : (who : Player) → (N).Policy who)
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (firstPast secondPast : List (app).PlayerEntry)
    (firstView secondView : (app).PlayerView)
    (firstPlayed : some (firstPast, firstView) ∈ (N).playedInformation who)
    (secondPlayed : some (secondPast, secondView) ∈ (N).playedInformation who)
    (firstClear : ¬ PhasePublicExclusion setup mode runtime leaks
      (some (firstPast, firstView)))
    (secondClear : ¬ PhasePublicExclusion setup mode runtime leaks
      (some (secondPast, secondView)))
    (sameKey : phaseTimingKey runtime leaks who (some (firstPast, firstView)) =
      phaseTimingKey runtime leaks who (some (secondPast, secondView))) :
    ((∀ word, phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
        bound fallback wellFormed source block low generation slotWeight slotNonnegative
          slotBounded plan who word firstPast firstView =
        phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed source block low
          generation slotWeight slotNonnegative slotBounded who word firstPast firstView) ∧
      (∀ word, phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
        bound fallback wellFormed source block low generation slotWeight slotNonnegative
          slotBounded plan who word secondPast secondView =
        phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed source block low
          generation slotWeight slotNonnegative slotBounded who word secondPast secondView)) ∨
    ∃ option,
      (∀ word, phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
        bound fallback wellFormed source block low generation slotWeight slotNonnegative
          slotBounded plan who word firstPast firstView =
        phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed source block low
          generation slotWeight slotNonnegative slotBounded option who word firstPast firstView) ∧
      (∀ word, phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
        bound fallback wellFormed source block low generation slotWeight slotNonnegative
          slotBounded plan who word secondPast secondView =
        phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed source block low
          generation slotWeight slotNonnegative slotBounded option who word secondPast
            secondView) := by
  classical
  let first : Agent := ⟨who, ⟨some (firstPast, firstView), firstPlayed⟩⟩
  let second : Agent := ⟨who, ⟨some (secondPast, secondView), secondPlayed⟩⟩
  have firstNotFree : ¬ isFree first := firstClear
  have secondNotFree : ¬ isFree second := secondClear
  have classified : isKeyed first ↔ isKeyed second :=
    phaseUnprotected_iff_of_timingKey_eq runtime leaks bound who firstPast secondPast firstView
      secondView sameKey
  have samePool : pool first = pool second := freeKeyedPool_eq_of_not_free firstNotFree
    secondNotFree classified sameKey
  have readout (policy : (app).Policy)
      (covered : ∀ past view response, response ∈ (policy past view).support →
        response ∈ (menu).actions who past view)
      (past : List (app).PlayerEntry) (view : (app).PlayerView) :
      (((menu).restrictPolicy initial horizon scheduler who policy) (some (past, view))).map
          (fun choice => choice.1.getD ⟨none⟩) = policy past view := by
    have exactPolicy := congrFun (congrFun ((menu).decode_restrictPolicy_of_covered initial
      horizon scheduler who policy covered) past) view
    simpa only [ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
      PMF.map_comp, Function.comp_def, ReactiveApplication.ResponseMenu.rawChoice]
        using exactPolicy
  have keyedLaw (past : List (app).PlayerEntry) (view : (app).PlayerView)
      (present : some (past, view) ∈ (N).playedInformation who)
      (owned : ownedKeyed isFree isKeyed (⟨who, ⟨some (past, view), present⟩⟩ : Agent))
      (word : DecisionView who Δ) :
      phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded plan
          who word past view =
      phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed source block low
        generation slotWeight slotNonnegative slotBounded
          (ownedKeyedIdentify (key := poolKey) owned (plan (pool ⟨who, ⟨_, present⟩⟩))) who word
            past view := by
    rw [word_member_apply, dite_eq_left present,
      phaseTimingWordComponent_of_ownedKeyed setup mode runtime leaks bounds initial horizon
        scheduler bound wellFormed source block low generation slotWeight slotNonnegative
          slotBounded who (some (past, view)) present word owned]
    exact readout _ (phaseCommitTimingWordPolicy_covered setup mode runtime leaks bounds wellFormed
      source block low generation slotWeight slotNonnegative slotBounded _ who word) past view
  have prescribedLaw (past : List (app).PlayerEntry) (view : (app).PlayerView)
      (present : some (past, view) ∈ (N).playedInformation who)
      (notFree : ¬ isFree (⟨who, ⟨some (past, view), present⟩⟩ : Agent))
      (notKeyed : ¬ isKeyed (⟨who, ⟨some (past, view), present⟩⟩ : Agent))
      (word : DecisionView who Δ) :
      phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded plan
          who word past view =
      phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed source block low generation
        slotWeight slotNonnegative slotBounded who word past view := by
    rw [word_member_apply, dite_eq_left present]
    have component : phaseTimingWordComponent setup mode runtime leaks bounds initial horizon
        scheduler bound wellFormed source block low generation slotWeight slotNonnegative
          slotBounded who word ⟨who, ⟨some (past, view), present⟩⟩
            (plan (pool ⟨who, ⟨some (past, view), present⟩⟩)) =
        (menu).restrictPolicy initial horizon scheduler who
          (phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed source block low
            generation slotWeight slotNonnegative slotBounded who word) (some (past, view)) := by
      unfold phaseTimingWordComponent
      obtain ⟨identify, same⟩ := freeKeyedComponent_of_not_free (free := isFree)
        (keyed := isKeyed) (key := poolKey) _ _ _
          (agent := ⟨who, ⟨some (past, view), present⟩⟩) notFree
      rw [same, keyedComponent_of_not_keyed _ _ (fun owned => notKeyed owned.1)]
      simp only [dite_true, cast_eq]
    rw [component]
    exact readout _ (phaseCommitWordPolicy_covered setup mode runtime leaks bounds wellFormed
      source block low generation slotWeight slotNonnegative slotBounded who word) past view
  by_cases keyed : isKeyed first
  · have secondKeyed : isKeyed second := classified.mp keyed
    let option := ownedKeyedIdentify (key := poolKey) ⟨keyed, firstNotFree⟩ (plan (pool first))
    have sameOption := ownedKeyedIdentify_at_eq plan first second ⟨keyed, firstNotFree⟩
      ⟨secondKeyed, secondNotFree⟩ samePool
    refine Or.inr ⟨option, ?_, ?_⟩
    · exact keyedLaw firstPast firstView firstPlayed ⟨keyed, firstNotFree⟩
    · intro word
      have law := keyedLaw secondPast secondView secondPlayed ⟨secondKeyed, secondNotFree⟩ word
      exact law.trans (congrArg (fun selected : LateOption bounds.candidateCount =>
        phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed source block low
          generation slotWeight slotNonnegative slotBounded selected who word secondPast secondView)
            sameOption).symm
  · exact Or.inl ⟨prescribedLaw firstPast firstView firstPlayed firstNotFree keyed,
      prescribedLaw secondPast secondView secondPlayed secondNotFree
        (fun yes => keyed (classified.mpr yes))⟩


/-- Actual clear counted actor callbacks derive their playedness, nonfree
classification and shared operational key from the evolving physical memory.
The same original finite plan then selects the same word-member branch. -/
theorem phaseTimingWordPlanPolicy_paired_binding
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (fallback : (who : Player) → (N).Policy who)
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (left right : (app).Control)
    (leftTrace : ((menu).protocol initial horizon scheduler).Trace (some left))
    (rightTrace : ((menu).protocol initial horizon scheduler).Trace (some right))
    (firstActive : left.actor = some who) (secondActive : right.actor = some who)
    (memory : BindingShadow (serviceGraph setup mode)) (owned : memory.OwnBindings who)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (application : left.execution.application = memory.phased who right.execution.application)
    (network : left.execution.network = right.execution.network)
    (receipts : left.execution.receipts = right.execution.receipts)
    (past : (left.execution.recall who).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
      (right.execution.recall who).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)))
    (clear : right.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : right.execution.application.SeedRequest who
      ⟨right.execution.application.attempt, event⟩) :
    ((∀ word, phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
        bound fallback wellFormed source block low generation slotWeight slotNonnegative
          slotBounded plan who word (left.execution.recall who) (left.execution.observe (app) who) =
        phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed source block low
          generation slotWeight slotNonnegative slotBounded who word (left.execution.recall who)
                  (left.execution.observe (app) who)) ∧
      (∀ word, phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
        bound fallback wellFormed source block low generation slotWeight slotNonnegative
          slotBounded plan who word (right.execution.recall who) (right.execution.observe (app)
                  who) =
        phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed source block low
          generation slotWeight slotNonnegative slotBounded who word (right.execution.recall who)
                  (right.execution.observe (app) who))) ∨
    ∃ option,
      (∀ word, phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
        bound fallback wellFormed source block low generation slotWeight slotNonnegative
          slotBounded plan who word (left.execution.recall who) (left.execution.observe (app) who) =
        phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed source block low
          generation slotWeight slotNonnegative slotBounded option who word
                  (left.execution.recall who) (left.execution.observe (app) who)) ∧
      (∀ word, phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
        bound fallback wellFormed source block low generation slotWeight slotNonnegative
          slotBounded plan who word (right.execution.recall who) (right.execution.observe (app)
                  who) =
        phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed source block low
          generation slotWeight slotNonnegative slotBounded option who word
                  (right.execution.recall who)
            (right.execution.observe (app) who)) := by
  have played (control : (app).Control)
      (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
      (active : control.actor = some who) :
      some (control.execution.recall who, control.execution.observe (app) who) ∈
        (N).playedInformation who := by
    have running : ¬ ((menu).protocol initial horizon scheduler).terminal (some control) := by
      change ¬ (control.remaining = 0 ∧ control.actor = none)
      simp only [active, reduceCtorEq, and_false, not_false_eq_true]
    have present := (N).mem_playedInformation (who := who)
      (history := ⟨some control, trace⟩) running
    change ((menu).signals initial horizon scheduler).infoOf who trace ∈ _ at present
    rw [(menu).info initial horizon scheduler who trace] at present
    simpa only [ReactiveApplication.observe, active, ↓reduceIte] using present
  have unflagged (control : (app).Control)
      (empty : control.execution.application.current.excluded = ∅) :
      ¬ PhasePublicExclusion setup mode runtime leaks
        (some (control.execution.recall who, control.execution.observe (app) who)) := by
    rintro ⟨before, view, same, excluded⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
    exact excluded empty
  have firstClear : left.execution.application.current.excluded = ∅ := by
    rw [application]
    exact clear
  have keyEq := phaseTimingKey_binding_memory runtime leaks
    (serviceGraph_revealRelaxedOrdered setup mode) memory who owned valid left.execution
      right.execution application network receipts past event payload binding request
  exact phaseTimingWordPlanPolicy_paired_of_key setup mode runtime leaks bounds initial horizon
    scheduler bound fallback wellFormed source block low generation slotWeight slotNonnegative
      slotBounded plan who _ _ _ _ (played left leftTrace firstActive)
        (played right rightTrace secondActive) (unflagged left firstClear)
          (unflagged right clear) keyEq

end Vegas
