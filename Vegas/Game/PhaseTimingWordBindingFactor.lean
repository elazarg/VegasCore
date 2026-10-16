/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordPlan
import Vegas.Pending.PhaseNativeInvariant

/-! # Actual binding responses factored through the current pool part and source action -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial runtimePlan)
variable [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).InfoState who)]

local notation "N" => ReactiveApplication.ResponseMenu.information (menu) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler
  bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

open Classical in
/-- At an authentic unsent clear binding input, every original finite-plan
member uses only its current pool part and addressed source action. Integrating
that same physical kernel against the genuine AUX nonmissing law recovers the
actual zero-raw component, retaining the original omission and slot tiers. -/
theorem phaseTimingWordPlanPolicy_binding_factor_of_history
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (fallback : (who : Player) → (N).Policy who)
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (clear : control.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (inside : low ≤ event.val ∧ event.val < low + block.length)
    (address : control.execution.application.attempt = ⟨low, generation⟩)
    (capacity : horizon ≤ bounds.candidateCount)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (played : some (control.execution.recall who, control.execution.observe (app) who) ∈
      (N).playedInformation who) :
    let agent : Agent := ⟨who, ⟨some (control.execution.recall who,
      control.execution.observe (app) who), played⟩⟩
    let sourceLaw := (setup.commitRecoveryNonmissingProfile source.strategy who
      (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe (app) who)))).map
            (fun choice => CommitRecoveryMove.underlying choice.1)
    ∃ kernel : Parts (pool agent) → Option (OwnAction Player L) → PMF (app).Action,
      (∀ (plan : (p : Pool) → Parts p) word,
        phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
            fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded
            plan who word (control.execution.recall who) (control.execution.observe (app) who) =
          kernel (plan (pool agent)) (block.wordAction who (event.val - low) word)) ∧
      ∀ part, (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed source 0 le_rfl (by norm_num) slotWeight slotNonnegative slotBounded agent
            part).map (fun choice => choice.1.getD ⟨none⟩) = sourceLaw.bind (kernel part) := by
  classical
  intro agent sourceLaw
  let past := control.execution.recall who
  let view := control.execution.observe (app) who
  let missingAt := fun (_ : List (app).PlayerEntry) (observed : (app).PlayerView) =>
    (source.strategy who (setup.commitRecoveryClearInformation wellFormed who
      (phaseSourceView? setup mode runtime leaks who event observed))).map
        (fun choice => CommitRecoveryMove.missed choice.1)
  let data := fun action : Option (OwnAction Player L) =>
    (phaseRecoveryBindingData setup mode event who payload binding
      (CommitRecoveryMove.lift action)).1
  have raw := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks runtimePlan inputs horizon
    scheduler raw
  have notFree : ¬ isFree agent := by
    change ¬ PhasePublicExclusion setup mode runtime leaks (some (past, view))
    rintro ⟨earlier, observed, same, nonempty⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
    exact nonempty clear
  have restricted (policy : (app).Policy)
      (covered : ∀ earlier observed response, response ∈ (policy earlier observed).support →
        response ∈ PhaseCount.onePacketActions runtime leaks bounds who earlier observed) :
      (((menu).restrictPolicy initial horizon scheduler who policy) (some (past, view))).map
          (fun choice => choice.1.getD ⟨none⟩) = policy past view := by
    have mapped := congrArg (PMF.map (fun response : Option (app).Action =>
      response.getD ⟨none⟩)) ((menu).restrictPolicy_map_val initial horizon scheduler who policy
        past view (covered past view))
    simp only [PMF.map_comp, Function.comp_def, Option.getD_some] at mapped
    change _ = (policy past view).map id at mapped
    rw [PMF.map_id] at mapped
    exact mapped
  by_cases keyed : isKeyed agent
  · let option := fun part : Parts (pool agent) =>
      ownedKeyedIdentify (key := poolKey) ⟨keyed, notFree⟩ part
    let kernel := fun part action => phaseBindingTimingWordResponse setup mode runtime leaks
      bounds who event payload (missingAt past view) (option part) slotWeight slotNonnegative
        slotBounded (data action) past view
    refine ⟨kernel, ?_, ?_⟩
    · intro plan word
      rw [word_member_apply, dite_eq_left played,
        phaseTimingWordComponent_of_ownedKeyed setup mode runtime leaks bounds initial horizon
          scheduler bound wellFormed source block low generation slotWeight slotNonnegative
          slotBounded who _ played word ⟨keyed, notFree⟩]
      change (((menu).restrictPolicy initial horizon scheduler who
        (phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed source block low
          generation slotWeight slotNonnegative slotBounded (option (plan (pool agent))) who word))
            (some (past, view))).map _ = _
      rw [restricted _ (phaseCommitTimingWordPolicy_covered setup mode runtime leaks bounds
        wellFormed source block low generation slotWeight slotNonnegative slotBounded _ who word)]
      exact phaseCommitTimingWordPolicy_binding setup mode runtime leaks bounds wellFormed source
        block low generation slotWeight slotNonnegative slotBounded _ who word control.execution
          valid event payload binding request inside address
    · intro part
      rw [phaseTimingComponent, freeKeyedComponent_of_ownedKeyed _ _ _ ⟨keyed, notFree⟩]
      simp only [phaseSourceTimingComponent, mix_zero, mix_map]
      change mix slotWeight slotNonnegative slotBounded
        ((((menu).restrictPolicy initial horizon scheduler who
          (phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed source who))
            (some (past, view))).map (fun choice => choice.1.getD ⟨none⟩))
        ((((menu).restrictPolicy initial horizon scheduler who
          (phaseSourceTimingPolicy setup mode runtime leaks bounds wellFormed source (option part)
            who)) (some (past, view))).map (fun choice => choice.1.getD ⟨none⟩)) =
          sourceLaw.bind (kernel part)
      rw [restricted _ (phaseSourceSlotPolicy_covered setup mode runtime leaks bounds wellFormed
        source who), restricted _ (phaseSourceTimingPolicy_covered setup mode runtime leaks bounds
        wellFormed source _ who)]
      rw [phaseSourceSlotPolicy_binding setup mode runtime leaks bounds wellFormed source
        control.execution valid who event payload binding request,
        phaseSourceTimingPolicy_binding setup mode runtime leaks bounds wellFormed source
          _ control.execution valid who event payload binding request]
      exact phaseBindingTimingWordResponse_law setup mode runtime leaks bounds wellFormed source
        who event payload binding past view slotWeight slotNonnegative slotBounded sourceLaw id
          (PMF.map_id _) (option part)
  · obtain ⟨serial, _bounded, serialEq, _nonempty, offered, canonical⟩ :=
      PhaseCount.phaseBindingWordPolicy_of_history runtime leaks bounds who event payload binding
        missingAt slotWeight slotNonnegative slotBounded data (menu) runtimePlan inputs horizon
        scheduler capacity control trace active request unsent values
    have selected : reactiveFreshSlot view.application.1 = some serial := by
      obtain ⟨freshSerial, _small, freshSelected⟩ := PhaseCandidates.reactiveFreshSlot_lt_horizon
        runtime leaks runtimePlan inputs horizon scheduler control raw who active
      have equal : freshSerial = serial := by
        simpa only [freshSelected, Option.getD_some] using serialEq
      exact equal ▸ freshSelected
    let kernel := fun (_ : Parts (pool agent)) action => PhaseCount.phaseBindingWordResponse runtime
      leaks bounds who event payload (missingAt past view) serial slotWeight slotNonnegative
        slotBounded (data action) past view
    have prescribedWord (word : DecisionView who Δ) (part : Parts (pool agent)) :
        phaseTimingWordComponent setup mode runtime leaks bounds initial horizon scheduler bound
            wellFormed source block low generation slotWeight slotNonnegative slotBounded who word
              agent part =
          (menu).restrictPolicy initial horizon scheduler who
            (phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed source block low
              generation slotWeight slotNonnegative slotBounded who word) (some (past, view)) := by
      unfold phaseTimingWordComponent
      obtain ⟨identify, same⟩ := freeKeyedComponent_of_not_free (free := isFree) (keyed := isKeyed)
        (key := poolKey) _ _ _ (agent := agent) notFree
      rw [same part, keyedComponent_of_not_keyed _ _ (fun owned => keyed owned.1)]
      simp only [agent, dite_true, cast_eq]
      rfl
    have prescribed (part : Parts (pool agent)) :
        phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed source 0 le_rfl (by norm_num) slotWeight slotNonnegative slotBounded agent
            part =
        phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
          wellFormed source 0 le_rfl (by norm_num) slotWeight slotNonnegative slotBounded who
            (some (past, view)) := by
      unfold phaseTimingComponent
      obtain ⟨identify, same⟩ := freeKeyedComponent_of_not_free (free := isFree) (keyed := isKeyed)
        (key := poolKey) _ _ _ (agent := agent) notFree
      rw [same part, keyedComponent_of_not_keyed _ _ (fun owned => keyed owned.1)]
    have covered (move : Option (CommitRecoveryMove Player L)) :
        phaseRecoveryBindingResponse setup mode runtime leaks who event payload binding serial
          move ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
      dsimp only [phaseRecoveryBindingResponse]
      split
      · exact PhaseCount.silence_onePacket runtime leaks bounds who past view
      · exact offered _
    have canonicalLaw : phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed
        source who event payload binding past view =
      phaseRecoveryBindingLaw setup mode runtime leaks wellFormed source who event payload binding
        serial (phaseSourceView? setup mode runtime leaks who event view) := by
      unfold phaseRecoveryBindingPolicy
      simp only [selected, ite_eq_left covered]
    refine ⟨kernel, ?_, ?_⟩
    · intro plan word
      rw [word_member_apply, dite_eq_left played, prescribedWord,
        restricted _ (phaseCommitWordPolicy_covered setup mode runtime leaks bounds wellFormed
          source block low generation slotWeight slotNonnegative slotBounded who word)]
      rw [phaseCommitWordPolicy_binding setup mode runtime leaks bounds wellFormed source block
        low generation slotWeight slotNonnegative slotBounded who word control.execution valid
          event payload binding request inside address]
      exact canonical (block.wordAction who (event.val - low) word)
    · intro part
      rw [prescribed, phaseSourcePerturbedStrategy, mix_zero, mix_map]
      change mix slotWeight slotNonnegative slotBounded
        ((((menu).restrictPolicy initial horizon scheduler who
          (phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed source who))
            (some (past, view))).map (fun choice => choice.1.getD ⟨none⟩))
        ((((menu).restrictPolicy initial horizon scheduler who
          (phaseSourcePolicy setup mode runtime leaks bounds wellFormed source who))
            (some (past, view))).map (fun choice => choice.1.getD ⟨none⟩)) =
          sourceLaw.bind (kernel part)
      rw [restricted _ (phaseSourceSlotPolicy_covered setup mode runtime leaks bounds wellFormed
        source who), restricted _ (phaseSourcePolicy_covered setup mode runtime leaks bounds
          wellFormed source who)]
      rw [phaseSourceSlotPolicy_binding setup mode runtime leaks bounds wellFormed source
        control.execution valid who event payload binding request,
        phaseSourcePolicy,
        phasePolicyDispatch_binding setup mode runtime leaks bounds _ control.execution valid who
          event payload binding request, canonicalLaw]
      exact word_response_law setup mode runtime leaks bounds wellFormed source who event payload
        binding serial past view slotWeight slotNonnegative slotBounded sourceLaw id (PMF.map_id _)

end Vegas
