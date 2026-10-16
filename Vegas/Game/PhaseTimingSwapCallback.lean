/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingSwapOpening
import Vegas.Game.PhaseRecoveryValuePlan
import Vegas.Pending.PhaseOpeningBindingPrefix
import Vegas.Pending.PhaseBindingMemoryCallback
import Vegas.Pending.PhaseSwapSymmetry
import Vegas.Pending.PhaseSwapInitialLaw
import Vegas.Pending.PhaseSwapCallback
import Interaction.ReactiveRecordedResponse

/-! # Actual nonbinding callback factors along guarded whole histories -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [histories : Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).History]
  [infos : ∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Pool" => FreeKeyedPool
  (fun agent : InformationModel.InformationAgent (N)
    (InformationModel.playedInformation (N)) =>
    PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent)))
  (fun agent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
  (fun agent => phaseTimingKey runtime leaks (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

omit [Fintype Player] histories infos in
private theorem fixed_request (swap : HiddenSwap (serviceGraph setup mode))
    (execution : (app).Execution)
    (guarded : PhaseSwapGuard runtime leaks swap (phaseSwapAllowed swap initial) execution)
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩) :
    RevealFixed swap execution.application.current.native event := by
  obtain ⟨phase, member, inside⟩ := request.2.1
  cases installed : execution.application.phases with
  | nil => simp only [installed, List.head?_nil, Option.not_mem_none] at member
  | cons current remaining =>
      simp only [installed, List.head?_cons, Option.mem_some_iff] at member
      subst phase
      exact guarded.active current remaining installed event inside request.2.2.1

/-- Every earlier actual callback other than an unsent binding has the same
whole fixed-plan response law across a guarded hidden swap. Its successful
opening, replay guard and swapped trace are derived from the whole history. -/
theorem phaseTimingPlanPolicy_nonbinding_swap_before_binding
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (fallback : (who : Player) → (N).Policy who)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p)
    (swap : HiddenSwap (serviceGraph setup mode))
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (expiry : ∀ event, swap.values.ExpiryFixed event)
    (remaining : Nat) (who : Player) (original : (app).Execution)
    (trace : (E).Trace (some ⟨remaining, some who, original⟩))
    (final : (app).Control) (finalTrace : (E).Trace (some final))
    (isPrefix : TracePrefix trace finalTrace)
    (guarded : PhaseSwapGuard runtime leaks swap (phaseSwapAllowed swap initial) final.execution)
    (bindingEvent : (serviceGraph setup mode).EventId) (bindingOwner : Player)
    (bindingPayload : L.Ty)
    (bindingOutput : (serviceGraph setup mode).outputLayout bindingEvent =
      .binding bindingOwner bindingPayload)
    (requested : final.execution.application.SeedRequest bindingOwner
      ⟨final.execution.application.attempt, bindingEvent⟩)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (nonbinding : ¬∃ event payload,
      (serviceGraph setup mode).outputLayout event = .binding who payload ∧
      original.application.SeedRequest who ⟨original.application.attempt, event⟩ ∧
      ∀ message ∈ (app).outputs (original.recall who),
        PhaseCount.event? message.payload ≠ some ⟨original.application.attempt, event⟩) :
    phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound fallback
        wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
          parts who (original.recall who) (original.observe app who) =
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound fallback
        wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
          parts who ((swap.phaseExecution original).recall who)
            ((swap.phaseExecution original).observe app who) := by
  classical
  have guardedBefore := swap.phaseSwapGuard_of_tracePrefix bounds plan inputs horizon scheduler
    _ final trace finalTrace isPrefix guarded bounded expiry
  let symmetry := phaseOnePacketSwapSymmetry bounds initial
    (phase_initial_support_invariant plan inputs) horizon scheduler swap
      (phaseSwapAllowed swap initial) (phase_initialClosed_swapAllowed swap plan inputs)
        bounded expiry
  have swappedTrace : (E).Trace (some ⟨remaining, some who, swap.phaseExecution original⟩) :=
    symmetry.mapTrace trace guardedBefore
  by_cases usable : ∃ coordinate, original.application.SeedRequest who coordinate ∧
      ∀ message ∈ (app).outputs (original.recall who),
        PhaseCount.event? message.payload ≠ some coordinate
  · obtain ⟨⟨attempt, event⟩, request, unsent⟩ := usable
    have address : attempt = original.application.attempt := request.1
    subst attempt
    cases node : nodeView (serviceGraph setup mode) event with
    | bind owner payload outputEq codeEq =>
        have ownerEq : owner = who := Option.some.inj
          (((EventCode.actor_cast outputEq _).symm.trans
            (congrArg EventCode.actor codeEq)).symm.trans request.2.2.2.1)
        subst owner
        exact (nonbinding ⟨event, payload, outputEq, request, unsent⟩).elim
    | resolve owner payload field checks outputEq codeEq =>
        have ownerEq : owner = who := Option.some.inj
          (((EventCode.actor_cast outputEq _).symm.trans
            (congrArg EventCode.actor codeEq)).symm.trans request.2.2.2.1)
        subst owner
        obtain ⟨value, stored⟩ := phase_opening_binding_success_before_binding runtime leaks bounds
          plan (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler
            _ final trace finalTrace isPrefix guarded.clear event who payload field checks
              outputEq codeEq node request.2.2.1 bindingEvent bindingOwner bindingPayload
                bindingOutput requested
        exact phaseTimingPlanPolicy_opening_swap setup mode runtime leaks bounds plan inputs
          horizon scheduler wellFormed source swap remaining who original trace swappedTrace event
            payload field checks outputEq codeEq node request
              (fixed_request setup mode runtime leaks plan inputs swap original guardedBefore
                who event request)
                unsent value stored (values payload value) bound fallback noise noiseNonnegative
                  noiseBounded slotWeight slotNonnegative slotBounded parts guardedBefore.clear
    | sample payload law outputEq codeEq =>
        have noOwner : (serviceGraph setup mode).actor? event = none :=
          (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
        have owned := request.2.2.2.1
        rw [noOwner] at owned
        cases owned
  · have swappedAbsent : ¬∃ coordinate,
        (swap.phaseExecution original).application.SeedRequest who coordinate ∧
        ∀ message ∈ (app).outputs ((swap.phaseExecution original).recall who),
          PhaseCount.event? message.payload ≠ some coordinate := by
      rintro ⟨coordinate, request, unsent⟩
      apply usable
      refine ⟨coordinate, request, ?_⟩
      change ∀ message ∈ (app).outputs ((original.recall who).map swap.phaseEntry),
        PhaseCount.event? message.payload ≠ some coordinate at unsent
      rwa [swap.phaseOutputs_entry] at unsent
    have firstMenu := PhaseCount.onePacketActions_eq_singleton_of_no_unsent runtime leaks bounds
      plan (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining who
        original trace usable
    have secondMenu := PhaseCount.onePacketActions_eq_singleton_of_no_unsent runtime leaks bounds
      plan (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining who
        (swap.phaseExecution original) swappedTrace swappedAbsent
    have forced (execution : (app).Execution)
        (singleton : PhaseCount.onePacketActions runtime leaks bounds who (execution.recall who)
          (execution.observe app who) = {⟨none⟩}) :
        phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative
            slotBounded parts who (execution.recall who) (execution.observe app who) =
              PMF.pure ⟨none⟩ := by
      apply pmf_eq_pure_of_support_subset_singleton
      intro action supported
      have offered := phaseTimingPlanPolicy_covered setup mode runtime leaks bounds initial horizon
        scheduler bound fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded parts who _ _ action supported
      change action ∈ PhaseCount.onePacketActions runtime leaks bounds who
        (execution.recall who) (execution.observe app who) at offered
      rw [singleton] at offered
      exact Finset.mem_singleton.mp offered
    exact (forced original firstMenu).trans (forced _ secondMenu).symm

/-- A literal occurrence in a whole owner recall supplies its genuine
callback, prefix, guarded swapped history and successful opening internally.
Its complete operational response factor is unchanged on the actual
input-restricted swap domain, allowing correlated original private cells. -/
theorem phaseTimingPlanPolicy_nonbinding_record_swap
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (fallback : (who : Player) → (N).Policy who)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p)
    (swap : HiddenSwap (serviceGraph setup mode))
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (expiry : ∀ event, swap.values.ExpiryFixed event)
    (final : (app).Control) (finalTrace : (E).Trace (some final))
    (guarded : PhaseSwapGuard runtime leaks swap (phaseSwapAllowed swap initial) final.execution)
    (bindingEvent : (serviceGraph setup mode).EventId) (bindingOwner : Player)
    (bindingPayload : L.Ty)
    (bindingOutput : (serviceGraph setup mode).outputLayout bindingEvent =
      .binding bindingOwner bindingPayload)
    (requested : final.execution.application.SeedRequest bindingOwner
      ⟨final.execution.application.attempt, bindingEvent⟩)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (who : Player) (past : List (app).PlayerEntry) (entry : (app).PlayerEntry)
    (later : List (app).PlayerEntry)
    (recalled : final.execution.recall who = past ++ entry :: later)
    (nonbinding : ¬∃ event payload,
      (serviceGraph setup mode).outputLayout event = .binding who payload ∧
      PhaseRuntimeState.requests entry.beforeView.application.2 who
        ⟨entry.beforeView.application.2.attempt, event⟩ ∧
      ∀ message ∈ (app).outputs past, PhaseCount.event? message.payload ≠
        some ⟨entry.beforeView.application.2.attempt, event⟩) :
    phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound fallback
        wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
          parts who past entry.beforeView entry.action =
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded parts who (past.map swap.phaseEntry) (swap.phaseView entry.beforeView)
            (swap.phaseAction entry.action) := by
  obtain ⟨before, prior, isPrefix, active, pastEq, viewed, offered⟩ :=
    (menu).recorded_response_at initial horizon scheduler final finalTrace who past entry later
      recalled
  have raw := (menu).toRawTrace initial horizon scheduler prior
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    raw
  have nonbindingBefore : ¬∃ event payload,
      (serviceGraph setup mode).outputLayout event = .binding who payload ∧
      before.execution.application.SeedRequest who ⟨before.execution.application.attempt, event⟩ ∧
      ∀ message ∈ (app).outputs (before.execution.recall who),
        PhaseCount.event? message.payload ≠ some ⟨before.execution.application.attempt, event⟩ := by
    rintro ⟨event, payload, outputEq, request, unsent⟩
    apply nonbinding
    refine ⟨event, payload, outputEq, ?_, ?_⟩
    · rw [viewed]
      exact (PhaseRuntimeState.requests_publicView _ valid _ _).mpr request
    · rw [viewed, ← pastEq]
      exact unsent
  have beforeEq : before = ⟨before.remaining, some who, before.execution⟩ := by
    cases before with
    | mk remaining actor execution => cases active; rfl
  let actual : (E).Trace (some ⟨before.remaining, some who, before.execution⟩) := beforeEq ▸ prior
  have actualPrefix : TracePrefix actual finalTrace := by
    dsimp only [actual]
    cases before with
    | mk remaining actor execution => cases active; exact isPrefix
  have laws := phaseTimingPlanPolicy_nonbinding_swap_before_binding setup mode runtime leaks
    bounds plan inputs horizon scheduler bound maximal wellFormed source fallback noise
      noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded parts swap bounded
        expiry before.remaining who before.execution actual final finalTrace actualPrefix
          guarded bindingEvent bindingOwner bindingPayload bindingOutput requested values
            nonbindingBefore
  rw [swap.observe_phaseExecution, pastEq, ← viewed] at laws
  change entry.action ∈ PhaseCount.onePacketActions runtime leaks bounds who past
    (before.execution.observe app who) at offered
  have fixed := swap.phaseAction_eq_of_nonbinding_callback bounds plan
    (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler before.remaining who
      before.execution actual nonbindingBefore entry.action (by
        simpa only [pastEq] using offered)
  rw [fixed]
  simpa only [HiddenSwap.phaseExecution, pastEq] using
    congrArg (fun law : PMF (app).Action => law entry.action) laws

end Vegas
