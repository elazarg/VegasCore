/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalFlagMass
import Vegas.Game.PhaseProposalGenuineSupport
import Vegas.Game.PhaseProposalReferenceStrategy
import Vegas.Game.PhaseAttemptContinuation
import Interaction.ReactiveMenuLikelihood
import Interaction.ReactiveResponseKernel
import GameTheoryExtensions.Analysis.Protocol.SupportedChoiceContinuation
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Uniform future flag error after an arbitrary literal current response -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (complete : leaks = MessageNetwork.completePendingObservation)
  (covered : bounds.CoversOutputValues)
  (maximal : plan.phases.IsChain fun first last =>
    first.kind ≠ last.kind ∨ first.kind = .sample)
  (values : ∀ who (key : setup.ProposalRecoveryComponent who),
    PMF (setup.CommitRecoveryValueChoice who key.1))
  (fullValues : ∀ who key, FullSupport (values who key))
  (rates : PhaseProposalRates)
  (waitingPositive : 0 < rates.waiting.val) (waitingBelow : rates.waiting.val < 1)
  (slotsPositive : 0 < rates.slots.val)
  (badPositive : 0 < rates.badPreparation.val) (badBelow : rates.badPreparation.val < 1)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => PMF.map (PhaseRuntimeState.initial plan)
  (PMF.map encodeInputs setup.initialLaw)
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds)
  (PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw))
    horizon scheduler
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds)
  (PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw))
    horizon scheduler
local notation "clean" => fun who =>
  ReactiveApplication.ResponseMenu.restrictPolicy (PhaseCount.onePacketMenu runtime leaks bounds)
    (PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw))
      horizon scheduler who
  (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who)
local notation "noisy" => phaseProposalReferenceStrategy setup mode runtime leaks bounds plan
  initial horizon scheduler values rates

include complete covered maximal fullValues waitingPositive waitingBelow slotsPositive
  badPositive badBelow

private theorem phaseProposal_restricted_choice_retained
    (history : (E).History) (who : Player)
    (choice : (N).Choice who ((N).infoOf who history.trace)) :
    rates.keep * ((clean who ((N).infoOf who history.trace)) choice).toReal ≤
      ((noisy who ((N).infoOf who history.trace)) choice).toReal := by
  classical
  have inactive (selected : (N).Choice who none) :
      rates.keep * (((clean who none) selected).toReal) ≤
        ((noisy who none) selected).toReal := by
    have same : selected = ⟨none, rfl⟩ := Subtype.ext selected.property
    subst selected
    simpa only [phaseProposalReferenceStrategy, ReactiveApplication.ResponseMenu.restrictPolicy,
      PMF.pure_apply, ite_true, ENNReal.toReal_one, mul_one] using rates.keep_le_one
  revert choice
  rcases history with ⟨state, trace⟩
  have observed := (menu).info initial horizon scheduler who trace
  change (N).infoOf who trace = (app).observe who state at observed
  cases state with
  | none =>
      change (N).infoOf who trace = none at observed
      rw [observed]
      exact inactive
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      by_cases active : actor = some who
      · subst actor
        have info : (N).infoOf who trace =
            some (execution.recall who, execution.observe app who) := by
          simpa only [ReactiveApplication.observe, ite_true] using observed
        rw [info]
        intro choice
        obtain ⟨response, _available, selected⟩ := choice.property
        have full := phaseProposalBaseClasses_fullSupport_of_counted setup mode runtime leaks
          bounds plan complete covered maximal values fullValues rates waitingPositive waitingBelow
            slotsPositive badPositive badBelow horizon scheduler remaining who execution (by
              have same : initial = setup.initialLaw.map (fun draw =>
                  PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
              exact same ▸ trace)
        have cleanAtom : ((clean who (some (execution.recall who,
            execution.observe app who))) choice).toReal =
            (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who
              (execution.recall who) (execution.observe app who) response).toReal := by
          rw [← pmf_map_apply_of_injective _ Subtype.val_injective choice, selected,
            (menu).restrictPolicy_atom initial horizon scheduler who _ _ _ response
              (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values who
                (execution.recall who) (execution.observe app who))]
        have noisyAtom : ((noisy who (some (execution.recall who,
            execution.observe app who))) choice).toReal =
            (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates who
              (execution.recall who) (execution.observe app who) response).toReal := by
          rw [phaseProposalReferenceStrategy,
            ← pmf_map_apply_of_injective _ Subtype.val_injective choice, selected,
            (menu).restrictPolicy_atom initial horizon scheduler who _ _ _ response
              (phaseProposalReferencePolicy_covered setup mode runtime leaks bounds plan values
                rates who (execution.recall who) (execution.observe app who))]
        rw [cleanAtom, noisyAtom]
        exact phaseProposalReferencePolicy_retained setup mode runtime leaks bounds plan values
          rates who (execution.recall who) (execution.observe app who) full response
      · have info : (N).infoOf who trace = none := by
          simpa only [ReactiveApplication.observe, ite_eq_right active] using observed
        rw [info]
        exact inactive

/-- Every authentic retained history, including debt, old pending packets
and earlier rare aliases, has the same uniform prospective flag bound. -/
theorem phaseProposal_future_flags_withinTV (history : (E).History) :
    PMF.WithinTV
      ((Fintype.card Player * (2 * horizon + 1) : Nat) * rates.flagBound)
      ((N).runBehavioralTerminalFrom ((menu).bounded initial horizon scheduler).wellFoundedHistories
        clean history)
      ((N).runBehavioralTerminalFrom ((menu).bounded initial horizon scheduler).wellFoundedHistories
        noisy history) := by
  rw [(N).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
      ((menu).bounded initial horizon scheduler).wellFoundedHistories
      ((menu).bounded initial horizon scheduler),
    (N).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
      ((menu).bounded initial horizon scheduler).wellFoundedHistories
      ((menu).bounded initial horizon scheduler)]
  apply PMF.WithinTV.mono
    ((one_sub_pow_le_mul rates.keep_nonnegative _).trans
      (mul_le_mul_of_nonneg_left rates.missing_keep_le (Nat.cast_nonneg _)))
  apply (N).runBehavioralFrom_withinTV_of_supported_choices clean noisy rates.keep
    rates.keep_nonnegative rates.keep_le_one history
  intro _elapsed later _supported who choice
  exact phaseProposal_restricted_choice_retained setup mode runtime leaks bounds plan complete
    covered maximal values fullValues rates waitingPositive waitingBelow slotsPositive badPositive
      badBelow horizon scheduler later who choice

/-- The current law and its genuine response history kernel remain literal.
The uniform error applies after every response, before integrating that law;
no current-response probability or information reach occurs in the bound. -/
theorem phaseProposal_future_flags_after_current_law
    (law : PMF (app).Action) (kernel : (app).Action → PMF (E).History) :
    PMF.WithinTV
      ((Fintype.card Player * (2 * horizon + 1) : Nat) * rates.flagBound)
      ((law.bind kernel).bind fun history => (N).runBehavioralTerminalFrom
        ((menu).bounded initial horizon scheduler).wellFoundedHistories clean history)
      ((law.bind kernel).bind fun history => (N).runBehavioralTerminalFrom
        ((menu).bounded initial horizon scheduler).wellFoundedHistories noisy history) := by
  apply PMF.WithinTV.bind_right
  intro history _supported
  exact phaseProposal_future_flags_withinTV setup mode runtime leaks bounds plan complete covered
    maximal values fullValues rates waitingPositive waitingBelow slotsPositive badPositive badBelow
      horizon scheduler history

/-- The same bound holds for the actual physical finish runner. The history
is used only for genuine-prefix support; no fresh-boundary premise is needed. -/
theorem phaseProposal_finish_future_flags_withinTV (history : (E).History) :
    PMF.WithinTV
      ((Fintype.card Player * (2 * horizon + 1) : Nat) * rates.flagBound)
      ((app).finish initial horizon scheduler
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) history.state)
      ((app).finish initial horizon scheduler
        (phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates)
          history.state) := by
  have cleanDecode : (menu).decodeProfile initial horizon scheduler clean =
      phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values := by
    funext who
    exact (menu).decode_restrictPolicy_of_covered initial horizon scheduler who _
      (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values who)
  have noisyDecode : (menu).decodeProfile initial horizon scheduler noisy =
      phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates := by
    funext who
    exact (menu).decode_restrictPolicy_of_covered initial horizon scheduler who _
      (phaseProposalReferencePolicy_covered setup mode runtime leaks bounds plan values rates who)
  have enough : (app).rank horizon history.state ≤ 2 * horizon + 1 := by
    have bound := (app).trace_bound initial horizon scheduler
      ((menu).toRawTrace initial horizon scheduler history.trace)
    omega
  have close := (phaseProposal_future_flags_withinTV setup mode runtime leaks bounds plan complete
    covered maximal values fullValues rates waitingPositive waitingBelow slotsPositive badPositive
      badBelow horizon scheduler history).map History.state
  rw [(N).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
      ((menu).bounded initial horizon scheduler).wellFoundedHistories
      ((menu).bounded initial horizon scheduler),
    (N).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
      ((menu).bounded initial horizon scheduler).wellFoundedHistories
      ((menu).bounded initial horizon scheduler),
    (menu).run_eq_finish initial horizon scheduler clean _ history enough,
    (menu).run_eq_finish initial horizon scheduler noisy _ history enough,
    cleanDecode, noisyDecode] at close
  exact close

/-- Reference CURRENT noise is removed in a separate comparison. Its
continuation kernel is arbitrary and can keep all strict-future flags. -/
theorem phaseProposal_current_flags_after_kernel
    (remaining : Nat) (who : Player) (execution : (app).Execution)
    (trace : (E).Trace (some ⟨remaining, some who, execution⟩))
    {Result : Type*} (kernel : (app).Action → PMF Result) :
    PMF.WithinTV rates.flagBound
      ((phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who
        (execution.recall who) (execution.observe app who)).bind kernel)
      ((phaseProposalReferencePolicy setup mode runtime leaks bounds plan values rates who
        (execution.recall who) (execution.observe app who)).bind kernel) := by
  have full := phaseProposalBaseClasses_fullSupport_of_counted setup mode runtime leaks bounds plan
    complete covered maximal values fullValues rates waitingPositive waitingBelow slotsPositive
      badPositive badBelow horizon scheduler remaining who execution (by
        have same : initial = setup.initialLaw.map (fun draw =>
            PhaseRuntimeState.initial plan (encodeInputs draw)) := PMF.map_comp _ _ _
        exact same ▸ trace)
  apply PMF.WithinTV.mono rates.missing_keep_le
  apply PMF.WithinTV.of_domination _ _ rates.keep rates.keep_le_one
  intro result
  exact prob_bind_ge_mul _ _ rates.keep
    (phaseProposalReferencePolicy_retained setup mode runtime leaks bounds plan values rates who
      (execution.recall who) (execution.observe app who) full) kernel result

omit complete covered maximal fullValues waitingPositive waitingBelow slotsPositive
  badPositive badBelow [Fintype Player] in
private theorem phaseProposal_payoff_bounded
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (who : Player) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (utilityBound : ∀ terminal owner, |utility terminal owner| ≤ bound)
    (excludedBound : |excludedPayoff who| ≤ bound) :
    ∀ state, -bound ≤ phaseExclusionBase setup mode runtime leaks utility excludedPayoff
        state who ∧
      phaseExclusionBase setup mode runtime leaks utility excludedPayoff state who ≤ bound := by
  intro state
  have interval := phaseExclusionBase_mem_Icc setup mode runtime leaks utility excludedPayoff
    (fun _ => -bound) (fun _ => bound)
    (fun terminal owner => (abs_le.mp (utilityBound terminal owner)).1)
    (fun terminal owner => (abs_le.mp (utilityBound terminal owner)).2) state who
  have lower := (abs_le.mp excludedBound).1
  have upper := (abs_le.mp excludedBound).2
  simpa only [min_eq_right lower, min_eq_right (neg_nonpos.mpr nonnegative),
    max_eq_right upper, max_eq_right nonnegative, Set.mem_Icc] using interval

/-- The actual response kernel is constructed at the supplied counted
callback. Removing two strict-future flag families and the reference's CURRENT
flags changes the gain by one uniform explicit error. The arbitrary current
law is unchanged in both of its continuations. -/
theorem phaseProposal_current_gain_flag_error
    (remaining : Nat) (who : Player) (execution : (app).Execution)
    (trace : (E).Trace (some ⟨remaining, some who, execution⟩))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (utilityBound : ∀ terminal owner, |utility terminal owner| ≤ bound)
    (excludedBound : |excludedPayoff who| ≤ bound) :
    let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
    ∃ kernel : (app).Action → PMF (E).History,
      (∀ profile : ∀ owner, (N).BehavioralPolicy owner,
        (N).runBehavioralFrom profile 1 ⟨some ⟨remaining, some who, execution⟩, trace⟩ =
          ((menu).decodeProfile initial horizon scheduler profile who (execution.recall who)
            (execution.observe app who)).bind kernel) ∧
      (∀ profile : ∀ owner, (N).BehavioralPolicy owner, ∀ action,
        action ∈ ((menu).decodeProfile initial horizon scheduler profile who
          (execution.recall who) (execution.observe app who)).support →
        (kernel action).map History.state =
          PMF.pure (some ⟨remaining, none, execution.respond app who action⟩)) ∧
      let payoff := fun final : (E).History => phaseExclusionBase setup mode runtime leaks utility
        excludedPayoff final.state who
      let cleanValue := fun law : PMF (app).Action =>
        expect ((law.bind kernel).bind fun history =>
          (N).runBehavioralTerminalFrom certificate clean history) payoff
      let noisyValue := fun law : PMF (app).Action =>
        expect ((law.bind kernel).bind fun history =>
          (N).runBehavioralTerminalFrom certificate noisy history) payoff
      let referenceClean := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan
        values who (execution.recall who) (execution.observe app who)
      let referenceNoisy := phaseProposalReferencePolicy setup mode runtime leaks bounds plan
        values rates who (execution.recall who) (execution.observe app who)
      ∀ law : PMF (app).Action,
        (noisyValue law - noisyValue referenceNoisy) -
            (cleanValue law - cleanValue referenceClean) ≤
          (2 * (Fintype.card Player * (2 * horizon + 1) : Nat) + 1) *
            rates.flagBound * (2 * bound) := by
  intro certificate
  obtain ⟨kernel, responseLaw, states⟩ :=
    (menu).exists_response_history_kernel initial horizon scheduler clean who remaining execution
      trace
  refine ⟨kernel, responseLaw, states, ?_⟩
  intro payoff cleanValue noisyValue referenceClean referenceNoisy law
  have bounded (final : (E).History) : -bound ≤ payoff final ∧
      payoff final ≤ -bound + (2 * bound) := by
    have interval := phaseProposal_payoff_bounded setup mode runtime leaks utility excludedPayoff
      who bound nonnegative utilityBound excludedBound final.state
    exact ⟨interval.1, by linarith [interval.2]⟩
  have future (currentLaw : PMF (app).Action) :=
    phaseProposal_future_flags_after_current_law setup mode runtime leaks bounds plan complete
      covered maximal values fullValues rates waitingPositive waitingBelow slotsPositive badPositive
        badBelow horizon scheduler currentLaw kernel
  have alternative := (future law).symm.expect_sub_le payoff (-bound) (2 * bound)
    (fun final _ => bounded final)
  have reference := (future referenceNoisy).expect_sub_le payoff (-bound) (2 * bound)
    (fun final _ => bounded final)
  have current := phaseProposal_current_flags_after_kernel setup mode runtime leaks bounds plan
    complete covered maximal values fullValues rates waitingPositive waitingBelow slotsPositive
      badPositive badBelow horizon scheduler remaining who execution trace
        (fun response => (kernel response).bind fun history =>
          (N).runBehavioralTerminalFrom certificate clean history)
  have currentValue := current.expect_sub_le payoff (-bound) (2 * bound)
    (fun final _ => bounded final)
  simp only [← PMF.bind_bind] at currentValue
  change noisyValue law - cleanValue law ≤ _ at alternative
  change cleanValue referenceNoisy - noisyValue referenceNoisy ≤ _ at reference
  change cleanValue referenceClean - cleanValue referenceNoisy ≤ _ at currentValue
  push_cast at alternative reference ⊢
  nlinarith [alternative, reference, currentValue]

end Vegas
