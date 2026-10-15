/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCallbackContinuation
import GameTheoryExtensions.Analysis.Protocol.SuccessRanking

/-! # Original assessment fibers and entire physical callback continuations -/

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
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "P" => phaseApplication runtime leaks
local notation "M" => menu.information initial horizon scheduler
local notation "E" => menu.protocol initial horizon scheduler

open Classical in
/-- The actual local value averages the original full-history belief, the
installed response lottery and the original entire physical continuation.
No source posterior or continuation identification is assumed. -/
theorem phase_localValue_eq_response_continuation
    (assessment : (M).BehavioralAssessment) (who : Player) (site : (M).InformationSite who)
    (law : PMF ((M).Choice who site.1))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) (B : ℝ) (nonnegative : 0 ≤ B)
    (utilityBound : ∀ terminal owner, |utility terminal owner| ≤ B)
    (excludedBound : |excludedPayoff who| ≤ B) :
    localValue (2 * horizon + 1) (fun final : (E).History => final.state)
      (phaseExclusionBase setup mode runtime leaks utility excludedPayoff) assessment site law =
      expect (assessment.belief who site) (fun history => expect law (fun choice =>
        expect (match history.1.state with
          | none => PMF.pure none
          | some control => (P).finish initial horizon scheduler
              ((menu).decodeProfile initial horizon scheduler assessment.strategy)
              (some ⟨control.remaining, none,
                control.execution.respond (P) who (choice.1.getD ⟨none⟩)⟩))
          (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
            final who))) := by
  classical
  let payoff := fun final =>
    phaseExclusionBase setup mode runtime leaks utility excludedPayoff final who
  let updated := Profile.update (sig := (M).behavioralSignature) assessment.strategy who
    ((assessment.strategy who).withLaw site.1 law)
  have payoffBound : ∀ final, |payoff final| ≤ B := by
    intro final
    have interval := phaseExclusionBase_mem_Icc setup mode runtime leaks utility excludedPayoff
      (fun _ => -B) (fun _ => B) (fun terminal owner => (abs_le.mp
        (utilityBound terminal owner)).1)
      (fun terminal owner => (abs_le.mp (utilityBound terminal owner)).2) final who
    have excludedLower := (abs_le.mp excludedBound).1
    have excludedUpper := (abs_le.mp excludedBound).2
    apply abs_le.mpr
    simpa only [min_eq_right excludedLower, min_eq_right (neg_nonpos.mpr nonnegative),
      max_eq_right excludedUpper, max_eq_right nonnegative, Set.mem_Icc, payoff] using interval
  rw [localValue_eq_expect_localRun]
  change expect ((assessment.belief who site).bind fun history =>
    (M).runBehavioralFrom updated (2 * horizon + 1) history.1)
      (fun final => payoff final.state) = _
  have tower := expect_bind_tower_bounded (assessment.belief who site)
    (fun history : (M).InformationHistory who site.1 =>
      (M).runBehavioralFrom updated (2 * horizon + 1) history.1)
    (fun final : (E).History => payoff final.state) (fun final => payoffBound final.state)
  rw [tower]
  apply expect_congr_on_support
  intro history _supported
  have active := InformationModel.InformationSite.active (M) site history
  change (P).actor history.1.state = some who at active
  cases stateEq : history.1.state with
  | none => simp only [stateEq, ReactiveApplication.actor] at active; cases active
  | some control =>
      have acting : control.actor = some who := by
        simpa only [stateEq, ReactiveApplication.actor, Option.bind_some] using active
      rcases control with ⟨remaining, actor, execution⟩
      dsimp only at acting
      subst actor
      have bounded := (P).trace_bound initial horizon scheduler
        ((menu).toRawTrace initial horizon scheduler history.1.trace)
      rw [(menu).toRawTrace_length] at bounded
      have enough : (P).rank horizon history.1.state ≤ 2 * horizon + 1 := by omega
      have row := (menu).run_local_law_finish_of_information initial horizon scheduler
        assessment.strategy history.1 who remaining execution stateEq site.1 history.2 law
          (2 * horizon) enough
      calc
        _ = expect (((M).runBehavioralFrom updated (2 * horizon + 1) history.1).map
            (fun final : (E).History => final.state)) payoff :=
          (expect_map (fun final : (E).History => final.state) _ payoff).symm
        _ = _ := by
          rw [row, expect_bind_tower_bounded _ _ payoff payoffBound, expect_map]
          rfl

end Vegas
