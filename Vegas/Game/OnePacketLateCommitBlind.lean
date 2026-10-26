/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateCommitFailure
import GameTheoryExtensions.Math.Probability.ProductDecorrelation

/-! # Uniform errors over late-commitment sites

The newest entry of an operational record is the operational state of the
history's state (`Vegas.operationalRecord_headD`), and every history of a
decision site with a pending event is a prefix of the site's rank
(`Vegas.ordered_of_site`). Errors vanishing at each of the finitely many sites
give one vanishing error for all of them (`Vegas.exists_uniform_of_sites`,
`Vegas.exists_uniform_decorrelation`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler

omit [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- The newest entry of an operational record is the operational state of the
history's state. -/
theorem operationalRecord_headD {state : (application setup runtime leaks).ProtocolState}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state) :
    (operationalRecord setup runtime leaks bounds horizon scheduler trace).headD
        (operationalState setup runtime leaks none) = operationalState setup runtime leaks state :=
  match trace with
  | .start => rfl
  | .extend _ _ _ _ => rfl

omit [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- Every history of a decision site of `who` with a pending event is a prefix of
the site's rank. -/
theorem ordered_of_site {who : Player} {site : (onePacketN).InformationSite who}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    (history : (onePacketN).InformationHistory who site.1) :
    ∃ remaining execution, history.1.state = some ⟨remaining, some who, execution⟩ ∧
      execution.recall who = past ∧ execution.observe (application setup runtime leaks) who = view ∧
      execution.application.config.cut.IsPrefix (siteRank (runtime := runtime) site.1) := by
  obtain ⟨remaining, execution, current, recallEq, observeEq⟩ :=
    state_of_site setup runtime leaks bounds horizon scheduler atSite history
  refine ⟨remaining, execution, current, recallEq, observeEq, ?_⟩
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      (current ▸ history.1.trace)
  obtain ⟨found, foundOrdered, _⟩ := pendingAt_history (runtime := runtime) rawTrace
  have rankEq : siteRank (runtime := runtime) site.1 = found := by
    rw [atSite, ← observeEq]
    change (execution.application.config.history.map EventGraph.Completion.event).length = found
    rw [List.length_map]
    exact history_length_of_isPrefix _ foundOrdered
  exact rankEq ▸ foundOrdered

omit [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
open Classical Filter in
/-- **Uniform errors from errors at each site.** For a property of errors at a
site that weakens as the error grows, if every site satisfying a condition has
a vanishing sequence of errors satisfying the property, then one vanishing
sequence serves every such site: the sum over the finitely many agents. -/
theorem exists_uniform_of_sites
    (property : ℕ → ∀ who, (onePacketN).InformationSite who → ℝ → Prop)
    (mono : ∀ n who site first second, first ≤ second → property n who site first →
      property n who site second)
    (condition : ∀ who, (onePacketN).InformationSite who → Prop)
    (perSite : ∀ who (site : (onePacketN).InformationSite who), condition who site →
      ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧ ∀ n, property n who site (error n)) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who), condition who site →
        property n who site (error n) := by
  let agentError := fun (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
      (n : ℕ) =>
    if present : ∃ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
        condition agent.1 ⟨agent.2.1, decision⟩ then
      |(perSite agent.1 ⟨agent.2.1, present.1⟩ present.2).choose n| else 0
  refine ⟨fun n => ∑ agent, agentError agent n, ?_, ?_⟩
  · rw [show (0 : ℝ) = ∑ _agent : (onePacketN).InformationAgent (onePacketN).playedInformation,
      (0 : ℝ) by simp]
    refine tendsto_finsetSum _ fun agent _ => ?_
    by_cases present : ∃ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
        condition agent.1 ⟨agent.2.1, decision⟩
    · simp only [agentError, present, ↓reduceDIte]
      simpa using (perSite agent.1 ⟨agent.2.1, present.1⟩ present.2).choose_spec.1.abs
    · simp only [agentError, present, ↓reduceDIte]
      exact tendsto_const_nhds
  · intro n who site holds
    have present : ∃ decision : (onePacketN).IsDecisionInfo ((onePacketN).agentAt site).1
        ((onePacketN).agentAt site).2.1,
        condition ((onePacketN).agentAt site).1 ⟨((onePacketN).agentAt site).2.1, decision⟩ :=
      ⟨site.2, holds⟩
    have nonneg : ∀ agent, 0 ≤ agentError agent n := fun agent => by
      simp only [agentError]
      split
      · exact abs_nonneg _
      · exact le_rfl
    have single := Finset.single_le_sum (f := fun agent => agentError agent n)
      (fun agent _ => nonneg agent) (Finset.mem_univ ((onePacketN).agentAt site))
    have atSite : agentError ((onePacketN).agentAt site) n =
        |(perSite who site holds).choose n| := by
      simp only [agentError, present, ↓reduceDIte]
    have spec := (perSite who site holds).choose_spec.2 n
    exact mono n who site _ _ ((le_abs_self _).trans (atSite ▸ single)) spec

omit [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
open Filter in
/-- **Uniform decorrelation.** If at every site satisfying a condition the
beliefs decorrelate the operational records and the decoded points up to a
vanishing error, one vanishing error serves every such site. -/
theorem exists_uniform_decorrelation
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (condition : ∀ who, (onePacketN).InformationSite who → Prop)
    (perSite : ∀ who (site : (onePacketN).InformationSite who), condition who site →
      ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧ ∀ n,
        BeliefDecorrelated ((targetSequence n).belief who site)
          (fun history => operationalRecord setup runtime leaks bounds horizon scheduler
            history.1.trace)
          (fun history => nativeDecodedState setup runtime leaks history.1.state) (error n)) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who), condition who site →
        BeliefDecorrelated ((targetSequence n).belief who site)
          (fun history => operationalRecord setup runtime leaks bounds horizon scheduler
            history.1.trace)
          (fun history => nativeDecodedState setup runtime leaks history.1.state) (error n) :=
  exists_uniform_of_sites setup runtime leaks bounds horizon scheduler
    (fun n who site error => BeliefDecorrelated ((targetSequence n).belief who site)
      (fun history => operationalRecord setup runtime leaks bounds horizon scheduler
        history.1.trace)
      (fun history => nativeDecodedState setup runtime leaks history.1.state) error)
    (fun _ _ _ _ _ le decorrelated => decorrelated.mono le) condition perSite

end Vegas
