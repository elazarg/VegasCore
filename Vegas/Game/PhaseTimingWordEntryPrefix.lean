/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordPlan
import Vegas.Pending.PhaseEntryOwnRecall

/-! # Original source words at genuine first-attempt prefixes

The original entry and full timing plans remain tagged through the existing
physical runner. Owned word kernels use only owned entry views; entry mixing
is retained rather than replaced by independence across hidden entries.
-/

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
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information initial
    horizon scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
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
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

variable {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
  (fallback : (who : Player) →
    ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon scheduler).Policy
      who)
  (wellFormed : setup.WellFormed) (source : setup.commitRecoveryModel.BehavioralAssessment)
  (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)

local notation "family" => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial
  horizon scheduler bound fallback wellFormed source block low generation slotWeight
    slotNonnegative slotBounded

local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound

/-- Away from its addressed attempt, the actual complete timing-plan member
cannot read the selected source word. It may still read the original plan. -/
theorem phaseTimingWordPlanPolicy_eq_of_other_attempt
    (plan : (p : Pool) → Parts p) (who : Player) (first second : DecisionView who Δ)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (different : view.application.2.attempt ≠ ⟨low, generation⟩) :
    family plan who first past view = family plan who second past view := by
  obtain ⟨law, constant⟩ | canonical | ⟨option, timed⟩ := phaseTimingWordPlanPolicy_cases setup mode
    runtime leaks bounds initial horizon scheduler bound fallback wellFormed source block low
      generation slotWeight slotNonnegative slotBounded plan who past view
  · exact (constant first).trans (constant second).symm
  · rw [canonical first, canonical second]
    obtain ⟨law, constant⟩ | ⟨event, payload, binding, inside, address, law⟩ :=
      phaseCommitWordPolicy_cases setup mode runtime leaks bounds wellFormed source block low
        generation slotWeight slotNonnegative slotBounded who past view
    · exact (constant first).trans (constant second).symm
    · exact False.elim (different address)
  · rw [timed first, timed second]
    obtain ⟨law, constant⟩ | ⟨event, payload, binding, inside, address, law⟩ :=
      phaseCommitTimingWordPolicy_cases setup mode runtime leaks bounds wellFormed source block low
        generation slotWeight slotNonnegative slotBounded option who past view
    · exact (constant first).trans (constant second).symm
    · exact False.elim (different address)

local instance timingWordEntryPoolFintype :
    Fintype (FreeKeyedPool isFree isKeyed poolKey) := Fintype.ofFinite _

open Classical in
/-- At a genuine first-attempt prefix, the original complete word remains
independent of the full updated timing plan. This is the actual immutable
family's posterior on the permanent recall; no entry recall is reset and no
independence of an outer hidden-entry mixture is asserted. -/
theorem phaseTimingWordPlanPolicy_entry_joint_of_history
    (initialized : ∀ state ∈ initial.support, state.Ordered)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some control))
    (address : control.execution.application.attempt = ⟨low, generation⟩) :
    ∃ (entry : (app).Control)
      (entryTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
        scheduler).Trace (some entry)),
      GameTheory.Protocol.ExecutionProtocol.TracePrefix entryTrace trace ∧
        entry.execution.application.attempt = ⟨low, generation⟩ ∧
      ∀ (weights : (p : Pool) → PMF (Parts p)) (who : Player)
        (prior : PMF (DecisionView who Δ)),
        let reference := prior.support_nonempty.choose
        let planLaw := independentProduct weights
        let original := planLaw.bind fun plan => prior.map (Prod.mk plan)
        let members := fun memory => family memory.1 who memory.2
        let plans := (app).policyMixture planLaw (fun plan => family plan who reference)
        ((app).policyMixture original members).posterior (entry.execution.recall who) =
          (plans.posterior (entry.execution.recall who)).bind
            (fun plan => prior.map (Prod.mk plan)) := by
  obtain ⟨entry, entryTrace, retained, same, _idle, _origin, fresh⟩ :=
    phase_attempt_entry_prefix runtime leaks (PhaseCount.onePacketMenu runtime leaks bounds) initial
      initialized horizon scheduler control trace
  refine ⟨entry, entryTrace, retained, same.trans address, ?_⟩
  intro weights who prior reference planLaw original members plans
  let past := entry.execution.recall who
  let split := Equiv.prodComm ((p : Pool) → Parts p) (DecisionView who Δ)
  let pairMembers := fun pair : DecisionView who Δ × ((p : Pool) → Parts p) =>
    family pair.2 who pair.1
  let baseline := fun plan => family plan who reference
  have splitLaw : original.map split = prior.bind (fun word => planLaw.map (Prod.mk word)) := by
    simp only [original, PMF.map_bind, PMF.map_comp, Function.comp_def]
    change (planLaw.bind (fun plan => prior.bind fun word => PMF.pure (word, plan))) =
      prior.bind (fun word => planLaw.bind fun plan => PMF.pure (word, plan))
    exact PMF.bind_comm ..
  have moved := (app).policyMixture_posterior_map original split pairMembers past
  have sameMembers : (fun memory => pairMembers (split memory)) = members := rfl
  rw [sameMembers, splitLaw] at moved
  have product := (app).policyMixture_posterior_independent_left prior planLaw pairMembers
    baseline past (by
      intro before record recorded word plan
      have member : record ∈ past := by
        obtain ⟨tail, equal⟩ := recorded
        rw [← equal]
        simp only [List.mem_append, List.mem_singleton]
        exact Or.inl (Or.inr trivial)
      exact phaseTimingWordPlanPolicy_eq_of_other_attempt setup mode runtime leaks bounds initial
        horizon scheduler bound fallback wellFormed source block low generation slotWeight
          slotNonnegative slotBounded plan who word reference before record.beforeView
            (fun equal => fresh who record member (equal.trans (same.trans address).symm)))
  have projected := congrArg (PMF.map split.symm) (moved.trans product)
  simp only [PMF.map_comp, Equiv.symm_apply_apply, PMF.map_bind,
    Function.comp_def] at projected
  change (((app).policyMixture original members).posterior past).map id = _ at projected
  rw [PMF.map_id] at projected
  refine projected.trans ?_
  change (prior.bind (fun word => (plans.posterior past).bind fun plan => PMF.pure (plan, word))) =
    (plans.posterior past).bind (fun plan => prior.bind fun word => PMF.pure (plan, word))
  exact PMF.bind_comm ..

end Vegas
