/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServiceTableRun

/-! # Focal interventions retain the original entry-conditioned service tables -/

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

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds

variable
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent (serviceGraph setup mode) → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
  (horizon : Nat)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds)
  (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds)
  (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
local notation "Q" => phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
local notation "P" => phaseCountServicePolicy setup mode runtime leaks bounds values choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
  slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
local notation "original" => independentProduct (fun _address : PhaseSeedAddress graph =>
  independentProduct (fun index : Fin horizon => PhaseCount.bindingServiceCoinLaw failure timing
    firstNonnegative firstBounded timingNonnegative timingBounded rawWeight rawNonnegative
      rawBounded (Fin.val index)))

/-- An arbitrary focal continuation is performed on the same complete entry
history. Foreign original tables have their genuine entry posteriors, and
averaging them gives the literal normalized foreign continuation. The unused
focal table keeps its genuine old posterior and has no effect on play. -/
theorem phaseCountServiceTapePolicy_table_continuation
    (certificate : (E).WellFoundedHistories) (stopped : (E).History → Prop)
    (entry : (E).History) (focal : Player) (focalPolicy : (N).BehavioralPolicy focal) :
    (independentProduct (fun who =>
      ((app).policyMixture original (fun table => Q table who)).posterior
        ((app).recallAt who entry.state))).bind (fun tables =>
      (N).runBehavioralUntil certificate
        (Function.update (fun who => (menu).restrictPolicy initial horizon scheduler who
          (Q (tables who) who)) focal focalPolicy) stopped entry) =
      (N).runBehavioralUntil certificate
        (Function.update (fun who => (menu).restrictPolicy initial horizon scheduler who (P who))
          focal focalPolicy) stopped entry := by
  classical
  let oldPosterior := fun who => ((app).policyMixture original
    (fun table => Q table who)).posterior ((app).recallAt who entry.state)
  let focalRaw := (app).decodePolicy
    ((menu).embedPolicy initial horizon scheduler focal focalPolicy)
  let priors := fun who => if who = focal then oldPosterior focal else original
  let members := fun (who : Player)
      (table : PhaseSeedAddress graph → Fin horizon → Bool × Bool) =>
    if who = focal then focalRaw else Q table who
  have covered : ∀ who table past view action, action ∈ (members who table past view).support →
      action ∈ (menu).actions who past view := by
    intro who table past view action supported
    by_cases same : who = focal
    · subst who
      simp only [members, ite_true] at supported
      exact (menu).decode_embedPolicy_covered initial horizon scheduler focal focalPolicy past
        view action supported
    · simp only [members, ite_eq_right same] at supported
      exact phaseCountServiceTapePolicy_covered setup mode runtime leaks bounds values choose
        failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon table who past view
        action supported
  have posteriorAtEntry (who : Player) :
      ((app).policyMixture (priors who) (members who)).posterior
          ((app).recallAt who entry.state) = oldPosterior who := by
    by_cases same : who = focal
    · subst who
      rw [(app).policyMixture_posterior_of_agree (priors focal) (members focal) focalRaw
        ((app).recallAt focal entry.state)
          (fun _before _record _prefix _table => by simp only [members, ite_true])]
      simp only [priors, ite_true]
    · simp only [priors, members, ite_eq_right same]
      rfl
  have restrictedFocal :
      (menu).restrictPolicy initial horizon scheduler focal focalRaw = focalPolicy :=
    (menu).restrict_decode_embedPolicy initial horizon scheduler focal focalPolicy
  have memberProfile (tables : Player → PhaseSeedAddress graph → Fin horizon → Bool × Bool) :
      (fun who => (menu).restrictPolicy initial horizon scheduler who
        (members who (tables who))) =
      Function.update (fun who => (menu).restrictPolicy initial horizon scheduler who
        (Q (tables who) who)) focal focalPolicy := by
    funext who
    by_cases same : who = focal
    · subst who
      simpa only [members, ite_true, Function.update_self] using restrictedFocal
    · simp only [members, ite_eq_right same, Function.update_of_ne same]
  have mixed := (menu).runUntil_policyMixtures initial horizon scheduler certificate priors
    members covered stopped entry
  simp_rw [posteriorAtEntry, memberProfile] at mixed
  apply mixed.trans
  apply (N).runBehavioralUntil_congr certificate stopped entry
  intro later _reached _running who
  by_cases same : who = focal
  · subst who
    have constant : ((app).policyMixture (priors focal) (members focal)).policy = focalRaw := by
      funext past view
      rw [ReactiveApplication.policyMixture_policy]
      simp only [members, ite_true]
      exact PMF.bind_const _ _
    rw [constant, restrictedFocal, Function.update_self]
  · have originalFamily : ((app).policyMixture (priors who) (members who)).policy =
        ((app).policyMixture original (fun table => Q table who)).policy := by
      simp only [priors, members, ite_eq_right same]
    rw [originalFamily, Function.update_of_ne same]
    rcases later with ⟨state, trace⟩
    have observed := (menu).info initial horizon scheduler who trace
    change (N).infoOf who trace = (app).observe who state at observed
    cases state with
    | none => rw [observed]; rfl
    | some current =>
        by_cases active : current.actor = some who
        · simp only [ReactiveApplication.observe, ite_eq_left active] at observed
          rw [observed]
          apply (menu).restrictPolicy_eq_of_law_eq
          exact phaseCountServiceTapePolicy_table_policy_of_history setup mode runtime leaks
            bounds values choose failure timing firstNonnegative firstBounded timingNonnegative
            timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
            horizon plan inputs scheduler current trace who active
        · simp only [ReactiveApplication.observe, ite_eq_right active] at observed
          rw [observed]
          rfl

end Vegas
