/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedHonestRound
import Vegas.Compile.SealedRoundCoupling
import Vegas.Compile.SealedStoppingCoupling
import GameTheoryExtensions.Core.UtilitySimulation

/-! # Strategic analysis of the pending-message round driver

The target game runs the actual sealed resolution driver. Players have its
unrestricted observation-local native policies; the wire policy is a fixed,
possibly randomized and adaptive environment, not an additional game player.

The coupling retains the deviator's actual timeout-checkpoint information and
a legal source completion with its registered choices fixed. Conditional
utility comparisons on this joint law give a deviation bound and same-error
Nash correspondence. A sufficient condition compares terminal utilities through
checkpoint-dependent caps; a uniform source floor is a special case.
Normal completion must use the same utility as the decoded source outcome.
The timeout comparisons remain explicit program/utility obligations and do
not follow from ordinary source dominance of quitting.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.GameForm GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- A concrete bounded round driver for one compiled program. Its state,
messages, player policies, and environment are those of the shared runtime. -/
structure RoundModel (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat) where
  principals : List Player
  serviceSlots : Nat
  total : Nat
  wire : (compilation.supported.resolvingRuntime nullValue window).messageApplication.WirePolicy
  budget : (compile source.core).graph.nodeCount * (window + 1) ≤ total

/-- A source realization respects the focal player's first registrations in
the recorded local history. This condition fixes registered choices, including
choices registered before their commitment message has been included. -/
def LockedAt (compilation : SealedCompilation source ty) (nullValue : L.Val ty)
    (window : Nat) (who : Player)
    (history : List
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry)
    (cfg : ReachableConfig (compile source.core).graph) : Prop :=
  ∀ (decision : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L),
    ((compile source.core).graph.nodeRow decision).sem = .commit who guard →
    ∀ value, (compilation.supported.compile.registrationEncoding decision.val).cachedValue
      (compilation.supported.resolvingRuntime nullValue window).messageApplication history =
        some value → cfg.1.nodeValues nullValue decision = value

namespace RoundModel

variable {compilation : SealedCompilation source ty} {nullValue : L.Val ty} {window : Nat}

/-- The operational game, including pending messages and timeout settlement. -/
def game (model : RoundModel compilation nullValue window) : GameForm Player where
  sig := policySignature Player
    (compilation.supported.resolvingRuntime nullValue window).messageApplication
  play players :=
    let runtime := compilation.supported.resolvingRuntime nullValue window
    runtime.runRounds model.principals model.serviceSlots players model.wire model.total
      (PolicyExecution.initial _ (State.initial _ runtime.initial))

/-- Deadline-relative inclusion capacity. The unreserved wire opportunities
remain arbitrary; fairness is required at the actual timeout scale. -/
structure Timely (model : RoundModel compilation nullValue window) where
  reserved : Nat → Bool
  service :
    (compilation.supported.resolvingRuntime nullValue window).messageApplication.InclusionService
      (fun turn => reserved turn = true)
      ((compilation.supported.resolvingRuntime nullValue
        window).messageApplication.wireEnvironment model.wire)
  period : Nat
  positive : 0 < period
  capacity : ∀ block, period * model.principals.length ≤
    (List.range' (((block + 1) * period - 1) * (model.serviceSlots + 1))
      model.serviceSlots).countP reserved
  roster : ∀ who, who ∈ model.principals
  windowBound : (compile source.core).graph.nodeCount * (period + 1) + 2 ≤ window
  wholePeriods : period ∣ model.total

/-- A recorded timeout at the player's own source commitment or its reveal.
This is a property of the actual ledger, not a classification of its policy. -/
def OwnTimeout (model : RoundModel compilation nullValue window) (who : Player)
    (next : model.game.sig.Outcome) : Prop :=
  ∃ node : Fin (compile source.core).graph.nodeCount,
    node.val ∈ next.native.application.visible.timeouts ∧
      ((∃ guard, ((compile source.core).graph.nodeRow node).sem = .commit who guard) ∨
        ∃ (producer : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L),
          ((compile source.core).graph.nodeRow node).sem =
            .reveal ((compile source.core).graph.nodeTarget producer) ∧
          ((compile source.core).graph.nodeRow producer).sem = .commit who guard)

/-- Under timely service, only the unilateral deviator can own a timeout. -/
theorem deviation_ownTimeout (model : RoundModel compilation nullValue window)
    (timely : model.Timely) (profile : SourceBehavioralProfile source.core.prog)
    (who : Player) (replacement : model.game.sig.Strategy who)
    (next : model.game.sig.Outcome)
    (hnext : next ∈ (model.game.play (Profile.update (fun player =>
      compilation.compileResolvingPolicy nullValue window player (profile player))
        who replacement)).support)
    (htimeout : next.native.application.visible.timeouts ≠ []) : model.OwnTimeout who next := by
  classical
  obtain ⟨index, hindex⟩ := List.exists_mem_of_ne_nil _ htimeout
  let graphProfile := fun player => compileSourcePolicy source.core.prog source.core.fresh
    (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
    rfl player (profile player)
  obtain ⟨node, owner, hnode, hnot, howned⟩ :=
    compilation.supported.runRounds_timeout_owner nullValue window model.principals
      model.serviceSlots _ model.wire timely.reserved timely.service timely.period
      timely.positive timely.capacity graphProfile (fun player => player ≠ who)
      (by
        intro player hplayer
        rw [Profile.update_of_ne _ _ hplayer]
        rfl)
      (fun player _ => timely.roster player) timely.windowBound model.total timely.wholePeriods
      next hnext index hindex
  have heq : owner = who := not_not.mp hnot
  subst owner
  exact ⟨node, by simpa only [hnode] using hindex, howned⟩

/-- Utility agreement is needed only on completed, timeout-free decoded
executions. Runtime trace preferences are permitted exactly when they satisfy
this agreement and the separate timeout comparison used below. The `none`
extension is immaterial on the terminal source support. -/
def NormalUtilityAgreement (model : RoundModel compilation nullValue window)
    (sourceUtility : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (nativeUtility : model.game.sig.Outcome → Player → ℝ) : Prop :=
  ∀ cfg : ReachableConfig (compile source.core).graph,
    ∀ next : model.game.sig.Outcome,
      Terminal (compile source.core).graph cfg.1 →
      SealedResolution.EventInvariant (compilation.supported.resolvingRuntime nullValue window)
        next.native.application →
      (compilation.supported.resolvingRuntime nullValue window).complete
        next.native.application.visible = true →
      next.native.application.visible.timeouts = [] →
      (compile source.core).graph.decodeSealedFrom ty next.native.application.service
        (Config.initial _) next.native.application.visible.events = some cfg.1 →
      ∀ who, nativeUtility next who =
        (observeSourceOutcome source.core cfg).elim 0 (fun outcome => sourceUtility outcome who)

theorem play_complete (model : RoundModel compilation nullValue window)
    (players : Profile model.game.sig) (next : model.game.sig.Outcome)
    (hnext : next ∈ (model.game.play players).support) :
    (compilation.supported.resolvingRuntime nullValue window).complete
      next.native.application.visible = true :=
  compilation.resolvingRuntime_runRounds_complete nullValue window model.principals
    model.serviceSlots players model.wire model.total model.budget next hnext

theorem play_eventInvariant (model : RoundModel compilation nullValue window)
    (players : Profile model.game.sig) (next : model.game.sig.Outcome)
    (hnext : next ∈ (model.game.play players).support) :
    SealedResolution.EventInvariant (compilation.supported.resolvingRuntime nullValue window)
      next.native.application := by
  apply (compilation.supported.resolvingRuntime nullValue window).runRounds_eventInvariant
    model.principals model.serviceSlots players model.wire model.total _ next
    SealedResolution.EventInvariant.initial hnext

/-- Honest expected utilities follow from the original source outcome law,
not from a putative backtranslation of the all-compiled profile. -/
theorem honest_utility [Finite Player]
    (model : RoundModel compilation nullValue window) (timely : model.Timely)
    (sourceUtility : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (nativeUtility : model.game.sig.Outcome → Player → ℝ)
    (hagrees : model.NormalUtilityAgreement sourceUtility nativeUtility)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player) :
    (model.game.play (fun player =>
      compilation.compileResolvingPolicy nullValue window player (profile player))).expect
        (fun next => nativeUtility next who) =
      (denoteSource source.core.prog profile source.core.env).expect
        (fun outcome => sourceUtility outcome who) := by
  obtain ⟨coupling, hsource, hnative, hdecode⟩ :=
    compilation.exists_honest_round_source_coupling nullValue window model.principals
      model.serviceSlots profile model.wire timely.reserved timely.service timely.period
      timely.positive timely.capacity timely.roster timely.windowBound model.total
      timely.wholePeriods model.budget
  let value := fun outcome : Option (VEnv L (sourceTerminalCtx source.core.prog)) =>
    outcome.elim 0 (fun final => sourceUtility final who)
  have hsourceExpect := congrArg (fun law => law.expect value) hsource
  simp only [FinDist.expect_map] at hsourceExpect
  dsimp only [value, Option.elim] at hsourceExpect
  rw [show model.game.play (fun player => compilation.compileResolvingPolicy nullValue window
      player (profile player)) = coupling.map Prod.snd from hnative.symm, FinDist.expect_map]
  rw [← hsourceExpect]
  apply FinDist.expect_congr
  intro pair hpair
  obtain ⟨hcomplete, hclear, hdecoded⟩ := hdecode pair.1 pair.2 hpair
  have hsome : observeSourceOutcome source.core pair.1 ≠ none := by
    intro hnone
    have hmem : none ∈ (coupling.map (fun pair =>
        observeSourceOutcome source.core pair.1)).support := by
      rw [FinDist.support_map]
      exact ⟨pair, hpair, hnone⟩
    rw [hsource, FinDist.support_map] at hmem
    obtain ⟨_, _, hfalse⟩ := hmem
    cases hfalse
  have hterminal : Terminal (compile source.core).graph pair.1.1 := by
    by_contra hnot
    exact hsome ((observeSourceOutcome_eq_none_iff source.core pair.1).2 hnot)
  have hnext : pair.2 ∈ (model.game.play (fun player =>
      compilation.compileResolvingPolicy nullValue window player (profile player))).support := by
    rw [show model.game.play _ = coupling.map Prod.snd from hnative.symm, FinDist.support_map]
    exact ⟨pair, hpair, rfl⟩
  exact hagrees pair.1 pair.2 hterminal (model.play_eventInvariant _ pair.2 hnext)
    hcomplete hclear hdecoded who

private def responseLaw [Finite Player]
    (model : RoundModel compilation nullValue window)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : model.game.sig.Strategy who) :
    let app := (compilation.supported.resolvingRuntime nullValue window).messageApplication
    FinDist ((List app.PlayerEntry → app.View → app.PlayerCommand) ×
      (List app.EnvironmentEntry → app.EnvironmentObservation → app.EnvironmentPolicyCommand)) := by
  let : Fintype Player := Fintype.ofFinite Player
  exact Classical.choose (compilation.exists_randomized_stopping_round_source_coupling
    nullValue window model.principals model.serviceSlots model.total who nullValue
    profile replacement model.wire)

/-- The compiler's constructed joint law of a legal source realization, the
deviator's local timeout-checkpoint information, and the native round result.
The response mixture is fixed before imposing any utility comparison. -/
def stoppingCoupling [Finite Player]
    (model : RoundModel compilation nullValue window)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : model.game.sig.Strategy who) :
    let app := (compilation.supported.resolvingRuntime nullValue window).messageApplication
    FinDist (ReachableConfig (compile source.core).graph ×
      ((List app.PlayerEntry × app.View) × app.PolicyExecution)) := by
  let : Fintype Player := Fintype.ofFinite Player
  exact (model.responseLaw profile who replacement).bind fun response =>
    compilation.extractedStoppingRoundSourceCoupling nullValue window model.principals
      model.serviceSlots model.total who response.1 response.2 nullValue profile

/-- Legal source alternatives extracted from the same ex-ante response law.
No alternative is selected by observing the timeout information. -/
def sourceDeviationMixture [Finite Player]
    (model : RoundModel compilation nullValue window)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : model.game.sig.Strategy who) :
    FinDist (SourceBehavioralPolicy source.core.prog who) :=
  (model.responseLaw profile who replacement).map fun response =>
    compilation.extractedSourcePolicy nullValue window who response.1 response.2
      (SealedResolution.roundSchedule model.principals model.serviceSlots model.total) nullValue

theorem stoppingCoupling_native [Finite Player]
    (model : RoundModel compilation nullValue window)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : model.game.sig.Strategy who) :
    (model.stoppingCoupling profile who replacement).map (fun pair => pair.2.2) =
      model.game.play (Profile.update (fun player =>
        compilation.compileResolvingPolicy nullValue window player (profile player))
          who replacement) := by
  let : Fintype Player := Fintype.ofFinite Player
  exact (Classical.choose_spec (compilation.exists_randomized_stopping_round_source_coupling
    nullValue window model.principals model.serviceSlots model.total who nullValue
    profile replacement model.wire)).2.2

theorem stoppingCoupling_source [Finite Player]
    (model : RoundModel compilation nullValue window)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : model.game.sig.Strategy who) :
    (model.stoppingCoupling profile who replacement).map
        (fun pair => observeSourceOutcome source.core pair.1) =
      (model.sourceDeviationMixture profile who replacement).bind fun alternative =>
        (denoteSource source.core.prog
          (Profile.update (sig := sourceGameSignature source.core.prog) profile who alternative)
          source.core.env).map some := by
  let : Fintype Player := Fintype.ofFinite Player
  rw [sourceDeviationMixture, FinDist.bind_map]
  exact (Classical.choose_spec (compilation.exists_randomized_stopping_round_source_coupling
    nullValue window model.principals model.serviceSlots model.total who nullValue
    profile replacement model.wire)).1

/-- The information/terminal-state joint marginal is the actual native trace
readout. Neither source values nor the predrawn response pair are components
of the information supplied to this observation. -/
theorem stoppingCoupling_information [Finite Player]
    (model : RoundModel compilation nullValue window)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : model.game.sig.Strategy who) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    (model.stoppingCoupling profile who replacement).map Prod.snd =
      (runtime.messageApplication.tracePolicies
        (Profile.update (sig := policySignature Player runtime.messageApplication)
          (fun player => compilation.compileResolvingPolicy nullValue window player
            (profile player)) who replacement)
        (runtime.roundEnvironment model.serviceSlots model.wire)
        (SealedResolution.roundSchedule model.principals model.serviceSlots model.total)
        (PolicyExecution.initial _ (State.initial _ runtime.initial))).map fun trace =>
          (runtime.firstTimeoutLocalInfo who trace,
            trace.firstReleaseEvery
              (SealedResolution.roundInvocations model.principals model.serviceSlots).length
              (fun execution : runtime.messageApplication.PolicyExecution =>
                runtime.complete execution.native.application.visible)
              model.total) := by
  let : Fintype Player := Fintype.ofFinite Player
  exact (Classical.choose_spec (compilation.exists_randomized_stopping_round_source_coupling
    nullValue window model.principals model.serviceSlots model.total who nullValue
    profile replacement model.wire)).2.1

/-- Every paired source completion retains the focal player's registrations
from the actual timeout-checkpoint history, also for randomized replacements. -/
theorem stoppingCoupling_locked [Finite Player]
    (model : RoundModel compilation nullValue window)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : model.game.sig.Strategy who)
    (pair) (hpair : pair ∈ (model.stoppingCoupling profile who replacement).support) :
    compilation.LockedAt nullValue window who pair.2.1.1 pair.1 := by
  let : Fintype Player := Fintype.ofFinite Player
  change pair ∈ ((model.responseLaw profile who replacement).bind _).support at hpair
  simp only [FinDist.support_bind, Set.mem_iUnion] at hpair
  obtain ⟨response, _, hpair⟩ := hpair
  intro decision guard hdecision value hcache
  exact compilation.extractedStoppingRoundSourceCoupling_locked nullValue window
    model.principals model.serviceSlots model.total who response.1 response.2 nullValue
    profile pair.1 pair.2.1 pair.2.2 hpair decision guard hdecision value hcache

/-- A utility comparison on each supported first-timeout information fiber of
the constructed coupling. The unnormalized form avoids zero-probability
conditioning. The source side is the fixed legal source policy mixture,
analytically conditioned on the native checkpoint, not a strategy allowed to
read that checkpoint. This is a supplied incentive condition; proving it for
a program's settlement requires additional reasoning about its continuations.
The checkpoint may follow the last opportunity to avert timeout. -/
def TimeoutCheckpointDominance [Finite Player]
    (model : RoundModel compilation nullValue window)
    (sourceUtility : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (nativeUtility : model.game.sig.Outcome → Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : model.game.sig.Strategy who) (margin : ℝ) : Prop := by
  classical
  let coupling := model.stoppingCoupling profile who replacement
  exact ∀ information,
    (∃ pair ∈ coupling.support,
      (!pair.2.2.native.application.visible.timeouts.isEmpty) = true ∧ pair.2.1 = information) →
    coupling.expect (fun pair =>
      if !pair.2.2.native.application.visible.timeouts.isEmpty && decide (pair.2.1 = information)
      then nativeUtility pair.2.2 who + margin else 0) ≤
    coupling.expect (fun pair =>
      if !pair.2.2.native.application.visible.timeouts.isEmpty && decide (pair.2.1 = information)
      then (observeSourceOutcome source.core pair.1).elim 0
        (fun outcome => sourceUtility outcome who) else 0)

/-- A checkpoint-conditional comparison suffices for an actual native utility
bound. The bound is against one legal source deviation; positive margins
charge the probability of timeout. The theorem constructs both laws before
using the supplied local utility inequalities. -/
theorem checkpoint_deviation_utility_bound [Finite Player]
    (model : RoundModel compilation nullValue window)
    (sourceUtility : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (nativeUtility : model.game.sig.Outcome → Player → ℝ)
    (hagrees : model.NormalUtilityAgreement sourceUtility nativeUtility)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : model.game.sig.Strategy who) (margin : ℝ)
    (hdominates : model.TimeoutCheckpointDominance sourceUtility nativeUtility
      profile who replacement margin) :
    ∃ alternative : SourceBehavioralPolicy source.core.prog who,
      (model.game.play (Profile.update (fun player =>
        compilation.compileResolvingPolicy nullValue window player (profile player))
          who replacement)).expect (fun next => nativeUtility next who) +
        margin * ((model.game.play (Profile.update (fun player =>
          compilation.compileResolvingPolicy nullValue window player (profile player))
            who replacement)).map (fun next =>
              !next.native.application.visible.timeouts.isEmpty)).prob true ≤
        (denoteSource source.core.prog
          (Profile.update (sig := sourceGameSignature source.core.prog) profile who alternative)
          source.core.env).expect (fun outcome => sourceUtility outcome who) := by
  classical
  let : Fintype Player := Fintype.ofFinite Player
  let coupling := model.stoppingCoupling profile who replacement
  let value := fun outcome : Option (VEnv L (sourceTerminalCtx source.core.prog)) =>
    outcome.elim 0 (fun final => sourceUtility final who)
  have hsourceExpect := congrArg (fun law => law.expect value)
    (model.stoppingCoupling_source profile who replacement)
  simp only [FinDist.expect_map, FinDist.expect_bind] at hsourceExpect
  have hbound := FinDist.stopping_information_fiber_bound coupling
    (fun pair => !pair.2.2.native.application.visible.timeouts.isEmpty) (fun pair => pair.2.1)
    (fun pair => value (observeSourceOutcome source.core pair.1))
    (fun pair => nativeUtility pair.2.2 who) margin
    (by
      intro pair hpair hclear
      have hclear' : pair.2.2.native.application.visible.timeouts = [] := by simpa using hclear
      have hnext : pair.2.2 ∈ (model.game.play (Profile.update (fun player =>
          compilation.compileResolvingPolicy nullValue window player (profile player))
            who replacement)).support := by
        rw [← model.stoppingCoupling_native profile who replacement, FinDist.support_map]
        exact ⟨pair, hpair, rfl⟩
      have hcomplete := model.play_complete _ pair.2.2 hnext
      have hterminal := compilation.mixtureStoppingRoundSourceCoupling_terminal
        nullValue window model.principals model.serviceSlots model.total who nullValue
        profile (model.responseLaw profile who replacement) pair.1 pair.2.1 pair.2.2 hpair
      have hdecoded := compilation.mixtureStoppingRoundSourceCoupling_decode_of_complete_clear
        nullValue window model.principals model.serviceSlots model.total who nullValue
        profile (model.responseLaw profile who replacement) pair.1 pair.2.1 pair.2.2 hpair
        hcomplete hclear'
      exact (hagrees pair.1 pair.2.2 hterminal (model.play_eventInvariant _ pair.2.2 hnext)
        hcomplete hclear' hdecoded who).le)
    (by
      simpa only [TimeoutCheckpointDominance, coupling, value, Bool.and_eq_true,
        decide_eq_true_eq] using hdominates)
  obtain ⟨alternative, _, hmean⟩ := FinDist.exists_expect_le_support
    (model.sourceDeviationMixture profile who replacement) (fun alternative =>
      (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) profile who alternative)
        source.core.env).expect (fun outcome => sourceUtility outcome who))
  refine ⟨alternative, ?_⟩
  rw [← model.stoppingCoupling_native profile who replacement,
    FinDist.expect_map, FinDist.map_comp]
  exact hbound.trans (hsourceExpect.le.trans hmean)

/-- Checkpoint-dependent caps suffice. Different information fibers may have
different utility ranges, so this does not require one global source floor.
The source bounds concern the retained legal completions in this coupling. -/
theorem timeoutCheckpointDominance_of_cap [Finite Player]
    (model : RoundModel compilation nullValue window)
    (sourceUtility : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (nativeUtility : model.game.sig.Outcome → Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : model.game.sig.Strategy who) (margin : ℝ)
    (cap : (List (compilation.supported.resolvingRuntime nullValue
      window).messageApplication.PlayerEntry ×
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.View) → ℝ)
    (hnative : ∀ pair ∈ (model.stoppingCoupling profile who replacement).support,
      (!pair.2.2.native.application.visible.timeouts.isEmpty) = true →
      nativeUtility pair.2.2 who ≤ cap pair.2.1)
    (hsource : ∀ pair ∈ (model.stoppingCoupling profile who replacement).support,
      (!pair.2.2.native.application.visible.timeouts.isEmpty) = true →
      cap pair.2.1 + margin ≤ (observeSourceOutcome source.core pair.1).elim 0
        (fun outcome => sourceUtility outcome who)) :
    model.TimeoutCheckpointDominance sourceUtility nativeUtility
      profile who replacement margin := by
  classical
  intro information _
  apply FinDist.expect_mono
  intro pair hpair
  by_cases hstop : (!pair.2.2.native.application.visible.timeouts.isEmpty) = true
  · have hn := hnative pair hpair hstop
    have hs := hsource pair hpair hstop
    by_cases hinfo : pair.2.1 = information
    · simp only [hstop, hinfo, decide_true, Bool.and_self, ↓reduceIte]
      linarith
    · simp [hinfo]
  · simp [hstop]

/-- It suffices to bound every terminal source realization compatible with
the recorded commitments. The source premise does not mention the extraction
or its probability law. The compiler proves that its paired completion is
one of these realizations. Native settlement still needs its own cap proof. -/
theorem timeoutCheckpointDominance_of_locked_cap [Finite Player]
    (model : RoundModel compilation nullValue window)
    (sourceUtility : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (nativeUtility : model.game.sig.Outcome → Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : model.game.sig.Strategy who) (margin : ℝ)
    (cap : (List (compilation.supported.resolvingRuntime nullValue
      window).messageApplication.PlayerEntry ×
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.View) → ℝ)
    (hnative : ∀ pair ∈ (model.stoppingCoupling profile who replacement).support,
      (!pair.2.2.native.application.visible.timeouts.isEmpty) = true →
      nativeUtility pair.2.2 who ≤ cap pair.2.1)
    (hsource : ∀ information cfg,
      Terminal (compile source.core).graph cfg.1 →
      compilation.LockedAt nullValue window who information.1 cfg →
      cap information + margin ≤ (observeSourceOutcome source.core cfg).elim 0
        (fun outcome => sourceUtility outcome who)) :
    model.TimeoutCheckpointDominance sourceUtility nativeUtility
      profile who replacement margin := by
  let : Fintype Player := Fintype.ofFinite Player
  apply model.timeoutCheckpointDominance_of_cap sourceUtility nativeUtility profile who
    replacement margin cap hnative
  intro pair hpair _
  exact hsource pair.2.1 pair.1
    (compilation.mixtureStoppingRoundSourceCoupling_terminal nullValue window
      model.principals model.serviceSlots model.total who nullValue profile
      (model.responseLaw profile who replacement) pair.1 pair.2.1 pair.2.2 hpair)
    (model.stoppingCoupling_locked profile who replacement pair hpair)

/-- The checkpoint comparisons need hold only for deviations at the profile
being analyzed. Reflection uses the independent honest law for compiled source
alternatives; it requires no comparisons at other source profiles. -/
theorem isεNash_iff_of_checkpointDominance [Finite Player]
    (model : RoundModel compilation nullValue window) (timely : model.Timely)
    (sourceUtility : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (nativeUtility : model.game.sig.Outcome → Player → ℝ)
    (hagrees : model.NormalUtilityAgreement sourceUtility nativeUtility)
    (profile : SourceBehavioralProfile source.core.prog)
    (hdominates : ∀ who replacement,
      model.TimeoutCheckpointDominance sourceUtility nativeUtility profile who replacement 0)
    (ε : ℝ) :
    IsεNash model.game nativeUtility ε
      (fun who => compilation.compileResolvingPolicy nullValue window who (profile who)) ↔
        IsεNash (sourceGameForm source.core.prog source.core.env) sourceUtility ε profile := by
  apply GameForm.isεNash_compileProfile_iff_of_utility_bounds
    (source := sourceGameForm source.core.prog source.core.env) (target := model.game)
    (sourceUtility := sourceUtility) (targetUtility := nativeUtility)
    (compilation.compileResolvingPolicy nullValue window)
    (model.honest_utility timely sourceUtility nativeUtility hagrees) profile _ ε
  intro who replacement
  obtain ⟨alternative, hbound⟩ := model.checkpoint_deviation_utility_bound sourceUtility
    nativeUtility hagrees profile who replacement 0 (hdominates who replacement)
  simp only [zero_mul, add_zero] at hbound
  exact ⟨alternative, hbound⟩

/-- At a source equilibrium, a positive continuation margin bounds how often
a competitive native deviation can time out. For an exact equilibrium, any
deviation attaining the compiled payoff has zero timeout probability. -/
theorem deviation_timeout_cost [Finite Player]
    (model : RoundModel compilation nullValue window) (timely : model.Timely)
    (sourceUtility : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (nativeUtility : model.game.sig.Outcome → Player → ℝ)
    (hagrees : model.NormalUtilityAgreement sourceUtility nativeUtility)
    (profile : SourceBehavioralProfile source.core.prog) (ε : ℝ)
    (hnash : IsεNash (sourceGameForm source.core.prog source.core.env)
      sourceUtility ε profile)
    (who : Player) (replacement : model.game.sig.Strategy who) (margin : ℝ)
    (hdominates : model.TimeoutCheckpointDominance sourceUtility nativeUtility
      profile who replacement margin) :
    let compiled := fun player =>
      compilation.compileResolvingPolicy nullValue window player (profile player)
    (model.game.play (Profile.update compiled who replacement)).expect
        (fun next => nativeUtility next who) +
      margin * ((model.game.play (Profile.update compiled who replacement)).map
        (fun next => !next.native.application.visible.timeouts.isEmpty)).prob true ≤
      (model.game.play compiled).expect (fun next => nativeUtility next who) + ε := by
  obtain ⟨alternative, hbound⟩ := model.checkpoint_deviation_utility_bound sourceUtility
    nativeUtility hagrees profile who replacement margin hdominates
  rw [GameTheory.isεNash_iff] at hnash
  have hsource := hnash who alternative
  change (denoteSource source.core.prog
    (Profile.update (sig := sourceGameSignature source.core.prog) profile who alternative)
    source.core.env).expect (fun outcome => sourceUtility outcome who) ≤
    (denoteSource source.core.prog profile source.core.env).expect
      (fun outcome => sourceUtility outcome who) + ε at hsource
  dsimp only
  rw [model.honest_utility timely sourceUtility nativeUtility hagrees profile who]
  exact hbound.trans hsource

/-- Comparisons valid at every source profile give the reusable, composable
utility-simulation certificate for this concrete operational edge. -/
def checkpointUtilitySimulation [Finite Player]
    (model : RoundModel compilation nullValue window) (timely : model.Timely)
    (sourceUtility : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (nativeUtility : model.game.sig.Outcome → Player → ℝ)
    (hagrees : model.NormalUtilityAgreement sourceUtility nativeUtility)
    (hdominates : ∀ profile who replacement,
      model.TimeoutCheckpointDominance sourceUtility nativeUtility profile who replacement 0) :
    UtilitySimulation (sourceGameForm source.core.prog source.core.env) model.game
      sourceUtility nativeUtility where
  compileStrategy := compilation.compileResolvingPolicy nullValue window
  honest_utility := model.honest_utility timely sourceUtility nativeUtility hagrees
  deviation_bound profile who replacement := by
    obtain ⟨alternative, hbound⟩ := model.checkpoint_deviation_utility_bound sourceUtility
      nativeUtility hagrees profile who replacement 0 (hdominates profile who replacement)
    simp only [zero_mul, add_zero] at hbound
    exact ⟨alternative, hbound⟩

/-- The uniform settlement condition discharges the checkpoint comparison.
Service attributes every actual timeout to the unilateral deviator; the
source bound applies to its retained terminal realization. -/
theorem timeoutCheckpointDominance_of_uniformCap [Finite Player]
    (model : RoundModel compilation nullValue window) (timely : model.Timely)
    (sourceUtility : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (nativeUtility : model.game.sig.Outcome → Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : model.game.sig.Strategy who) (floor margin : ℝ)
    (hsourceFloor : ∀ outcome, floor + margin ≤ sourceUtility outcome who)
    (htimeout : ∀ next : model.game.sig.Outcome,
      (compilation.supported.resolvingRuntime nullValue window).complete
        next.native.application.visible = true →
      model.OwnTimeout who next → nativeUtility next who ≤ floor) :
    model.TimeoutCheckpointDominance sourceUtility nativeUtility
      profile who replacement margin := by
  let : Fintype Player := Fintype.ofFinite Player
  apply model.timeoutCheckpointDominance_of_cap sourceUtility nativeUtility profile who
    replacement margin (fun _ => floor)
  · intro pair hpair hstop
    have hnext : pair.2.2 ∈ (model.game.play (Profile.update (fun player =>
        compilation.compileResolvingPolicy nullValue window player (profile player))
          who replacement)).support := by
      rw [← model.stoppingCoupling_native profile who replacement, FinDist.support_map]
      exact ⟨pair, hpair, rfl⟩
    have hclear : pair.2.2.native.application.visible.timeouts ≠ [] := by simpa using hstop
    exact htimeout pair.2.2 (model.play_complete _ pair.2.2 hnext)
      (model.deviation_ownTimeout timely profile who replacement pair.2.2 hnext hclear)
  · intro pair hpair _
    have hterminal := compilation.mixtureStoppingRoundSourceCoupling_terminal nullValue window
      model.principals model.serviceSlots model.total who nullValue profile
      (model.responseLaw profile who replacement) pair.1 pair.2.1 pair.2.2 hpair
    rw [observeSourceOutcome_of_terminal source.core pair.1 hterminal]
    exact hsourceFloor _

/-- A native unilateral deviation is bounded by a legal written-source
deviation when every completed timeout settlement lies below a common source
utility floor. No restriction is imposed on the deviator's commands or on its
use of delivered pending payloads. This sufficient condition concerns the
deviator's utility only; it gives no lower bound for other affected players. -/
theorem deviation_utility_margin_bound [Finite Player]
    (model : RoundModel compilation nullValue window) (timely : model.Timely)
    (sourceUtility : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (nativeUtility : model.game.sig.Outcome → Player → ℝ)
    (hagrees : model.NormalUtilityAgreement sourceUtility nativeUtility)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : model.game.sig.Strategy who) (floor margin : ℝ)
    (hsourceFloor : ∀ outcome, floor + margin ≤ sourceUtility outcome who)
    (htimeout : ∀ next : model.game.sig.Outcome,
      (compilation.supported.resolvingRuntime nullValue window).complete
        next.native.application.visible = true →
      model.OwnTimeout who next → nativeUtility next who ≤ floor) :
    ∃ alternative : SourceBehavioralPolicy source.core.prog who,
      (model.game.play (Profile.update (fun player =>
        compilation.compileResolvingPolicy nullValue window player (profile player))
          who replacement)).expect (fun next => nativeUtility next who) +
        margin * ((model.game.play (Profile.update (fun player =>
          compilation.compileResolvingPolicy nullValue window player (profile player))
            who replacement)).map (fun next =>
              !next.native.application.visible.timeouts.isEmpty)).prob true ≤
        (denoteSource source.core.prog
          (Profile.update (sig := sourceGameSignature source.core.prog) profile who alternative)
          source.core.env).expect (fun outcome => sourceUtility outcome who) := by
  exact model.checkpoint_deviation_utility_bound sourceUtility nativeUtility hagrees
    profile who replacement margin
    (model.timeoutCheckpointDominance_of_uniformCap timely sourceUtility nativeUtility
      profile who replacement floor margin hsourceFloor htimeout)

/-- A concrete source-to-pending-message utility simulation under timely
service and the stated uniform timeout bound. All policies in the target game
remain available to unilateral deviators. -/
def utilitySimulation [Finite Player]
    (model : RoundModel compilation nullValue window) (timely : model.Timely)
    (sourceUtility : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (nativeUtility : model.game.sig.Outcome → Player → ℝ)
    (hagrees : model.NormalUtilityAgreement sourceUtility nativeUtility)
    (floor : Player → ℝ) (hsourceFloor : ∀ outcome who, floor who ≤ sourceUtility outcome who)
    (htimeout : ∀ next : model.game.sig.Outcome,
      (compilation.supported.resolvingRuntime nullValue window).complete
        next.native.application.visible = true →
      ∀ who, model.OwnTimeout who next → nativeUtility next who ≤ floor who) :
    UtilitySimulation (sourceGameForm source.core.prog source.core.env) model.game
      sourceUtility nativeUtility where
  compileStrategy := compilation.compileResolvingPolicy nullValue window
  honest_utility := model.honest_utility timely sourceUtility nativeUtility hagrees
  deviation_bound profile who replacement :=
    by
      obtain ⟨alternative, hbound⟩ :=
        model.deviation_utility_margin_bound timely sourceUtility nativeUtility hagrees
          profile who replacement (floor who) 0 (fun outcome => by
            simpa only [add_zero] using hsourceFloor outcome who)
          (fun next hcomplete htimeout' => htimeout next hcomplete who htimeout')
      simp only [zero_mul, add_zero] at hbound
      exact ⟨alternative, hbound⟩

/-- The same epsilon is preserved and reflected at compiled profiles. This is
an end-to-end theorem about the written-source game and the actual pending-
message driver, conditional on its explicit service and settlement incentives. -/
theorem isεNash_iff [Finite Player]
    (model : RoundModel compilation nullValue window) (timely : model.Timely)
    (sourceUtility : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (nativeUtility : model.game.sig.Outcome → Player → ℝ)
    (hagrees : model.NormalUtilityAgreement sourceUtility nativeUtility)
    (floor : Player → ℝ) (hsourceFloor : ∀ outcome who, floor who ≤ sourceUtility outcome who)
    (htimeout : ∀ next : model.game.sig.Outcome,
      (compilation.supported.resolvingRuntime nullValue window).complete
        next.native.application.visible = true →
      ∀ who, model.OwnTimeout who next → nativeUtility next who ≤ floor who)
    (ε : ℝ) (profile : SourceBehavioralProfile source.core.prog) :
    IsεNash model.game nativeUtility ε
      (fun who => compilation.compileResolvingPolicy nullValue window who (profile who)) ↔
        IsεNash (sourceGameForm source.core.prog source.core.env) sourceUtility ε profile :=
  (model.utilitySimulation timely sourceUtility nativeUtility hagrees floor hsourceFloor
    htimeout).isεNash_compileProfile_iff ε profile

end RoundModel

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.RoundModel.isεNash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.RoundModel.isεNash_iff
