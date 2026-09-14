/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedHonestRound
import Vegas.Compile.SealedRoundCoupling
import GameTheoryExtensions.Core.UtilitySimulation

/-! # Strategic analysis of the pending-message round driver

The target game runs the actual sealed resolution driver. Players have its
unrestricted observation-local native policies; the wire policy is a fixed,
possibly randomized and adaptive environment, not an additional game player.

The utility theorem below uses an explicit sufficient incentive condition:
completed timeout settlements pay the deviator at most a floor attained by
every source outcome. This includes zero-valued default settlements and
nonnegative source utilities. It is stronger than a conditional continuation
comparison, and is not implied by ordinary source dominance of quitting.
Normal completion must use the same utility as the decoded source outcome.
These are utility conditions, not assumed strategic simulations.
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
  let : Fintype Player := Fintype.ofFinite Player
  obtain ⟨responses, hsource, hnative⟩ :=
    compilation.exists_randomized_round_source_coupling nullValue window model.principals
      model.serviceSlots model.total who nullValue profile replacement model.wire
  let coupling := responses.bind fun response =>
    compilation.extractedRoundSourceCoupling nullValue window model.principals model.serviceSlots
      model.total who response.1 response.2 nullValue profile
  let value := fun outcome : Option (VEnv L (sourceTerminalCtx source.core.prog)) =>
    outcome.elim 0 (fun final => sourceUtility final who)
  have hsourceExpect := congrArg (fun law => law.expect value) hsource
  simp only [FinDist.expect_map, FinDist.expect_bind] at hsourceExpect
  let stopped := fun pair : ReachableConfig (compile source.core).graph ×
      model.game.sig.Outcome => !pair.2.native.application.visible.timeouts.isEmpty
  have hpoint : ∀ pair ∈ coupling.support,
      nativeUtility pair.2 who + (if stopped pair then margin else 0) ≤
        value (observeSourceOutcome source.core pair.1) := by
    intro pair hpair
    have hnext : pair.2 ∈ (model.game.play (Profile.update (fun player =>
        compilation.compileResolvingPolicy nullValue window player (profile player))
          who replacement)).support := by
      rw [show model.game.play _ = coupling.map Prod.snd from hnative.symm,
        FinDist.support_map]
      exact ⟨pair, hpair, rfl⟩
    have hcomplete := model.play_complete _ pair.2 hnext
    have hterminal := compilation.mixtureRoundSourceCoupling_terminal nullValue window
      model.principals model.serviceSlots model.total who nullValue profile responses
      pair.1 pair.2 hpair
    by_cases hclear : pair.2.native.application.visible.timeouts = []
    · have hdecoded := compilation.mixtureRoundSourceCoupling_decode_of_complete_clear
        nullValue window model.principals model.serviceSlots model.total who nullValue
        profile responses pair.1 pair.2 hpair hcomplete hclear
      simpa only [stopped, hclear, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, add_zero] using
        (hagrees pair.1 pair.2 hterminal (model.play_eventInvariant _ pair.2 hnext)
          hcomplete hclear hdecoded who).le
    · have hstop : stopped pair = true := by simp [stopped, hclear]
      simp only [hstop, ↓reduceIte]
      have hcap := htimeout pair.2 hcomplete
        (model.deviation_ownTimeout timely profile who replacement pair.2 hnext hclear)
      rw [observeSourceOutcome_of_terminal source.core pair.1 hterminal]
      dsimp only [value, Option.elim]
      exact (by linarith : nativeUtility pair.2 who + margin ≤ floor + margin).trans
        (hsourceFloor _)
  have hbound := FinDist.stopping_information_fiber_bound coupling stopped (fun _ => ())
    (fun pair => value (observeSourceOutcome source.core pair.1))
    (fun pair => nativeUtility pair.2 who) margin
    (by
      intro pair hpair hclear
      simpa only [hclear, Bool.false_eq_true, ↓reduceIte, add_zero] using hpoint pair hpair)
    (by
      intro _ _
      apply FinDist.expect_mono
      intro pair hpair
      cases hstop : stopped pair with
      | false => simp
      | true => simpa [hstop] using hpoint pair hpair)
  have hmean := FinDist.exists_expect_le_support responses (fun response =>
    (denoteSource source.core.prog
      (Profile.update (sig := sourceGameSignature source.core.prog) profile who
        (compilation.extractedSourcePolicy nullValue window who response.1 response.2
          (SealedResolution.roundSchedule model.principals model.serviceSlots model.total)
          nullValue)) source.core.env).expect (fun outcome => sourceUtility outcome who))
  obtain ⟨response, _, hmean⟩ := hmean
  refine ⟨compilation.extractedSourcePolicy nullValue window who response.1 response.2
    (SealedResolution.roundSchedule model.principals model.serviceSlots model.total) nullValue, ?_⟩
  rw [show model.game.play _ = coupling.map Prod.snd from hnative.symm,
    FinDist.expect_map, FinDist.map_comp]
  apply hbound.trans
  simpa only [coupling, FinDist.expect_bind] using hsourceExpect.le.trans hmean

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
