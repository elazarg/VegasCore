/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.EventMessages
import Vegas.Game.EventServiceEdge
import Vegas.Pending.EventStrategicLaw
import GameTheory.Core.MixtureUtilitySimulation
import GameTheory.Core.MixtureSimulationComposition
import Vegas.Source.FiniteSupport

/-! # Strategic correctness of asynchronous source-to-message compilation

The certificate is three edges composed. The compiler reaches the canonical
graph with a single backtranslated policy; the execution mode is a second edge,
also a single policy; the message service is the third, and the only one that
needs a mixture. Each retains one deviation across private setup.

The last step replaces the store reading by the semantic one. They agree on
every serviced play -- completion discharges the terminality test -- and differ
only where the game never goes.

Native deviations are finitely branching: native commands range over unbounded
replay identifiers and raw values, so the service's predraw covers exactly the
deviations whose laws have finite support. The wire and order policies branch
finitely, fresh binding alphabets are finite, and the initial law is finitely
supported.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]

/-- A compiled source policy relays a graph law over finitely many actions. -/
theorem compileEventPendingStrategy_finiteSupport (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode)) (who : Player)
    (policy : BehavioralPolicy who setup.program) :
    (setup.compileEventPendingStrategy mode runtime who policy).FiniteSupport :=
  runtime.compilePlayerPolicy_finiteSupport fun event _ _ =>
    have := ((Vegas.toEventGraph_finiteActions setup.program finite).withMode mode) event
    (Set.finite_univ_iff.mpr this).subset (Set.subset_univ _)

/-- Finitely branching native players, wire, and order, with a finitely
supported initial law, give a finitely supported pending play. -/
theorem eventPendingGame_play_support_finite (setup : Setup (Player := Player) (L := L))
    [setup.FiniteInitialLaw] (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (roster : List Player) (reactionRounds : Nat)
    {wire : runtime.application.WirePolicy} {order : runtime.ServiceOrderPolicy}
    (wireFinite : wire.FiniteSupport) (orderFinite : order.FiniteSupport)
    (players : Profile (setup.eventPendingGame mode runtime roster reactionRounds wire order).sig)
    (playersFinite : ∀ who, MessageApplication.PlayerPolicy.FiniteSupport (players who)) :
    ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
      players).support.Finite :=
  runtime.servicedEventGame_play_support_finite roster reactionRounds playersFinite wireFinite
    orderFinite _ (by rw [PMF.support_map]; exact setup.initialLaw_support_finite.image _)

/-- Replacing one compiled source policy by a finitely branching native one keeps
every coordinate finitely branching. -/
theorem compileEventPending_update_finiteSupport (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : BehavioralProfile setup.program) (who : Player)
    (replacement : runtime.application.PlayerPolicy)
    (replacementFinite : replacement.FiniteSupport) (actor : Player) :
    MessageApplication.PlayerPolicy.FiniteSupport
      (Profile.update (sig := (setup.eventPendingGame mode runtime
        roster reactionRounds wire order).sig)
        (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
        who replacement actor) := by
  by_cases same : actor = who
  · subst actor
    rw [Profile.update_same]
    exact replacementFinite
  · rw [Profile.update_of_ne _ _ same]
    exact setup.compileEventPendingStrategy_finiteSupport finite mode runtime actor _

/-- Every finitely branching unilateral native policy has exactly the terminal
source-state law of a finite mixture of source policies, against unchanged
opponents. -/
theorem eventPendingGame_deviation_law
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (profile : BehavioralProfile setup.program) (who : Player)
    (replacement : runtime.application.PlayerPolicy)
    (replacementFinite : replacement.FiniteSupport) :
    ∃ mixture : PMF (BehavioralPolicy who setup.program), mixture.support.Finite ∧
      ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
        (Profile.update (sig := (setup.eventPendingGame mode runtime
          roster reactionRounds wire order).sig)
          (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
          who replacement)).map (setup.eventPendingOutcome mode runtime) =
      mixture.bind fun alternative =>
        (setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program)
          profile who alternative)).map some := by
  obtain ⟨mixture, mixtureFinite, law⟩ := runtime.exists_deviation_mixture_store_law feasible
    (setup.eventGraph.withMode_barrierOrdered
      (Vegas.toEventGraph_barrierOrdered setup.program) mode)
    ((Vegas.toEventGraph_finiteActions setup.program finite).withMode mode)
    (setup.initialLaw.map fun initial => setup.eventInputs initial)
    (by rw [PMF.support_map]; exact setup.initialLaw_support_finite.image _)
    (setup.eventGraph.toModeProfile mode
      (Vegas.compileEventProfile setup.program profile))
    roster reactionRounds who replacement replacementFinite wire wireFinite order orderFinite
  refine ⟨mixture.map (fun alternative =>
    Vegas.backtranslateEventPolicy setup.program who
      (setup.eventGraph.fromModePolicy mode who alternative)),
    by rw [PMF.support_map]; exact mixtureFinite.image _, ?_⟩
  rw [setup.eventPendingGame_map_outcome]
  change (((runtime.servicedEventGame _ roster reactionRounds wire order).play
    (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
      (runtime.compileProfile
        (setup.eventGraph.toModeProfile mode
          (Vegas.compileEventProfile setup.program profile)))
      who replacement)).map (fun execution => execution.native.application.config.store)).map _ = _
  rw [law]
  simp only [PMF.map_bind, PMF.bind_map]
  apply bind_congr_on_support _
  intro alternative _
  simp_rw [← (setup.eventGraph.withMode mode).runPolicies_canonical_normalize_eq,
    setup.eventGraph.runPolicies_withMode_store, setup.eventGraph.fromModeProfile_update,
    setup.eventGraph.fromModeProfile_toModeProfile]
  have canonical := Vegas.canonical_setup_deviation_decode setup profile who
    (setup.eventGraph.fromModePolicy mode who alternative)
  simp only [← Vegas.EventGraph.runPolicies_canonical_normalize_eq] at canonical
  exact canonical

/-- The semantic readout and the store decoder induce the same law on every
serviced play, whatever the players do. -/
private theorem eventPendingGame_map_publicOutcome (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (players : Profile
      (setup.eventPendingGame mode runtime roster reactionRounds wire order).sig) :
    ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play players).map
        (setup.eventPendingPublicOutcome mode runtime) =
      ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play players).map
        (fun execution => setup.eventPublicDecode execution.native.application.config.store) := by
  have base := congrArg (PMF.map (Option.map (publicOutcome setup.program)))
    (setup.eventPendingGame_map_outcome mode runtime roster reactionRounds wire order players)
  rw [eventPendingPublicOutcome_eq, ← PMF.map_comp, base]
  simp only [PMF.map_comp, Function.comp_def, eventPublicDecode]

/-- A composable exact strategic certificate for the concrete source compiler
and public pending-message service: the compiler's edge to the canonical graph,
the execution mode's edge above it, and the message service's edge above that.
Every finitely branching native unilateral policy is admitted, and the mixture is
the service's contribution. -/
def eventPendingSimulation (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport) :
    GameForm.MixtureSimulationOn setup.gameForm
      (setup.eventPendingGame mode runtime roster reactionRounds wire order) some
      (setup.eventPendingPublicOutcome mode runtime)
      (fun _ policy => MessageApplication.PlayerPolicy.FiniteSupport policy) :=
  (((setup.canonicalEventSimulation.reobserve some some
        (fun outcome => setup.eventPublicDecode (setup.eventGraph.terminalStore outcome))
        (fun _ => rfl) setup.eventPublicDecode_terminalStore).trans
      (((setup.eventGraph.eventModeSimulation mode
            (setup.initialLaw.map fun initial => setup.eventInputs initial)).trans
          (runtime.servicedCanonicalSimulation
            (setup.eventGraph.withMode_barrierOrdered
              (Vegas.toEventGraph_barrierOrdered setup.program) mode)
            ((Vegas.toEventGraph_finiteActions setup.program finite).withMode mode)
            feasible (setup.initialLaw.map fun initial => setup.eventInputs initial)
            (by rw [PMF.support_map]; exact setup.initialLaw_support_finite.image _)
            roster reactionRounds wire wireFinite order orderFinite)
          (fun _ _ => trivial)).reobserve setup.eventPublicDecode
            (fun outcome => setup.eventPublicDecode (setup.eventGraph.terminalStore outcome))
            (fun execution =>
              setup.eventPublicDecode execution.native.application.config.store)
            (fun _ => rfl) (fun _ => rfl))
      (fun _ _ => trivial)).reobserveTarget (setup.eventPendingPublicOutcome mode runtime)
    (setup.eventPendingGame_map_publicOutcome mode runtime roster reactionRounds wire order))

/-- Every lower bound on a terminal-state observation against unilateral
source deviations holds against finitely branching unilateral native deviations.
The observation need not describe the deviating player's preferences. -/
theorem eventPendingGame_deviation_guarantee
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (profile : BehavioralProfile setup.program) (who : Player)
    (value : PublicOutcome setup.program → ℝ) (missing bound : ℝ)
    (sourceBound : ∀ alternative : BehavioralPolicy who setup.program,
      bound ≤ expect (setup.publicRun
        (Profile.update (sig := SourceProgram.gameSignature setup.program)
          profile who alternative)) value)
    (replacement : runtime.application.PlayerPolicy)
    (replacementFinite : replacement.FiniteSupport) :
    bound ≤ expect ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
      (Profile.update (sig := (setup.eventPendingGame mode runtime
        roster reactionRounds wire order).sig)
        (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
        who replacement))
          (fun outcome =>
            (setup.eventPendingPublicOutcome mode runtime outcome).elim missing value) := by
  let optionValue : Option (PublicOutcome setup.program) → ℝ :=
    fun outcome => outcome.elim missing value
  let simulation := setup.eventPendingSimulation finite mode runtime feasible roster
    reactionRounds wire wireFinite order orderFinite
  exact simulation.guarantee profile who optionValue bound
    (fun alternative _ => sourceBound alternative) replacement replacementFinite
    (payoffIntegrable_of_finite_support _ _
      (setup.eventPendingGame_play_support_finite mode runtime roster reactionRounds wireFinite
        orderFinite _ (setup.compileEventPending_update_finiteSupport finite mode runtime roster
          reactionRounds wire order profile who replacement replacementFinite)))

/-- Against fixed opponents, each finitely branching native deviation's expected
terminal-state test value is bounded above by that of some legal source
deviation. The witness may depend on both the profile and the chosen test. -/
theorem eventPendingGame_deviation_utility_bound
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (profile : BehavioralProfile setup.program) (who : Player)
    (value : PublicOutcome setup.program → ℝ) (missing : ℝ)
    (replacement : runtime.application.PlayerPolicy)
    (replacementFinite : replacement.FiniteSupport) :
    ∃ alternative : BehavioralPolicy who setup.program,
      expect ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
        (Profile.update
          (sig := (setup.eventPendingGame mode runtime roster reactionRounds wire order).sig)
          (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
          who replacement))
            (fun outcome =>
              (setup.eventPendingPublicOutcome mode runtime outcome).elim missing value) ≤
      expect (setup.publicRun (Profile.update (sig := SourceProgram.gameSignature setup.program)
        profile who alternative)) (fun result => value result) := by
  let optionValue : Option (PublicOutcome setup.program) → Player → ℝ :=
    fun outcome _ => outcome.elim missing value
  let simulation := setup.eventPendingSimulation finite mode runtime feasible roster
    reactionRounds wire wireFinite order orderFinite
  exact (simulation.exists_source_deviation_ge optionValue profile who replacement
    replacementFinite
    (payoffIntegrable_of_finite_support _ _
      (setup.eventPendingGame_play_support_finite mode runtime roster reactionRounds wireFinite
        orderFinite _ (setup.compileEventPending_update_finiteSupport finite mode runtime roster
          reactionRounds wire order profile who replacement replacementFinite)))).imp
    fun _ found => found.2

/-- Same-error Nash preservation and reflection at compiled profiles for every
utility of the terminal source state, against finitely branching native
deviations. -/
theorem eventPendingGame_approximate_nash_iff
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (utility : PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ) (profile : BehavioralProfile setup.program) :
    (∀ who (replacement : runtime.application.PlayerPolicy), replacement.FiniteSupport →
      euPreferenceWithin ε
        (fun outcome who => (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing who) (fun result => utility result who)) who
        ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
          (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor)))
        ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
          (Profile.update (sig := (setup.eventPendingGame mode runtime
            roster reactionRounds wire order).sig)
            (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
            who replacement))) ↔
      IsεNash setup.gameForm utility ε profile := by
  let optionUtility : Option (PublicOutcome setup.program) → Player → ℝ :=
    fun outcome who => outcome.elim (missing who) (fun result => utility result who)
  exact ((setup.eventPendingSimulation finite mode runtime feasible roster reactionRounds wire
    wireFinite order orderFinite).considered_deviations_iff_isεNash optionUtility ε
      profile).trans (and_iff_left fun who replacement replacementFinite =>
        hasExpectation_of_payoffIntegrable (payoffIntegrable_of_finite_support _ _
          (setup.eventPendingGame_play_support_finite mode runtime roster reactionRounds
            wireFinite orderFinite _ (setup.compileEventPending_update_finiteSupport finite mode
              runtime roster reactionRounds wire order profile who replacement
                replacementFinite))))

/-- A source best response compiles to a best response against the same
opponents compiled, against every finitely branching native deviation. Only one
player is fixed, so the opponents need not be best responding themselves. -/
theorem eventPendingGame_isBestResponse_compileProfile
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (utility : PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (profile : BehavioralProfile setup.program) (who : Player)
    (best : IsBestResponse setup.gameForm (euPreference utility) who profile (profile who))
    (replacement : runtime.application.PlayerPolicy)
    (replacementFinite : replacement.FiniteSupport) :
    euPreference (fun outcome actor =>
        (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing actor) (fun result => utility result actor)) who
      ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
        (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor)))
      ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
        (Profile.update (sig := (setup.eventPendingGame mode runtime
          roster reactionRounds wire order).sig)
          (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
          who replacement)) := by
  let optionUtility : Option (PublicOutcome setup.program) → Player → ℝ :=
    fun outcome actor => outcome.elim (missing actor) (fun result => utility result actor)
  exact (setup.eventPendingSimulation finite mode runtime feasible roster reactionRounds wire
    wireFinite order orderFinite).compileStrategy_ge_considered optionUtility profile who best
      replacement replacementFinite
      (payoffIntegrable_of_finite_support _ _
        (setup.eventPendingGame_play_support_finite mode runtime roster reactionRounds
          wireFinite orderFinite _ (setup.compileEventPending_update_finiteSupport finite mode
            runtime roster reactionRounds wire order profile who replacement replacementFinite)))
      (payoffIntegrable_of_finite_support _ _
        (setup.gameForm_play_support_finite finite _))

/-- A dominant source policy compiles to a best response against every compiled
opponent profile and every finitely branching native deviation. The environment
ranges over compiled source profiles only, so this is dominance relative to
source-expressible opponents, not native dominance. -/
theorem eventPendingGame_isBestResponse_of_isDominant
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (utility : PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (who : Player) (policy : BehavioralPolicy who setup.program)
    (dominant : IsDominant setup.gameForm (euPreference utility) who policy)
    (opponents : BehavioralProfile setup.program)
    (replacement : runtime.application.PlayerPolicy)
    (replacementFinite : replacement.FiniteSupport) :
    euPreference (fun outcome actor =>
        (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing actor) (fun result => utility result actor)) who
      ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
        (Profile.update (sig := (setup.eventPendingGame mode runtime
          roster reactionRounds wire order).sig)
          (fun actor => setup.compileEventPendingStrategy mode runtime actor (opponents actor))
          who (setup.compileEventPendingStrategy mode runtime who policy)))
      ((setup.eventPendingGame mode runtime roster reactionRounds wire order).play
        (Profile.update (sig := (setup.eventPendingGame mode runtime
          roster reactionRounds wire order).sig)
          (fun actor => setup.compileEventPendingStrategy mode runtime actor (opponents actor))
          who replacement)) := by
  let profile := Profile.update (sig := SourceProgram.gameSignature setup.program)
    opponents who policy
  have own : profile who = policy := by simp only [profile, Profile.update_same]
  have best : IsBestResponse setup.gameForm (euPreference utility) who profile
      (profile who) := by
    intro alternative
    rw [own]
    simpa only [profile, Profile.update_idem] using dominant alternative opponents
  have compiled : Profile.update (sig := (setup.eventPendingGame mode runtime
      roster reactionRounds wire order).sig)
      (fun actor => setup.compileEventPendingStrategy mode runtime actor (opponents actor))
      who (setup.compileEventPendingStrategy mode runtime who policy) =
      fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor) := by
    funext actor
    by_cases same : actor = who
    · subst actor
      simp only [profile, Profile.update_same]
    · simp only [profile, Profile.update_of_ne _ _ same]
  have replaced : Profile.update (sig := (setup.eventPendingGame mode runtime
      roster reactionRounds wire order).sig)
      (fun actor => setup.compileEventPendingStrategy mode runtime actor (opponents actor))
      who replacement =
      Profile.update (sig := (setup.eventPendingGame mode runtime
        roster reactionRounds wire order).sig)
        (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))
        who replacement := by
    funext actor
    by_cases same : actor = who
    · subst actor
      simp only [Profile.update_same]
    · simp only [profile, Profile.update_of_ne _ _ same]
  rw [compiled, replaced]
  exact setup.eventPendingGame_isBestResponse_compileProfile finite mode runtime feasible roster
    reactionRounds wire wireFinite order orderFinite utility missing profile who best replacement
    replacementFinite

/-- Strong Nash reflects from a compiled profile: if no native coalition gains
at the compiled profile, then no source coalition gains at the source profile.
Only the honest law is used. The converse direction fails in general, because a
target may offer a coalition a channel the source lacks; see
`GameTheory.GameForm.CoalitionWitness.isEmpty_coalitionSimulation`. -/
theorem eventPendingGame_isStrongNash_of_compileProfile
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (feasible : runtime.ServiceFeasible)
    (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (wireFinite : wire.FiniteSupport)
    (order : runtime.ServiceOrderPolicy) (orderFinite : order.FiniteSupport)
    (utility : PublicOutcome setup.program → Player → ℝ)
    (missing : Player → ℝ) (ε : ℝ) (profile : BehavioralProfile setup.program)
    (strong : IsStrongNash (setup.eventPendingGame mode runtime roster reactionRounds wire order)
      (euPreferenceWithin ε fun outcome actor =>
        (setup.eventPendingPublicOutcome mode runtime outcome).elim
          (missing actor) (fun result => utility result actor))
      (fun actor => setup.compileEventPendingStrategy mode runtime actor (profile actor))) :
    IsStrongNash setup.gameForm (euPreferenceWithin ε utility) profile := by
  let optionUtility : Option (PublicOutcome setup.program) → Player → ℝ :=
    fun outcome actor => outcome.elim (missing actor) (fun result => utility result actor)
  let simulation := setup.eventPendingSimulation finite mode runtime feasible roster
    reactionRounds wire wireFinite order orderFinite
  rw [← isεGroupNash_nonemptyGroups_iff] at strong ⊢
  have sourceIntegrable (profile : BehavioralProfile setup.program) (who : Player) :=
    payoffIntegrable_of_finite_support (setup.gameForm.play profile)
      ((fun observation => optionUtility observation who) ∘ some)
      (setup.gameForm_play_support_finite finite profile)
  have targetIntegrable (profile : BehavioralProfile setup.program) (who : Player) :=
    (simulation.integrable_compile_iff profile
      (fun observation => optionUtility observation who)).mpr (sourceIntegrable profile who)
  exact GameForm.isεGroupNash_of_compileProfile simulation.compileStrategy
    (fun profile who => ⟨fun _ => hasExpectation_of_payoffIntegrable (sourceIntegrable profile who),
      fun _ => hasExpectation_of_payoffIntegrable (targetIntegrable profile who)⟩)
    (fun profile who _ _ => (extendedExpect_eq_expect (targetIntegrable profile who)).trans
      ((congrArg _ (simulation.expect_compile profile
        (fun observation => optionUtility observation who))).trans
          (extendedExpect_eq_expect (sourceIntegrable profile who)).symm))
    (nonemptyGroups Player) ε profile strong

end Vegas.SourceProgram.Setup
