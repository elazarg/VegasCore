/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SourceCorrespondence
import Vegas.EventGraph.Strategic
import Vegas.Compile.SourceUtility
import GameTheoryExtensions.Core.UtilitySimulation

/-! # Strategic preservation from written source to declared-read graph execution

This is a concrete compiler certificate, not an assumed simulation. It handles
every checked source program, including samples, guarded commitments, and
reveals. The target is the graph's declared-read policy game: extending that
target with message histories, pending traffic, or timeouts needs a further
strategic proof. Graph scheduling does not supply an extra policy input here.
-/

noncomputable section

namespace Vegas.WFProgram

open EventGraph ToEventGraph GameTheory GameTheory.GameForm GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Exact source-outcome simulation for every unilateral graph-kernel
deviation. The witness is a single source policy, embedded as a pure mixture
in the general compositional interface. -/
def sourceGraphSimulation (source : WFProgram P L) :
    MixtureSimulationOn (sourceGameForm source.core.prog source.core.env)
      (policyGame (compile source.core).graph (compile source.core).graphWF
        (compile_guardLive source.core source.legal))
      some (observeSourceOutcome source.core) (fun _ _ => True) where
  compileStrategy who policy := compileSourcePolicy source.core.prog source.core.fresh
    (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
    rfl who policy
  honest_law := runPolicyNodes_compileSourcePolicy_source source.core source.legal
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    refine ⟨FinDist.pure (backtranslateCommitPolicy source.core who replacement), ?_⟩
    rw [FinDist.pure_bind]
    exact runPolicyNodes_source_deviation source.core source.legal profile who replacement

/-- Pointwise source utility floors transport to graph deviations against the
same compiled opponents. No bound is required for different opponent policies. -/
theorem graphPayout_floor_of_source_deviations (source : WFProgram P L)
    (valuation : Payout P → P → ℝ) (missing : P → ℝ)
    (profile : SourceBehavioralProfile source.core.prog) (who : P) (floor : ℝ)
    (hlower : ∀ (alternative : SourceBehavioralPolicy source.core.prog who) final,
      final ∈ (denoteSource source.core.prog (Profile.update
        (sig := sourceGameSignature source.core.prog) profile who alternative)
        source.core.env).support →
      floor ≤ valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who)
    (alternative : CommitPolicy (compile source.core).graph who)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ ((policyGame (compile source.core).graph (compile source.core).graphWF
      (compile_guardLive source.core source.legal)).play
        (Profile.update (source.sourceGraphSimulation.compileProfile profile) who
          alternative)).support) :
    floor ≤ (source.graphPayoutUtility valuation missing).eval cfg.1.store who := by
  have hterminal := runPolicyNodes_terminal (compile source.core).graphWF
    (compile_guardLive source.core source.legal) _ ⟨Config.initial _, .initial⟩
    (compile source.core).graph.nodeOrder (compile source.core).graph.nodeOrder_readyOrder
    (fun node => Or.inr (by simp)) cfg hcfg
  have hobservation : observeSourceOutcome source.core cfg ∈
      ((denoteSource source.core.prog (Profile.update (sig := sourceGameSignature source.core.prog)
        profile who (backtranslateCommitPolicy source.core who alternative))
          source.core.env).map some).support :=
    (runPolicyNodes_source_deviation source.core source.legal profile who alternative) ▸
      ((FinDist.support_map _ _).symm ▸ ⟨cfg, hcfg, rfl⟩)
  rw [observeSourceOutcome_of_terminal source.core cfg hterminal] at hobservation
  simp only [FinDist.support_map, Set.mem_image, Option.some.injEq] at hobservation
  obtain ⟨final, hfinal, heq⟩ := hobservation
  rw [source.graphPayoutUtility_terminal valuation missing cfg hterminal who, ← heq]
  exact hlower _ final hfinal

/-- Interpret the exact source/graph correspondence using any public graph
utility whose terminal meaning agrees with the supplied source utility.
This is a compiler-adapter interface: terminal agreement must be proved, not
assumed of the native runtime. Nonterminal utility extensions are immaterial. -/
def sourceGraphUtilitySimulation (source : WFProgram P L)
    (sourceUtility : VEnv L (sourceTerminalCtx source.core.prog) → P → ℝ)
    (graphUtility : (compile source.core).graph.PublicUtility) (missing : P → ℝ)
    (hterminalUtility : ∀ (cfg : ReachableConfig (compile source.core).graph)
      (hterminal : Terminal (compile source.core).graph cfg.1) (who : P),
      graphUtility.eval cfg.1.store who = sourceUtility
        (decodeSourceOutcome source.core.prog source.core.fresh
          (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
          cfg hterminal) who) :
    UtilitySimulation (sourceGameForm source.core.prog source.core.env)
      (policyGame (compile source.core).graph (compile source.core).graphWF
        (compile_guardLive source.core source.legal))
      sourceUtility (fun cfg => graphUtility.eval cfg.1.store) :=
  (source.sourceGraphSimulation.toUtilitySimulation
    (fun outcome who => outcome.elim (missing who)
      (fun final => sourceUtility final who))
    (fun _ _ => trivial)).congrUtilities _ _ (fun _ _ => rfl) (by
      intro profile who
      apply FinDist.expect_congr
      intro cfg hcfg
      have hterminal := runPolicyNodes_terminal (compile source.core).graphWF
        (compile_guardLive source.core source.legal) profile
        ⟨Config.initial _, .initial⟩ (compile source.core).graph.nodeOrder
        (compile source.core).graph.nodeOrder_readyOrder
        (fun node => Or.inr (by simp)) cfg hcfg
      rw [observeSourceOutcome_of_terminal source.core cfg hterminal]
      exact (hterminalUtility cfg hterminal who).symm)

/-- Payout valuation is one source/public-graph utility interpretation. -/
def sourceGraphPayoutSimulation (source : WFProgram P L)
    (valuation : Payout P → P → ℝ) (missing : P → ℝ) :
    UtilitySimulation (sourceGameForm source.core.prog source.core.env)
      (policyGame (compile source.core).graph (compile source.core).graphWF
        (compile_guardLive source.core source.legal))
      (fun final who => valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who)
      (fun cfg => (source.graphPayoutUtility valuation missing).eval cfg.1.store) :=
  source.sourceGraphUtilitySimulation
    (fun final who => valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who)
    (source.graphPayoutUtility valuation missing) missing
    (source.graphPayoutUtility_terminal valuation missing)

/-- All source-outcome utilities have the same approximate Nash equilibria
at compiled graph profiles, with the same additive error. `none` is unreachable
in complete graph play, so its utility is immaterial. -/
theorem source_graph_approximate_nash_iff (source : WFProgram P L)
    (value : Option (VEnv L (sourceTerminalCtx source.core.prog)) → P → ℝ)
    (ε : ℝ) (profile : SourceBehavioralProfile source.core.prog) :
    IsεNash (policyGame (compile source.core).graph (compile source.core).graphWF
      (compile_guardLive source.core source.legal))
      (fun outcome who => value (observeSourceOutcome source.core outcome) who) ε
      (source.sourceGraphSimulation.compileProfile profile) ↔
    IsεNash (sourceGameForm source.core.prog source.core.env)
      (fun outcome who => value (some outcome) who) ε profile :=
  source.sourceGraphSimulation.isεNash_compileProfile_iff value ε profile (fun _ _ => trivial)

theorem source_graph_nash_iff (source : WFProgram P L)
    (value : Option (VEnv L (sourceTerminalCtx source.core.prog)) → P → ℝ)
    (profile : SourceBehavioralProfile source.core.prog) :
    IsNash (policyGame (compile source.core).graph (compile source.core).graphWF
      (compile_guardLive source.core source.legal))
      (euPreference (fun outcome who => value (observeSourceOutcome source.core outcome) who))
      (source.sourceGraphSimulation.compileProfile profile) ↔
    IsNash (sourceGameForm source.core.prog source.core.env)
      (euPreference (fun outcome who => value (some outcome) who)) profile :=
  source.sourceGraphSimulation.isNash_compileProfile_iff value profile (fun _ _ => trivial)

end Vegas.WFProgram

/-- info: 'Vegas.WFProgram.sourceGraphSimulation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.sourceGraphSimulation

/-- info: 'Vegas.WFProgram.source_graph_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.source_graph_approximate_nash_iff

/-- info: 'Vegas.WFProgram.source_graph_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.source_graph_nash_iff
