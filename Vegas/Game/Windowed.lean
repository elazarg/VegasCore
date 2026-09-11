/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedMixedDeviation
import Vegas.Compile.WindowedReferenceLaw
import Vegas.Compile.ApplicationPolicyLocality
import GameTheoryExtensions.Core.MixtureSimulation

/-! # The fixed windowed operational game

The target game runs the message application's native transition function.
Each strategy is an unrestricted randomized raw-command policy. Compilation
embeds each source player's policy separately; it does not construct player
clients. The reference execution and unilateral mixture laws together preserve
and reflect public-result utility equilibria for the same block service.
-/

noncomputable section

namespace Vegas.WFProgram

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable (source : WFProgram P L)
variable (plan : ApplicationPlan source.accounted source.core.fresh
  (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
variable (deadlineOf : Nat → Nat)
variable (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
variable (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
variable (windowOf : Nat → Nat)

/-- Sequential terminal bindings projected into the executable public result
type. The success tag distinguishes completion from missing runtime output. -/
def publicResult (terminal : VEnv L (sourceTerminalCtx source.core.prog)) :
    Bool × Option (Env L.Val (erasePubVCtx (compile source.core).terminalCtx)) :=
  (true, some (cast (congrArg (VEnv L)
    (compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog source.core.fresh
      (BuildState.fromInitial
        (initialState source.core.Γ source.core.env source.core.wctx))).symm) terminal).erasePubEnv)

/-- The game induced by the actual fixed block-service execution. No source
interpreter or backtranslation participates in its transition function. -/
def windowedGame (roster : List P) : GameForm P :=
  let runtime := plan.windowed deadlineOf binding choice windowOf
  runtime.application.policyGame (runtime.blockEnvironment roster)
    (List.replicate (plan.instructions deadlineOf).length
      (WindowedApplication.blockInvocations roster)).flatten
    (plan.windowedInitialExecution deadlineOf binding choice windowOf).native

/-- Public result read from a native execution. Full native histories remain
available as the operational game's outcomes; this map selects the observation
covered by the source correspondence theorem. -/
def windowedPublicResult
    (out : (plan.windowed deadlineOf binding choice windowOf).application.PolicyExecution) :
    Bool × Option (Env L.Val (erasePubVCtx (compile source.core).terminalCtx)) :=
  (out.native.application.base.memory.finished (compile source.core).graph.nodeCount,
    (compile source.core).readPublicTerminal? out.native.application.base.memory)

/-- Embed one source policy. Other coordinates used to form the internal
profile are irrelevant, by source-policy locality of the generated dispatcher. -/
def windowedCompilePolicy (who : P) (strategy : SourceBehavioralPolicy source.core.prog who) :
    (plan.windowed deadlineOf binding choice windowOf).application.PlayerPolicy :=
  let runtime := plan.windowed deadlineOf binding choice windowOf
  runtime.blockPlayer who (runtime.liftPlayerPolicy
    (plan.liftProfile deadlineOf
      (Profile.update (sig := sourceGameSignature source.core.prog)
        (legalSourceProfile source.core.prog source.legal) who strategy) who))

/-- Coordinatewise compilation is exactly the operational reference profile. -/
theorem windowed_compileProfile (profile : SourceBehavioralProfile source.core.prog) :
    (fun who => source.windowedCompilePolicy plan deadlineOf binding choice windowOf
      who (profile who)) = plan.windowedReferencePlayers profile deadlineOf binding choice
        windowOf := by
  funext who
  let runtime := plan.windowed deadlineOf binding choice windowOf
  have hpolicy := plan.liftProfile_eq_of_sourcePolicy_eq deadlineOf
    (Profile.update (sig := sourceGameSignature source.core.prog)
      (legalSourceProfile source.core.prog source.legal) who (profile who)) profile who (by
        intro Δ x b guard site visible
        simp only [Profile.update_same])
  exact congrArg (fun policy => runtime.blockPlayer who (runtime.liftPlayerPolicy policy)) hpolicy

/-- The actual operational game under the coordinatewise compiled profile has
the source program's public-result law. -/
theorem windowed_honest_public_law
    (profile : SourceBehavioralProfile source.core.prog) (roster : List P) (focal : P)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins)
    (hfallbacks : plan.BlockFallbacks binding choice) (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ plan.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster) :
    ((source.windowedGame plan deadlineOf binding choice windowOf roster).play
      (fun who => source.windowedCompilePolicy plan deadlineOf binding choice windowOf
        who (profile who))).map
        (source.windowedPublicResult plan deadlineOf binding choice windowOf) =
      ((sourceGameForm source.core.prog source.core.env).play profile).map
        source.publicResult := by
  rw [source.windowed_compileProfile plan deadlineOf binding choice windowOf profile]
  exact plan.windowed_reference_source_public_law source profile deadlineOf binding choice
    windowOf roster focal hinitial horigins hfallbacks hroster howners

/-- Arbitrary unilateral strategies of the operational game are simulated
by finite mixtures of source deviations. Every other coordinate is the
compilation of its original source policy. -/
theorem windowed_deviation_mixture
    (profile : SourceBehavioralProfile source.core.prog) (roster : List P) (focal : P)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins)
    (hfallbacks : plan.BlockFallbacks binding choice) (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ plan.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster)
    (replacement : (source.windowedGame plan deadlineOf binding choice windowOf roster).sig.Strategy
      focal)
    (relay : P) (hrelay : relay ∈ roster) (hrelayOther : relay ≠ focal) :
    ∃ sourceMixture : FinDist (SourceBehavioralPolicy source.core.prog focal),
      (((source.windowedGame plan deadlineOf binding choice windowOf roster).play
        (Profile.update (sig := (source.windowedGame plan deadlineOf binding choice windowOf
          roster).sig)
          (fun who => source.windowedCompilePolicy plan deadlineOf binding choice windowOf
            who (profile who)) focal replacement)).map
        (source.windowedPublicResult plan deadlineOf binding choice windowOf)) =
        sourceMixture.bind fun alternative =>
          ((sourceGameForm source.core.prog source.core.env).play
            (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
              alternative)).map source.publicResult := by
  rw [source.windowed_compileProfile plan deadlineOf binding choice windowOf profile]
  exact plan.windowed_deviation_source_public_mixture source profile deadlineOf binding choice
    windowOf roster focal hinitial horigins hfallbacks hroster howners replacement
    relay hrelay hrelayOther

/-- The source game and its fixed windowed operational game have the same
public observation law, and every native unilateral deviation is represented
by a finite mixture of source deviations. -/
def windowed_mixtureSimulation
    (roster : List P) (focal : P)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins)
    (hfallbacks : plan.BlockFallbacks binding choice) (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ plan.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster)
    (hrelays : ∀ player, ∃ relay ∈ roster, relay ≠ player) :
    GameTheory.GameForm.MixtureSimulationOn
      (sourceGameForm source.core.prog source.core.env)
      (source.windowedGame plan deadlineOf binding choice windowOf roster)
      source.publicResult
      (source.windowedPublicResult plan deadlineOf binding choice windowOf)
      (fun _ _ => True) where
  compileStrategy := fun who strategy =>
    source.windowedCompilePolicy plan deadlineOf binding choice windowOf who strategy
  honest_law := fun profile =>
    source.windowed_honest_public_law plan deadlineOf binding choice windowOf profile roster
      focal hinitial horigins hfallbacks hroster howners
  compiled_considered := fun _ _ => trivial
  deviation_mixture := by
    intro profile who replacement _
    obtain ⟨relay, hrelay, hrelayOther⟩ := hrelays who
    exact source.windowed_deviation_mixture plan deadlineOf binding choice windowOf profile
      roster who hinitial horigins hfallbacks hroster howners replacement relay hrelay
      hrelayOther

/-- A bound against every source replacement protects the same observable
against an arbitrary randomized runtime replacement. The observable may value
an unchanged player; the deviator's own utility is unrestricted. -/
theorem windowed_guarantee
    (profile : SourceBehavioralProfile source.core.prog) (roster : List P) (focal : P)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins)
    (hfallbacks : plan.BlockFallbacks binding choice) (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ plan.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster)
    (value : (Bool × Option (Env L.Val (erasePubVCtx (compile source.core).terminalCtx))) → ℝ)
    (bound : ℝ)
    (hbound : ∀ alternative : SourceBehavioralPolicy source.core.prog focal,
      bound ≤ ((sourceGameForm source.core.prog source.core.env).play
        (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
          alternative)).expect (fun terminal => value (source.publicResult terminal)))
    (replacement : (source.windowedGame plan deadlineOf binding choice windowOf roster).sig.Strategy
      focal)
    (relay : P) (hrelay : relay ∈ roster) (hrelayOther : relay ≠ focal) :
    bound ≤ ((source.windowedGame plan deadlineOf binding choice windowOf roster).play
      (Profile.update
        (sig := (source.windowedGame plan deadlineOf binding choice windowOf roster).sig)
        (fun who => source.windowedCompilePolicy plan deadlineOf binding choice windowOf
          who (profile who)) focal replacement)).expect
      (fun out => value
        (source.windowedPublicResult plan deadlineOf binding choice windowOf out)) := by
  obtain ⟨mixture, hlaw⟩ := source.windowed_deviation_mixture plan deadlineOf binding choice
    windowOf profile roster focal hinitial horigins hfallbacks hroster howners replacement
    relay hrelay hrelayOther
  rw [← FinDist.expect_map, hlaw, FinDist.expect_bind]
  calc
    bound = mixture.expect (fun _ => bound) := (FinDist.expect_const _ _).symm
    _ ≤ _ := FinDist.expect_mono fun alternative _ => by
      rw [FinDist.expect_map]
      exact hbound alternative

/-- For arbitrary utilities of the public result, coordinatewise compilation
preserves and reflects the exact approximate-Nash budget. Preservation against
unrestricted native deviations uses a distinct roster relay for each possible
deviator. -/
theorem windowed_approximate_nash_iff
    (profile : SourceBehavioralProfile source.core.prog) (roster : List P) (focal : P)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins)
    (hfallbacks : plan.BlockFallbacks binding choice) (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ plan.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster)
    (hrelays : ∀ player, ∃ relay ∈ roster, relay ≠ player)
    (value : (Bool × Option
      (Env L.Val (erasePubVCtx (compile source.core).terminalCtx))) → P → ℝ)
    (ε : ℝ) :
    IsεNash (source.windowedGame plan deadlineOf binding choice windowOf roster)
      (fun out player => value
        (source.windowedPublicResult plan deadlineOf binding choice windowOf out) player) ε
      (fun player => source.windowedCompilePolicy plan deadlineOf binding choice windowOf
        player (profile player)) ↔
      IsεNash (sourceGameForm source.core.prog source.core.env)
        (fun terminal player => value (source.publicResult terminal) player) ε profile := by
  let simulation := source.windowed_mixtureSimulation plan deadlineOf binding choice windowOf
    roster focal hinitial horigins hfallbacks hroster howners hrelays
  exact simulation.isεNash_compileProfile_iff value ε profile (fun _ _ => trivial)

/-- Exact expected-utility Nash is preserved and reflected as the zero-budget
case of the public-result equilibrium theorem. -/
theorem windowed_nash_iff
    (profile : SourceBehavioralProfile source.core.prog) (roster : List P) (focal : P)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins)
    (hfallbacks : plan.BlockFallbacks binding choice) (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ plan.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster)
    (hrelays : ∀ player, ∃ relay ∈ roster, relay ≠ player)
    (value : (Bool × Option
      (Env L.Val (erasePubVCtx (compile source.core).terminalCtx))) → P → ℝ) :
    IsNash (source.windowedGame plan deadlineOf binding choice windowOf roster)
      (euPreference (fun out player => value
        (source.windowedPublicResult plan deadlineOf binding choice windowOf out) player))
      (fun player => source.windowedCompilePolicy plan deadlineOf binding choice windowOf
        player (profile player)) ↔
      IsNash (sourceGameForm source.core.prog source.core.env)
        (euPreference (fun terminal player => value (source.publicResult terminal) player))
        profile := by
  rw [isNash_iff_isεNash_zero, isNash_iff_isεNash_zero]
  exact source.windowed_approximate_nash_iff plan deadlineOf binding choice windowOf profile
    roster focal hinitial horigins hfallbacks hroster howners hrelays value 0

end Vegas.WFProgram

/-- info: 'Vegas.WFProgram.windowed_compileProfile'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.windowed_compileProfile

/-- info: 'Vegas.WFProgram.windowed_deviation_mixture'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.windowed_deviation_mixture

/-- info: 'Vegas.WFProgram.windowed_mixtureSimulation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.windowed_mixtureSimulation

/-- info: 'Vegas.WFProgram.windowed_guarantee'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.windowed_guarantee

/-- info: 'Vegas.WFProgram.windowed_honest_public_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.windowed_honest_public_law

/-- info: 'Vegas.WFProgram.windowed_approximate_nash_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.windowed_approximate_nash_iff

/-- info: 'Vegas.WFProgram.windowed_nash_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.windowed_nash_iff
