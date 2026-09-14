/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Core.Settlement
import Vegas.Compile.SealedSettlement
import Vegas.Game.SealedPayout

/-! # Source payout bounds imply pending-message incentive preservation

The uniform quitting condition is stated entirely in the written source
semantics. The compiler supplies public settlement correspondence, timeout
ownership, normal utility agreement, and the causal deviation comparison.
Only utilities obtained by valuing the programmed payout are considered here.
-/

noncomputable section

namespace Vegas.SealedCompilation.RoundModel

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Finite Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable {compilation : SealedCompilation source ty} {nullValue : L.Val ty} {window : Nat}

/-- In actual pending-message play, a player's timeout has the programmed
payout of a legal written-source execution recording that player's default.
The same source witness establishes the choice and the payout. It is a
settlement witness, not a claim about the opponents' source policy law. -/
theorem play_publicPayout_source_choice
    (model : RoundModel compilation nullValue window)
    (players : Profile model.game.sig) (next : model.game.sig.Outcome)
    (hnext : next ∈ (model.game.play players).support)
    (who : Player) (hown : model.OwnTimeout who next) :
    ∃ final : VEnv L (sourceTerminalCtx source.core.prog),
      SmallStep.Star ⟨source.core.Γ, source.core.env, source.core.prog⟩
        ⟨sourceTerminalCtx source.core.prog, final, .ret (sourceTerminalPayoffs source.core.prog)⟩ ∧
      source.core.prog.Chooses who nullValue final ∧
      compilation.publicPayout? next.native.application.visible.events =
        some (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) := by
  obtain ⟨node, htimeout, howned⟩ := hown
  have hsettlement := SealedResolution.runRounds_initial_settlementInvariant
    (compilation.supported.resolvingRuntime nullValue window)
    model.principals model.serviceSlots players model.wire model.total next hnext
  obtain ⟨cfg, hterminal, hchoice, hpayout⟩ :=
    compilation.publicPayout_source_choice_of_timeout nullValue window next.native.application
      (model.play_eventInvariant players next hnext) hsettlement
      (model.play_complete players next hnext) node who htimeout howned
  exact ⟨_, decodeSourceOutcome_reachable source.core cfg hterminal, hchoice, hpayout⟩

/-- A source-only bound on all quitting settlements discharges every native
timeout-checkpoint comparison, including adaptive selective withholding.
No agreement with a runtime utility or checkpoint cap is assumed by the caller. -/
theorem timeoutCheckpointDominance_of_sourcePayoutBound
    (model : RoundModel compilation nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing bound : Player → ℝ)
    (hbound : source.core.prog.QuitPayoutBound source.core.env nullValue valuation bound)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : model.game.sig.Strategy who) :
    model.TimeoutCheckpointDominance (sourcePayoutUtility (source := source) valuation)
      (nativePayoutUtility model valuation missing) profile who replacement 0 := by
  let : Fintype Player := Fintype.ofFinite Player
  apply model.timeoutCheckpointDominance_of_locked_cap
    (sourcePayoutUtility (source := source) valuation) (nativePayoutUtility model valuation missing)
    profile who replacement 0 (fun _ => bound who)
  · intro pair hpair hstop
    have hnext : pair.2.2 ∈ (model.game.play (Profile.update (fun player =>
        compilation.compileResolvingPolicy nullValue window player (profile player))
          who replacement)).support := by
      rw [← model.stoppingCoupling_native profile who replacement, FinDist.support_map]
      exact ⟨pair, hpair, rfl⟩
    have hown := model.deviation_ownTimeout timely profile who replacement pair.2.2 hnext
      (by simpa using hstop)
    obtain ⟨final, hsource, hchoice, hpayout⟩ :=
      model.play_publicPayout_source_choice _ pair.2.2 hnext who hown
    rw [nativePayoutUtility, hpayout]
    exact hbound.quit_upper final hsource who hchoice
  · intro _information cfg hterminal _hlocked
    rw [observeSourceOutcome_of_terminal source.core cfg hterminal]
    simpa only [add_zero, Option.elim_some, sourcePayoutUtility] using
      hbound.lower _ (decodeSourceOutcome_reachable source.core cfg hterminal) who

/-- The source-only payout bound constructs the generic composable utility
simulation for this generated runtime and its actual policy translation. -/
def sourcePayoutSimulation
    (model : RoundModel compilation nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing bound : Player → ℝ)
    (hbound : source.core.prog.QuitPayoutBound source.core.env nullValue valuation bound) :
    GameTheory.GameForm.UtilitySimulation
      (sourceGameForm source.core.prog source.core.env) model.game
      (sourcePayoutUtility (source := source) valuation)
      (nativePayoutUtility model valuation missing) :=
  model.checkpointUtilitySimulation timely _ _
    (model.normalUtilityAgreement_sourcePayout valuation missing)
    (model.timeoutCheckpointDominance_of_sourcePayoutBound timely valuation missing bound hbound)

/-- Source-level quitting payout bounds give same-error equilibrium
preservation and reflection at compiled profiles in the actual pending-message
game. Players have arbitrary native policies; the fixed adaptive wire must
satisfy the deadline-relative service condition. The missing-payout fallback
is immaterial on actual completed executions. -/
theorem isεNash_iff_of_sourcePayoutBound
    (model : RoundModel compilation nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing bound : Player → ℝ)
    (hbound : source.core.prog.QuitPayoutBound source.core.env nullValue valuation bound)
    (ε : ℝ) (profile : SourceBehavioralProfile source.core.prog) :
    IsεNash model.game (nativePayoutUtility model valuation missing) ε
      (fun who => compilation.compileResolvingPolicy nullValue window who (profile who)) ↔
    IsεNash (sourceGameForm source.core.prog source.core.env)
      (sourcePayoutUtility (source := source) valuation) ε profile :=
  (model.sourcePayoutSimulation timely valuation missing bound hbound).isεNash_compileProfile_iff
    ε profile

end Vegas.SealedCompilation.RoundModel

/-- info: 'Vegas.SealedCompilation.RoundModel.isεNash_iff_of_sourcePayoutBound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.RoundModel.isεNash_iff_of_sourcePayoutBound
