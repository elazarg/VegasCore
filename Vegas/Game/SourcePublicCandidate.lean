/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPublicSourceOutcome
import Vegas.Compile.SealedTermination
import Vegas.Game.SourceCandidate

/-! # Public source outcomes in the candidate-message game

The compiler's public decoder reads the written-source terminal environment
from native public events. Analysis may apply any interpretation to that
environment: payouts are one possible observation, not the utility carrier.
The honest outcome law is exact. Arbitrary unilateral deviations satisfy the
source-prefix utility bound under the stated source quitting condition.
Neither theorem reads private candidate meanings to evaluate native outcomes.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph GameTheory GameTheory.GameForm GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty}

variable [Finite Player] [DecidableEq (L.Val ty)]

/-- Every supported result of the actual stopped game decodes to a legal
public source outcome, under arbitrary player and wire policies. The driver's
budget proves completion, so neither fairness nor a completion premise is
needed. This support theorem does not assert a source deviation law. -/
theorem candidate_public_source_support (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window)
    (players : Profile model.game.sig) (next : model.game.sig.Outcome)
    (hnext : next ∈ (model.game.play players).support) :
    ∃ final : VEnv L (sourceTerminalCtx source.core.prog),
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := sourceTerminalCtx source.core.prog, env := final,
          cont := .ret (sourceTerminalPayoffs source.core.prog) } ∧
      compilation.publicSourceOutcome? next.native.application.visible.events =
        some final.erasePubEnv := by
  let runtime := compilation.supported.resolvingRuntime nullValue window
  have hpublic := runtime.runRounds_candidate_publicInvariant
    model.principals model.serviceSlots players model.wire model.total _ next
    ⟨Interaction.SealedResolution.PublicEventInvariant.initial runtime,
      Interaction.SealedResolution.SettlementInvariant.initial runtime⟩ hnext
  have hcomplete := compilation.supported.candidateRuntime_runRounds_complete
    nullValue window model.principals model.serviceSlots players model.wire model.total
    model.budget next hnext
  exact compilation.publicSourceOutcome?_source_of_complete nullValue window
    next.native.application.visible hpublic.1 hcomplete

/-- The complete public source outcome law agrees at every compiled profile.
No quitting incentive condition is needed for this honest execution theorem. -/
theorem candidate_public_source_law (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (profile : SourceBehavioralProfile source.core.prog) :
    (model.game.play
      (fun player => compilation.compileCandidatePolicy nullValue window player (profile player))
        ).map (fun next =>
          compilation.publicSourceOutcome? next.native.application.visible.events) =
      ((sourceGameForm source.core.prog source.core.env).play profile).map
        (fun final => some final.erasePubEnv) := by
  let : Fintype Player := Fintype.ofFinite Player
  let graphGame := policyGame (compile source.core).graph (compile source.core).graphWF
    (compile_guardLive source.core source.legal)
  let compiled := source.sourceGraphSimulation.compileProfile profile
  have hnative := model.honest_observation_law timely
    (compile_guardLive source.core source.legal) source.publicSourceOutcome?
    source.publicSourceOutcome?_eq_of_publicFields_eq compiled
  have hterminal : ∀ cfg ∈ (graphGame.play compiled).support,
      Terminal (compile source.core).graph cfg.1 := by
    intro cfg hcfg
    exact runPolicyNodes_terminal (compile source.core).graphWF
      (compile_guardLive source.core source.legal) compiled ⟨Config.initial _, .initial⟩
      (compile source.core).graph.nodeOrder (compile source.core).graph.nodeOrder_readyOrder
      (fun node => Or.inr (by simp)) cfg hcfg
  have hdecode : (graphGame.play compiled).map (fun cfg =>
      source.publicSourceOutcome? cfg.1.store) =
      (graphGame.play compiled).map (fun cfg =>
        (observeSourceOutcome source.core cfg).map VEnv.erasePubEnv) := by
    apply FinDist.map_congr_of_eq_on_support
    intro cfg hcfg
    rw [source.publicSourceOutcome?_terminal cfg (hterminal cfg hcfg),
      observeSourceOutcome_of_terminal source.core cfg (hterminal cfg hcfg)]
    rfl
  have hsource := congrArg
    (fun law : FinDist (Option (VEnv L (sourceTerminalCtx source.core.prog))) =>
      law.map (fun final => final.map VEnv.erasePubEnv))
    (source.sourceGraphSimulation.honest_law profile)
  simp only [FinDist.map_comp] at hsource
  exact hnative.trans (hdecode.trans hsource)

/-- Honest expected utilities follow for any interpretation of the public
terminal source environment, without restricting it to payout valuations. -/
theorem candidate_public_honest_utility (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (interpretation :
      Env L.Val (erasePubVCtx (sourceTerminalCtx source.core.prog)) → Player → ℝ)
    (missing : Player → ℝ) (profile : SourceBehavioralProfile source.core.prog) (who : Player) :
    (model.game.play
      (fun player => compilation.compileCandidatePolicy nullValue window player (profile player))
        ).expect (fun next =>
          (compilation.publicSourceOutcome? next.native.application.visible.events).elim
            (missing who) (fun outcome => interpretation outcome who)) =
      ((sourceGameForm source.core.prog source.core.env).play profile).expect
        (fun final => interpretation final.erasePubEnv who) :=
  compilation.candidate_honest_utility nullValue window model timely
    (fun final who => interpretation final.erasePubEnv who)
    (source.graphPublicUtility interpretation missing) missing
    (source.graphPublicUtility_terminal interpretation missing) profile who

/-- Every arbitrary native unilateral deviation is bounded by a legal source
deviation for the given public-outcome interpretation. The sole incentive
premise is the source-defined prefix-relative quitting comparison. -/
theorem candidate_public_deviation_bound (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (interpretation :
      Env L.Val (erasePubVCtx (sourceTerminalCtx source.core.prog)) → Player → ℝ)
    (missing : Player → ℝ) (profile : SourceBehavioralProfile source.core.prog)
    (hdominance : source.core.prog.QuitPrefixDominanceAgainst source.core.env nullValue
      (fun final who => interpretation final.erasePubEnv who) profile)
    (who : Player) (replacement : model.game.sig.Strategy who) :
    ∃ alternative : SourceBehavioralPolicy source.core.prog who,
      (model.game.play (Profile.update
        (fun player => compilation.compileCandidatePolicy nullValue window player (profile player))
        who replacement)).expect (fun next =>
          (compilation.publicSourceOutcome? next.native.application.visible.events).elim
            (missing who) (fun outcome => interpretation outcome who)) ≤
      ((sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who alternative)).expect
          (fun final => interpretation final.erasePubEnv who) :=
  compilation.candidate_utility_deviation_bound nullValue window model timely
    (fun final who => interpretation final.erasePubEnv who)
    (source.graphPublicUtility interpretation missing) missing
    (source.graphPublicUtility_terminal interpretation missing) profile hdominance who replacement

/-- Reflection at compiled profiles needs only honest public-utility
agreement. No source quitting incentive premise is required. -/
theorem candidate_public_approximate_nash_reflect
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (interpretation :
      Env L.Val (erasePubVCtx (sourceTerminalCtx source.core.prog)) → Player → ℝ)
    (missing : Player → ℝ) (profile : SourceBehavioralProfile source.core.prog) (ε : ℝ)
    (hnash : IsεNash model.game (fun next who =>
      (compilation.publicSourceOutcome? next.native.application.visible.events).elim
        (missing who) (fun outcome => interpretation outcome who)) ε
      (fun player => compilation.compileCandidatePolicy nullValue window player (profile player))) :
    IsεNash (sourceGameForm source.core.prog source.core.env)
      (fun final who => interpretation final.erasePubEnv who) ε profile :=
  isεNash_of_compileProfile
    (source := sourceGameForm source.core.prog source.core.env) (target := model.game)
    (sourceUtility := fun final who => interpretation final.erasePubEnv who)
    (targetUtility := fun next who =>
      (compilation.publicSourceOutcome? next.native.application.visible.events).elim
        (missing who) (fun outcome => interpretation outcome who))
    (compilation.compileCandidatePolicy nullValue window)
    (compilation.candidate_public_honest_utility nullValue window model timely
      interpretation missing) profile ε hnash

/-- Same-error Nash equivalence at the actual compiled profile for an arbitrary
public source outcome interpretation satisfying the source quitting condition. -/
theorem candidate_public_approximate_nash_iff (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (interpretation :
      Env L.Val (erasePubVCtx (sourceTerminalCtx source.core.prog)) → Player → ℝ)
    (missing : Player → ℝ) (profile : SourceBehavioralProfile source.core.prog)
    (hdominance : source.core.prog.QuitPrefixDominanceAgainst source.core.env nullValue
      (fun final who => interpretation final.erasePubEnv who) profile) (ε : ℝ) :
    IsεNash model.game (fun next who =>
      (compilation.publicSourceOutcome? next.native.application.visible.events).elim
        (missing who) (fun outcome => interpretation outcome who)) ε
      (fun player => compilation.compileCandidatePolicy nullValue window player (profile player)) ↔
    IsεNash (sourceGameForm source.core.prog source.core.env)
      (fun final who => interpretation final.erasePubEnv who) ε profile :=
  isεNash_compileProfile_iff_of_utility_bounds
    (source := sourceGameForm source.core.prog source.core.env) (target := model.game)
    (sourceUtility := fun final who => interpretation final.erasePubEnv who)
    (targetUtility := fun next who =>
      (compilation.publicSourceOutcome? next.native.application.visible.events).elim
        (missing who) (fun outcome => interpretation outcome who))
    (compilation.compileCandidatePolicy nullValue window)
    (compilation.candidate_public_honest_utility nullValue window model timely
      interpretation missing)
    profile (compilation.candidate_public_deviation_bound nullValue window model timely
      interpretation missing profile hdominance) ε

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.candidate_public_source_support' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_public_source_support

/-- info: 'Vegas.SealedCompilation.candidate_public_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_public_source_law

/-- info: 'Vegas.SealedCompilation.candidate_public_deviation_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_public_deviation_bound

/-- info: 'Vegas.SealedCompilation.candidate_public_approximate_nash_reflect' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_public_approximate_nash_reflect

/-- info: 'Vegas.SealedCompilation.candidate_public_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_public_approximate_nash_iff
