/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceGraph
import Vegas.Game.SealedCandidate
import Vegas.Compile.SealedCandidatePolicy
import Vegas.Compile.SealedPublicOutcome
import Vegas.Compile.SourceDisclosureReads

/-! # Written-source strategies in the candidate-message runtime

This edge is the composition of the independently proved source-to-graph and
graph-to-candidate certificates. The source compiler certifies the graph's
information condition, disclosure uniqueness, and public utility interpretation.
The only incentive premise is the written-source uniform quitting bound.
The target permits arbitrary observation-local native unilateral policies,
including competing and unopenable candidates, malformed traffic, and replay.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph GameTheory GameTheory.GameForm

variable {Player : Type} [DecidableEq Player] [Finite Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Source-to-candidate utility simulation by composition through the graph.
The target utility values the actual public payout; no private service table
or source reconstruction is used to evaluate native outcomes. -/
def candidatePayoutSimulation (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing bound : Player → ℝ)
    (hbound : source.core.prog.QuitPayoutBound source.core.env nullValue valuation bound) :
    UtilitySimulation (sourceGameForm source.core.prog source.core.env) model.game
      (fun final who => valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who)
      (fun next who => (compilation.publicPayout? next.native.application.visible.events).elim
        (missing who) (fun payout => valuation payout who)) := by
  letI : Fintype Player := Fintype.ofFinite Player
  exact (source.sourceGraphPayoutSimulation valuation missing).trans
    (model.utilitySimulation timely (compile_publicPrefixReadable source.core)
      (compile_guardLive source.core source.legal) source.compiled_uniqueReveals
      (source.graphPayoutUtility valuation missing) bound
      (source.graphQuitBound_of_source nullValue valuation missing bound hbound))

/-- Arbitrary native unilateral deviations have no greater expected payout
utility than a legal written-source deviation against the original opponents. -/
theorem candidate_deviation_bound (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing bound : Player → ℝ)
    (hbound : source.core.prog.QuitPayoutBound source.core.env nullValue valuation bound)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : model.game.sig.Strategy who) :
    ∃ alternative : SourceBehavioralPolicy source.core.prog who,
      (model.game.play (Profile.update
        (fun player => compilation.compileCandidatePolicy nullValue window player (profile player))
        who replacement)).expect (fun next =>
          (compilation.publicPayout? next.native.application.visible.events).elim
            (missing who) (fun payout => valuation payout who)) ≤
      ((sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who alternative)).expect (fun final =>
          valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who) :=
  (compilation.candidatePayoutSimulation nullValue window model timely valuation missing bound
    hbound).deviation_bound profile who replacement

/-- End-to-end same-error equilibrium preservation and reflection at the
actual generated profiles. Fair service is relative to the timeout windows;
the source quitting condition is stronger than ordinary ex-ante dominance.
Neither native deviation laws nor native utility inequalities are premises. -/
theorem candidate_approximate_nash_iff (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing bound : Player → ℝ)
    (hbound : source.core.prog.QuitPayoutBound source.core.env nullValue valuation bound)
    (ε : ℝ) (profile : SourceBehavioralProfile source.core.prog) :
    IsεNash model.game
      (fun next who => (compilation.publicPayout? next.native.application.visible.events).elim
        (missing who) (fun payout => valuation payout who)) ε
      (fun who => compilation.compileCandidatePolicy nullValue window who (profile who)) ↔
    IsεNash (sourceGameForm source.core.prog source.core.env)
      (fun final who => valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who)
      ε profile :=
  (compilation.candidatePayoutSimulation nullValue window model timely valuation missing bound
    hbound).isεNash_compileProfile_iff ε profile

theorem candidate_nash_iff (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing bound : Player → ℝ)
    (hbound : source.core.prog.QuitPayoutBound source.core.env nullValue valuation bound)
    (profile : SourceBehavioralProfile source.core.prog) :
    IsNash model.game
      (euPreference (fun next who =>
        (compilation.publicPayout? next.native.application.visible.events).elim
          (missing who) (fun payout => valuation payout who)))
      (fun who => compilation.compileCandidatePolicy nullValue window who (profile who)) ↔
    IsNash (sourceGameForm source.core.prog source.core.env)
      (euPreference (fun final who =>
        valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who)) profile :=
  (compilation.candidatePayoutSimulation nullValue window model timely valuation missing bound
    hbound).isNash_compileProfile_iff profile

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.candidatePayoutSimulation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidatePayoutSimulation

/-- info: 'Vegas.SealedCompilation.candidate_approximate_nash_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_approximate_nash_iff

/-- info: 'Vegas.SealedCompilation.candidate_nash_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_nash_iff
