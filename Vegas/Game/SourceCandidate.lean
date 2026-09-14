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
Incentive premises are source-only: a cap on legal quitting settlements and a
pointwise floor against the fixed opponents. A uniform floor supplies a reusable
whole-game utility simulation.
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

/-- Honest expected payout agreement needs no quitting incentive condition. -/
theorem candidate_honest_payout_utility (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing : Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player) :
    (model.game.play
      (fun player => compilation.compileCandidatePolicy nullValue window player (profile player))
        ).expect (fun next => (compilation.publicPayout?
          next.native.application.visible.events).elim
            (missing who) (fun payout => valuation payout who)) =
      ((sourceGameForm source.core.prog source.core.env).play profile).expect
        (fun final =>
          valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who) := by
  let : Fintype Player := Fintype.ofFinite Player
  exact (model.honest_utility timely (compile_guardLive source.core source.legal)
    (source.graphPayoutUtility valuation missing)
    ((source.sourceGraphPayoutSimulation valuation missing).compileProfile profile) who).trans
      ((source.sourceGraphPayoutSimulation valuation missing).honest_utility profile who)

/-- The source floor is required only against the fixed opponents under
analysis. Runtime deviations remain unrestricted, and the cap on quitting
settlements is still expressed entirely in written-source semantics. -/
theorem candidate_deviation_bound_of_source_floor (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing bound : Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog)
    (hbound : source.core.prog.QuitPayoutBoundAgainst source.core.env nullValue
      valuation bound profile) (who : Player) (replacement : model.game.sig.Strategy who) :
    ∃ alternative : SourceBehavioralPolicy source.core.prog who,
      (model.game.play (Profile.update
        (fun player => compilation.compileCandidatePolicy nullValue window player (profile player))
        who replacement)).expect (fun next =>
          (compilation.publicPayout? next.native.application.visible.events).elim
            (missing who) (fun payout => valuation payout who)) ≤
      ((sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who alternative)).expect (fun final =>
          valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who) := by
  let : Fintype Player := Fintype.ofFinite Player
  let first := source.sourceGraphPayoutSimulation valuation missing
  obtain ⟨graphAlternative, hgraph⟩ := model.deviation_bound_of_support_floor timely
    (compile_publicPrefixReadable source.core) (compile_guardLive source.core source.legal)
    source.compiled_uniqueReveals (source.graphPayoutUtility valuation missing) bound
    (source.graphQuitCap_of_source nullValue valuation missing bound hbound.quit_upper)
    (first.compileProfile profile) who
    (source.graphPayout_floor_of_source_deviations valuation missing profile who (bound who)
      (hbound.lower who)) replacement
  obtain ⟨alternative, hsource⟩ := first.deviation_bound profile who graphAlternative
  exact ⟨alternative, hgraph.trans hsource⟩

/-- Same-error Nash equivalence at a fixed source profile under a source-only
support floor against its unchanged opponents and a global quitting cap.
No source floor at another opponent profile is assumed. -/
theorem candidate_approximate_nash_iff_of_source_floor
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing bound : Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog)
    (hbound : source.core.prog.QuitPayoutBoundAgainst source.core.env nullValue
      valuation bound profile) (ε : ℝ) :
    IsεNash model.game
      (fun next who => (compilation.publicPayout? next.native.application.visible.events).elim
        (missing who) (fun payout => valuation payout who)) ε
      (fun who => compilation.compileCandidatePolicy nullValue window who (profile who)) ↔
    IsεNash (sourceGameForm source.core.prog source.core.env)
      (fun final who => valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who)
      ε profile :=
  isεNash_compileProfile_iff_of_utility_bounds
    (source := sourceGameForm source.core.prog source.core.env) (target := model.game)
    (sourceUtility := fun final who =>
      valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who)
    (targetUtility := fun next who =>
      (compilation.publicPayout? next.native.application.visible.events).elim
        (missing who) (fun payout => valuation payout who))
    (compilation.compileCandidatePolicy nullValue window)
    (compilation.candidate_honest_payout_utility nullValue window model timely valuation missing)
    profile (compilation.candidate_deviation_bound_of_source_floor nullValue window model timely
      valuation missing bound profile hbound) ε

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

/-- info: 'Vegas.SealedCompilation.candidate_deviation_bound_of_source_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_deviation_bound_of_source_floor

/-- info: 'Vegas.SealedCompilation.candidate_approximate_nash_iff_of_source_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_approximate_nash_iff_of_source_floor

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
