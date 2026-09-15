/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceGraph
import Vegas.Game.SealedCandidate
import Vegas.Game.SealedCandidatePrefix
import Vegas.Game.SourceQuitPrefix
import Vegas.Compile.SealedCandidatePolicy
import Vegas.Compile.SealedPublicOutcome
import Vegas.Compile.SourceDisclosureReads

/-! # Written-source strategies in the candidate-message runtime

This edge is the composition of the independently proved source-to-graph and
graph-to-candidate certificates. The source compiler certifies the graph's
information condition, disclosure uniqueness, and public utility interpretation.
Incentive premises are source-only: legal quitting settlements are compared
with supported unilateral continuations sharing the public environment before
the source decision. A global quitting cap and fixed-opponent support floor
are sufficient conditions. A uniform floor supplies a reusable whole-game
utility simulation.
Separate caps and floors give a timeout-weighted deviation bound and quantified
approximate-Nash preservation. Reflection requires no quitting condition.
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

/-- An arbitrary native deviation is bounded by a written-source deviation
against unchanged opponents under the source-only prefix-relative quitting
condition. The proof composes the graph/native prefix comparison with the
independent source/graph strategic correspondence. -/
theorem candidate_deviation_bound_of_source_quit_prefix
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing : Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog)
    (hdominance : source.core.prog.QuitPayoutPrefixDominanceAgainst source.core.env
      nullValue valuation profile) (who : Player) (replacement : model.game.sig.Strategy who) :
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
  obtain ⟨graphAlternative, hgraph⟩ := model.deviation_bound_of_quit_prefix timely
    (compile_publicPrefixReadable source.core) (compile_guardLive source.core source.legal)
    source.compiled_uniqueReveals (source.graphPayoutUtility valuation missing)
    (first.compileProfile profile) who
    (fun alternative quitting continued hcontinued hquitting producer guard
        hproducer hvalue hreads =>
      source.graphPayout_le_of_source_quitPrefix nullValue valuation missing profile hdominance
        who alternative quitting continued hcontinued hquitting producer guard hproducer
        hvalue hreads) replacement
  obtain ⟨alternative, hsource⟩ := first.deviation_bound profile who graphAlternative
  exact ⟨alternative, hgraph.trans hsource⟩

/-- Same-error Nash preservation and reflection at a compiled source profile
under a source-only comparison of prefix-matched quitting continuations. The
target permits all observation-local candidate-message deviations. -/
theorem candidate_approximate_nash_iff_of_source_quit_prefix
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing : Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog)
    (hdominance : source.core.prog.QuitPayoutPrefixDominanceAgainst source.core.env
      nullValue valuation profile) (ε : ℝ) :
    IsεNash model.game (fun next who =>
      (compilation.publicPayout? next.native.application.visible.events).elim
        (missing who) (fun payout => valuation payout who)) ε
      (fun player => compilation.compileCandidatePolicy nullValue window player (profile player)) ↔
    IsεNash (sourceGameForm source.core.prog source.core.env)
      (fun final who => valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who)
      ε profile := by
  exact isεNash_compileProfile_iff_of_utility_bounds
    (source := sourceGameForm source.core.prog source.core.env) (target := model.game)
    (sourceUtility := fun final who =>
      valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who)
    (targetUtility := fun next who =>
      (compilation.publicPayout? next.native.application.visible.events).elim
        (missing who) (fun payout => valuation payout who))
    (compilation.compileCandidatePolicy nullValue window)
    (compilation.candidate_honest_payout_utility nullValue window model timely valuation missing)
    profile (compilation.candidate_deviation_bound_of_source_quit_prefix nullValue window
      model timely valuation missing profile hdominance) ε

/-- Exact Nash correspondence at the compiled profile is the zero-error
instance of the same source-prefix comparison. -/
theorem candidate_nash_iff_of_source_quit_prefix
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing : Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog)
    (hdominance : source.core.prog.QuitPayoutPrefixDominanceAgainst source.core.env
      nullValue valuation profile) :
    IsNash model.game (euPreference (fun next who =>
      (compilation.publicPayout? next.native.application.visible.events).elim
        (missing who) (fun payout => valuation payout who)))
      (fun player => compilation.compileCandidatePolicy nullValue window player (profile player)) ↔
    IsNash (sourceGameForm source.core.prog source.core.env)
      (euPreference (fun final who =>
        valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who)) profile := by
  simpa only [isNash_iff_isεNash_zero] using
    compilation.candidate_approximate_nash_iff_of_source_quit_prefix nullValue window model
      timely valuation missing profile hdominance 0

/-- A source-defined gap between the quitting cap and the fixed-opponent
support floor bounds the gain from selective quitting. It is charged only on
the actual native timeout event, not on every execution. -/
theorem candidate_deviation_bound_with_quit_gap (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing cap floor : Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog)
    (hcap : source.core.prog.QuitPayoutCap source.core.env nullValue valuation cap)
    (hfloor : source.core.prog.PayoutFloorAgainst source.core.env valuation floor profile)
    (who : Player) (replacement : model.game.sig.Strategy who) :
    ∃ alternative : SourceBehavioralPolicy source.core.prog who,
      (model.game.play (Profile.update
        (fun player => compilation.compileCandidatePolicy nullValue window player (profile player))
        who replacement)).expect (fun next =>
          (compilation.publicPayout? next.native.application.visible.events).elim
            (missing who) (fun payout => valuation payout who)) ≤
      ((sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who alternative)).expect (fun final =>
          valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who) +
        (cap who - floor who) * ((model.game.play (Profile.update
          (fun player => compilation.compileCandidatePolicy nullValue window player
            (profile player)) who replacement)).map
              (fun next => !next.native.application.visible.timeouts.isEmpty)).prob true := by
  let : Fintype Player := Fintype.ofFinite Player
  let first := source.sourceGraphPayoutSimulation valuation missing
  obtain ⟨graphAlternative, hgraph⟩ := model.deviation_bound_with_quit_gap timely
    (compile_publicPrefixReadable source.core) (compile_guardLive source.core source.legal)
    source.compiled_uniqueReveals (source.graphPayoutUtility valuation missing) cap
    (source.graphQuitCap_of_source nullValue valuation missing cap hcap)
    (first.compileProfile profile) who (floor who)
    (source.graphPayout_floor_of_source_deviations valuation missing profile who (floor who)
      (hfloor who)) replacement
  obtain ⟨alternative, hsource⟩ := first.deviation_bound profile who graphAlternative
  refine ⟨alternative, hgraph.trans ?_⟩
  exact add_le_add hsource le_rfl

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
  exact compilation.candidate_deviation_bound_of_source_quit_prefix nullValue window model
    timely valuation missing profile hbound.quitPayoutPrefixDominance who replacement

/-- At an approximate source equilibrium, the gain of each native deviation
is bounded by the source error plus the source utility gap times that very
deviation's timeout probability. -/
theorem candidate_deviation_gain_bound (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing cap floor : Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog)
    (hcap : source.core.prog.QuitPayoutCap source.core.env nullValue valuation cap)
    (hfloor : source.core.prog.PayoutFloorAgainst source.core.env valuation floor profile)
    (ε : ℝ) (hnash : IsεNash (sourceGameForm source.core.prog source.core.env)
      (fun final who => valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who)
      ε profile) (who : Player) (replacement : model.game.sig.Strategy who) :
    let compiled := fun player =>
      compilation.compileCandidatePolicy nullValue window player (profile player)
    let utility := fun next : model.game.sig.Outcome =>
      (compilation.publicPayout? next.native.application.visible.events).elim
        (missing who) (fun payout => valuation payout who)
    (model.game.play (Profile.update compiled who replacement)).expect utility -
        (model.game.play compiled).expect utility ≤
      ε + (cap who - floor who) * ((model.game.play
        (Profile.update compiled who replacement)).map
          (fun next => !next.native.application.visible.timeouts.isEmpty)).prob true := by
  obtain ⟨alternative, hbound⟩ := compilation.candidate_deviation_bound_with_quit_gap
    nullValue window model timely valuation missing cap floor profile hcap hfloor who replacement
  rw [GameTheory.isεNash_iff] at hnash
  have hsource := hnash who alternative
  have hhonest := compilation.candidate_honest_payout_utility nullValue window model timely
    valuation missing profile who
  dsimp only
  change ((sourceGameForm source.core.prog source.core.env).play
    (Profile.update profile who alternative)).expect (fun final =>
      valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who) ≤
    ((sourceGameForm source.core.prog source.core.env).play profile).expect (fun final =>
      valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who) + ε at hsource
  linarith

/-- A uniform upper bound on the source utility gaps gives an unconditional
approximate-Nash guarantee. The sharper deviation theorem charges only actual
timeout probability; this corollary uses its upper bound of one. -/
theorem candidate_approximate_nash_of_source_gap (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing cap floor : Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog)
    (hcap : source.core.prog.QuitPayoutCap source.core.env nullValue valuation cap)
    (hfloor : source.core.prog.PayoutFloorAgainst source.core.env valuation floor profile)
    (ε δ : ℝ) (hnash : IsεNash (sourceGameForm source.core.prog source.core.env)
      (fun final who => valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who)
      ε profile) (hδ : 0 ≤ δ) (hgap : ∀ who, cap who - floor who ≤ δ) :
    IsεNash model.game
      (fun next who => (compilation.publicPayout? next.native.application.visible.events).elim
        (missing who) (fun payout => valuation payout who)) (ε + δ)
      (fun who => compilation.compileCandidatePolicy nullValue window who (profile who)) := by
  rw [GameTheory.isεNash_iff]
  intro who replacement
  have hgain := compilation.candidate_deviation_gain_bound nullValue window model timely valuation
    missing cap floor profile hcap hfloor ε hnash who replacement
  dsimp only at hgain
  let law := (model.game.play (Profile.update
    (fun player => compilation.compileCandidatePolicy nullValue window player (profile player))
    who replacement)).map (fun next => !next.native.application.visible.timeouts.isEmpty)
  have hcost : (cap who - floor who) * law.prob true ≤ δ :=
    (mul_le_mul_of_nonneg_right (hgap who) (law.prob_nonneg true)).trans
      (mul_le_of_le_one_right hδ (law.prob_le_one true))
  change (model.game.play (Profile.update
    (fun player => compilation.compileCandidatePolicy nullValue window player (profile player))
    who replacement)).expect _ ≤ (model.game.play
      (fun player => compilation.compileCandidatePolicy nullValue window player
        (profile player))).expect _ + (ε + δ)
  linarith

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

/-- Reflection needs only honest payout agreement and timely service. It has
no source quitting incentive premise and makes no claim outside compiled profiles. -/
theorem candidate_approximate_nash_reflect (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (model : compilation.supported.CandidateRoundModel nullValue window) (timely : model.Timely)
    (valuation : Payout Player → Player → ℝ) (missing : Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog) (ε : ℝ)
    (hnash : IsεNash model.game
      (fun next who => (compilation.publicPayout? next.native.application.visible.events).elim
        (missing who) (fun payout => valuation payout who)) ε
      (fun who => compilation.compileCandidatePolicy nullValue window who (profile who))) :
    IsεNash (sourceGameForm source.core.prog source.core.env)
      (fun final who => valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who)
      ε profile :=
  isεNash_of_compileProfile
    (source := sourceGameForm source.core.prog source.core.env) (target := model.game)
    (sourceUtility := fun final who =>
      valuation (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) who)
    (targetUtility := fun next who =>
      (compilation.publicPayout? next.native.application.visible.events).elim
        (missing who) (fun payout => valuation payout who))
    (compilation.compileCandidatePolicy nullValue window)
    (compilation.candidate_honest_payout_utility nullValue window model timely valuation missing)
    profile ε hnash

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

/-- info: 'Vegas.SealedCompilation.candidate_deviation_bound_of_source_quit_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_deviation_bound_of_source_quit_prefix

/-- info: 'Vegas.SealedCompilation.candidate_approximate_nash_iff_of_source_quit_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_approximate_nash_iff_of_source_quit_prefix

/-- info: 'Vegas.SealedCompilation.candidate_nash_iff_of_source_quit_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_nash_iff_of_source_quit_prefix

/-- info: 'Vegas.SealedCompilation.candidate_deviation_bound_with_quit_gap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_deviation_bound_with_quit_gap

/-- info: 'Vegas.SealedCompilation.candidate_approximate_nash_of_source_gap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_approximate_nash_of_source_gap

/-- info: 'Vegas.SealedCompilation.candidate_approximate_nash_reflect'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_approximate_nash_reflect

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
