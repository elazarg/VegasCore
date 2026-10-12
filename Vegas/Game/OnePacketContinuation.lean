/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLawApproximation

/-! # Transporting continuations of the one-packet game

From any history of the one-packet game, for instance the history just after
an owner's local source choice at a forced information state, suppose the
as-if-honest continuation reads out a given source continuation law. Then every
profile dominating as-if-honest play from that history, whatever it does
elsewhere, has a joint law of typed readout and exclusion payoff within
`|Player| * fuel * (1 - retention)` in total variation of that source
continuation with its exclusion payoff
(`Vegas.onePacket_continuation_readout_exclusion_withinTV`), and expected
exclusion payoffs within that error times the payoff range
(`Vegas.onePacket_continuation_expect_exclusion_sub_le`). Along retentions
tending to one the error vanishes, uniformly over histories and over the
dominating profiles (`Vegas.onePacket_continuationTransport`). For prescribed
trembled components the retention is `Vegas.trembleRetention` of the scale.

The as-if-honest continuation identity and the domination from the history are
explicit hypotheses; from initialization both are proven
(`Vegas.honestProfile_readout_law`, `Vegas.dominatesHonest_of_prescribed_forced`).
Two cases are excluded and covered elsewhere. After a choice at which the
decoded point leaves some player owing a failed reveal, the information states
after the public failure are not forced and their play is free, so the readout
law is not transported; the owner's payoff is pinned instead
(`Vegas.decoded_owesFailure_expect_exclusionBase`). At a late activation, whose
send may no longer fit the deadline, the event may fail by expiry; such choices
are ranked by their success probability (`Vegas.lateBest_failure_le`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))
  (initial : PMF (application setup leaks).State) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- A typed readout with the exclusion payoff it determines. -/
def withExclusion (readout : Option (State L setup.program.terminalCtx)) :
    Option (State L setup.program.terminalCtx) × (Player → ℝ) :=
  (readout, exclusionReadoutUtility setup parameter utility excludedPayoff readout)

/-- **Continuation transport.** From a history whose as-if-honest continuation
reads out `sourceLaw`, every profile dominating as-if-honest play from it has a
joint law of typed readout and exclusion payoff within
`|Player| * fuel * (1 - retention)` of `sourceLaw` with its exclusion payoff. -/
theorem onePacket_continuation_readout_exclusion_withinTV
    (assessment : setup.intendedModel.BehavioralAssessment)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
      scheduler).History) (fuel : Nat)
    (sourceLaw : PMF (Option (State L setup.program.terminalCtx)))
    (honestContinuation : ((onePacketModel setup leaks bounds initial horizon
        scheduler).runBehavioralFrom
        (honestProfile setup leaks bounds initial horizon scheduler assessment) fuel start).map
        (fun final => sourceReadout setup leaks final.state) = sourceLaw)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (profile : ∀ who,
      (onePacketModel setup leaks bounds initial horizon scheduler).BehavioralPolicy who)
    (dominates : DominatesHonestFrom setup leaks bounds initial horizon scheduler assessment
      retention profile start) :
    PMF.WithinTV ((Fintype.card Player * fuel : ℕ) * (1 - retention))
      (((onePacketModel setup leaks bounds initial horizon scheduler).runBehavioralFrom profile
        fuel start).map
          (readoutExclusion setup leaks bounds initial horizon scheduler parameter utility
            excludedPayoff))
      (sourceLaw.map (withExclusion setup parameter utility excludedPayoff)) := by
  have native : readoutExclusion setup leaks bounds initial horizon scheduler parameter utility
      excludedPayoff = withExclusion setup parameter utility excludedPayoff ∘
        fun final => sourceReadout setup leaks final.state := rfl
  rw [native, ← PMF.map_comp, ← honestContinuation, PMF.map_comp, PMF.map_comp]
  exact ((onePacket_continuation_withinTV_honest setup leaks bounds initial horizon scheduler
    assessment nonnegative le_one profile start dominates fuel).map _).symm

/-- **Transported expected payoffs.** Under the hypotheses of
`onePacket_continuation_readout_exclusion_withinTV`, with every readout payoff
of `who` in `[low, low + range]`, the expected native exclusion payoff of `who`
differs from its expected exclusion payoff under `sourceLaw` by at most the
error times the range. -/
theorem onePacket_continuation_expect_exclusion_sub_le
    (assessment : setup.intendedModel.BehavioralAssessment)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
      scheduler).History) (fuel : Nat)
    (sourceLaw : PMF (Option (State L setup.program.terminalCtx)))
    (honestContinuation : ((onePacketModel setup leaks bounds initial horizon
        scheduler).runBehavioralFrom
        (honestProfile setup leaks bounds initial horizon scheduler assessment) fuel start).map
        (fun final => sourceReadout setup leaks final.state) = sourceLaw)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (profile : ∀ who,
      (onePacketModel setup leaks bounds initial horizon scheduler).BehavioralPolicy who)
    (dominates : DominatesHonestFrom setup leaks bounds initial horizon scheduler assessment
      retention profile start) (who : Player) (low range : ℝ)
    (bounded : ∀ readout, low ≤ exclusionReadoutUtility setup parameter utility excludedPayoff
        readout who ∧
      exclusionReadoutUtility setup parameter utility excludedPayoff readout who ≤ low + range) :
    |expect ((onePacketModel setup leaks bounds initial horizon scheduler).runBehavioralFrom
        profile fuel start)
        (fun final => exclusionBase setup parameter utility excludedPayoff leaks final.state who) -
      expect sourceLaw
        (fun readout => exclusionReadoutUtility setup parameter utility excludedPayoff readout
          who)| ≤
      ((Fintype.card Player * fuel : ℕ) * (1 - retention)) * range := by
  have close := onePacket_continuation_readout_exclusion_withinTV setup leaks bounds initial
    horizon scheduler parameter utility excludedPayoff assessment start fuel sourceLaw
    honestContinuation nonnegative le_one profile dominates
  let payoff := fun pair : Option (State L setup.program.terminalCtx) × (Player → ℝ) =>
    pair.2 who
  have pairBounded : ∀ pair, pair ∈ (((onePacketModel setup leaks bounds initial horizon
      scheduler).runBehavioralFrom profile fuel start).map
        (readoutExclusion setup leaks bounds initial horizon scheduler parameter utility
          excludedPayoff)).support ∨
      pair ∈ (sourceLaw.map (withExclusion setup parameter utility excludedPayoff)).support →
      low ≤ payoff pair ∧ payoff pair ≤ low + range := by
    rintro pair (member | member)
    · obtain ⟨final, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact bounded (sourceReadout setup leaks final.state)
    · obtain ⟨readout, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      exact bounded readout
  have upper := close.expect_sub_le payoff low range pairBounded
  have lower := close.symm.expect_sub_le payoff low range (fun pair member =>
    pairBounded pair member.symm)
  rw [expect_map, expect_map] at upper lower
  let native := fun final : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial
      horizon scheduler).History =>
    exclusionBase setup parameter utility excludedPayoff leaks final.state who
  let source := fun readout : Option (State L setup.program.terminalCtx) =>
    exclusionReadoutUtility setup parameter utility excludedPayoff readout who
  have upper' : expect ((onePacketModel setup leaks bounds initial horizon
      scheduler).runBehavioralFrom profile fuel start) native - expect sourceLaw source ≤
      ((Fintype.card Player * fuel : ℕ) * (1 - retention)) * range := upper
  have lower' : expect sourceLaw source - expect ((onePacketModel setup leaks bounds initial
      horizon scheduler).runBehavioralFrom profile fuel start) native ≤
      ((Fintype.card Player * fuel : ℕ) * (1 - retention)) * range := lower
  exact abs_le.mpr ⟨by linarith, upper'⟩

/-- **Uniform continuation transport.** Along retentions in `[0, 1]` that tend
to one, there is one vanishing error bounding, at every index, from every
history whose as-if-honest continuation reads out a given source law, the
distance of the joint law of typed readout and exclusion payoff of every
profile dominating as-if-honest play from that source law with its exclusion
payoff. -/
theorem onePacket_continuationTransport
    (assessments : ℕ → setup.intendedModel.BehavioralAssessment) (fuel : Nat)
    (retentions : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ retentions n)
    (le_one : ∀ n, retentions n ≤ 1) (converging : Tendsto retentions atTop (nhds 1)) :
    ∃ transportError : ℕ → ℝ, Tendsto transportError atTop (nhds 0) ∧
      ∀ n (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
          scheduler).History)
        (sourceLaw : PMF (Option (State L setup.program.terminalCtx))),
        ((onePacketModel setup leaks bounds initial horizon scheduler).runBehavioralFrom
            (honestProfile setup leaks bounds initial horizon scheduler (assessments n)) fuel
            start).map (fun final => sourceReadout setup leaks final.state) = sourceLaw →
        ∀ profile : (∀ who,
          (onePacketModel setup leaks bounds initial horizon scheduler).BehavioralPolicy who),
        DominatesHonestFrom setup leaks bounds initial horizon scheduler (assessments n)
          (retentions n) profile start →
        PMF.WithinTV (transportError n)
          (((onePacketModel setup leaks bounds initial horizon scheduler).runBehavioralFrom
            profile fuel start).map
              (readoutExclusion setup leaks bounds initial horizon scheduler parameter utility
                excludedPayoff))
          (sourceLaw.map (withExclusion setup parameter utility excludedPayoff)) := by
  refine ⟨fun n => (Fintype.card Player * fuel : ℕ) * (1 - retentions n), ?_,
    fun n start sourceLaw honest profile dominates =>
      onePacket_continuation_readout_exclusion_withinTV setup leaks bounds initial horizon
        scheduler parameter utility excludedPayoff (assessments n) start fuel sourceLaw honest
        (nonnegative n) (le_one n) profile dominates⟩
  have limit := ((tendsto_const_nhds (x := (1 : ℝ))).sub converging).const_mul
    ((Fintype.card Player * fuel : ℕ) : ℝ)
  simpa using limit

end Vegas
