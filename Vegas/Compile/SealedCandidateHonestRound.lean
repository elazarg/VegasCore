/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidatePolicy
import Vegas.Compile.SealedHonestRound
import Vegas.Compile.SealedPublicOutcome

/-! # Written-source payouts in the candidate-message round driver

The honest host embedding transports the original source coupling through the
same stopped operational driver. The observable law includes completion and
the timeout list, so it does not assume successful settlement. Its payout is
computed from public initial fields and opening events, not private service
state. No utility function or incentive hypothesis is needed for this law.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Finite Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Under deadline-relative inclusion service, the candidate-host execution
of any source profile completes without timeouts and has exactly the written
source payout law. The wire-policy retyping is surjective and preserves every
observable input. The claim concerns generated profiles, not arbitrary
candidate-player deviations. -/
theorem candidate_honest_round_payout_law
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots : Nat)
    (profile : SourceBehavioralProfile source.core.prog)
    (wire : (compilation.supported.resolvingRuntime nullValue window).messageApplication.WirePolicy)
    (reserved : Nat → Bool)
    (hservice :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.InclusionService
        (fun turn => reserved turn = true)
        ((compilation.supported.resolvingRuntime nullValue
          window).messageApplication.wireEnvironment wire))
    (period : Nat) (hperiod : 0 < period)
    (hcapacity : ∀ block, period * principals.length ≤
      (List.range' (((block + 1) * period - 1) * (serviceSlots + 1))
        serviceSlots).countP reserved)
    (hroster : ∀ who, who ∈ principals)
    (hwindow : (compile source.core).graph.nodeCount * (period + 1) + 2 ≤ window)
    (total : Nat) (hperiods : period ∣ total)
    (hbound : (compile source.core).graph.nodeCount * (window + 1) ≤ total) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    (runtime.candidateRoundDriver.runRounds principals serviceSlots
        (fun who => compilation.compileCandidatePolicy nullValue window who (profile who))
        (runtime.candidateWirePolicy wire) total
        (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).map
        (fun next => (runtime.complete next.native.application.visible,
          next.native.application.visible.timeouts,
          compilation.publicPayout? next.native.application.visible.events)) =
      (denoteSource source.core.prog profile source.core.env).map
        (fun final => (true, ([] : List Nat),
          some (evalPayoffs (sourceTerminalPayoffs source.core.prog) final))) := by
  classical
  intro runtime
  obtain ⟨coupling, hsource, hnative, hpairs⟩ :=
    compilation.exists_honest_round_source_coupling nullValue window principals serviceSlots
      profile wire reserved hservice period hperiod hcapacity hroster hwindow total hperiods hbound
  let summarize := fun outcome : Option (VEnv L (sourceTerminalCtx source.core.prog)) =>
    (true, ([] : List Nat), outcome.map (evalPayoffs (sourceTerminalPayoffs source.core.prog)))
  rw [← compilation.candidateRounds_law nullValue window principals serviceSlots profile wire total,
    FinDist.map_comp, ← hnative, FinDist.map_comp]
  calc
    _ = coupling.map (fun pair => summarize (observeSourceOutcome source.core pair.1)) := by
      apply FinDist.map_congr_of_eq_on_support
      intro ⟨cfg, next⟩ hpair
      obtain ⟨hcomplete, hclear, hdecode⟩ := hpairs cfg next hpair
      have hnext : next ∈ (runtime.roundDriver.runRounds principals serviceSlots
          (fun who => compilation.compileResolvingPolicy nullValue window who (profile who))
          wire total (PolicyExecution.initial _ (State.initial _ runtime.initial))).support := by
        rw [← hnative, FinDist.support_map]
        exact ⟨(cfg, next), hpair, rfl⟩
      have hinvariant := runtime.runRounds_eventInvariant principals serviceSlots _ wire total
        _ next SealedResolution.EventInvariant.initial hnext
      have hobservable : observeSourceOutcome source.core cfg ∈
          ((denoteSource source.core.prog profile source.core.env).map some).support := by
        rw [← hsource, FinDist.support_map]
        exact ⟨(cfg, next), hpair, rfl⟩
      rw [FinDist.support_map] at hobservable
      obtain ⟨final, _, hfinal⟩ := hobservable
      have hterminal : Terminal (compile source.core).graph cfg.1 := by
        by_contra hnot
        rw [(observeSourceOutcome_eq_none_iff source.core cfg).mpr hnot] at hfinal
        exact Option.some_ne_none _ hfinal
      have hpayout := evalPayoffs?_eq_decodedSourceOutcome source.core.prog source.core.fresh
        (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
        cfg hterminal
      change (runtime.complete next.native.application.visible,
        next.native.application.visible.timeouts,
        compilation.publicPayout? next.native.application.visible.events) =
          summarize (observeSourceOutcome source.core cfg)
      rw [hcomplete, hclear, compilation.publicPayout?_eq_graph_of_decode nullValue window
        next.native.application hinvariant cfg.1 hdecode,
        observeSourceOutcome_of_terminal source.core cfg hterminal]
      exact congrArg (fun payout => (true, ([] : List Nat), payout)) hpayout
    _ = _ := by
      have hmapped := congrArg (FinDist.map summarize) hsource
      simpa only [FinDist.map_comp, Function.comp_def, summarize, Option.map_some] using hmapped

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.candidate_honest_round_payout_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_honest_round_payout_law
