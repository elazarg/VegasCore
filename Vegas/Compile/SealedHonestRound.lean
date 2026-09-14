/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedHonestGraphRound
import Vegas.Compile.SourceCorrespondence

/-! # Original source outcomes in the public pending-message driver

Periodic inclusion capacity and a sufficient timeout window ensure that the
all-compiled execution completes without defaults. The source/native
probability law then supplies an exact coupling with the original written
source profile. The native marginal is the actual early-stopping round driver,
not a separate execution or a postulated graph game. The wire policy may be
randomized and may adapt to its full pending-message observation.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Finite Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- End-to-end honest outcome preservation for the sealed pending-message
backend. Source kernels are unchanged. All supported pairs have normal native
completion and decode to the retained source realization. The assumptions
concern roster coverage, real inclusion capacity, the timeout window, and a
sufficient whole-period budget; acceptance and successful completion are
conclusions. No unilateral utility or equilibrium claim is made here. -/
theorem exists_honest_round_source_coupling
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
    ∃ coupling : FinDist (ReachableConfig (compile source.core).graph ×
        runtime.messageApplication.PolicyExecution),
      coupling.map (fun pair => observeSourceOutcome source.core pair.1) =
        (denoteSource source.core.prog profile source.core.env).map some ∧
      coupling.map Prod.snd =
        runtime.roundDriver.runRounds principals serviceSlots
          (fun who => compilation.compileResolvingPolicy nullValue window who (profile who))
          wire total (PolicyExecution.initial _ (State.initial _ runtime.initial)) ∧
      ∀ cfg next, (cfg, next) ∈ coupling.support →
        runtime.complete next.native.application.visible = true ∧
        next.native.application.visible.timeouts = [] ∧
        (compile source.core).graph.decodeSealedFrom ty next.native.application.service
          (Config.initial _) next.native.application.visible.events = some cfg.1 := by
  let : Fintype Player := Fintype.ofFinite Player
  intro runtime
  let graphProfile := fun who => compileSourcePolicy source.core.prog source.core.fresh
    (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
    rfl who (profile who)
  obtain ⟨coupling, hgraph, hnative, hpairs⟩ :=
    compilation.supported.exists_honest_round_graph_coupling
      (compile_guardLive source.core source.legal) nullValue window principals serviceSlots
      graphProfile wire reserved hservice period hperiod hcapacity hroster hwindow total
      hperiods hbound
  refine ⟨coupling, ?_, hnative, hpairs⟩
  have hmapped := congrArg (fun law => law.map (observeSourceOutcome source.core)) hgraph
  have hsource := source.sourceRealization_source profile
  exact (FinDist.map_comp _ _ _).symm.trans (hmapped.trans hsource)

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.exists_honest_round_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.exists_honest_round_source_coupling
