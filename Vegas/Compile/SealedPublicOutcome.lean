/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedGraphSettlement
import Vegas.Compile.RevealAccounting
import Vegas.EventGraph.Payoff

/-! # Source outcomes obtained from public graph settlement

The backend reconstructs graph realizations independently of source syntax.
The source compiler certifies disclosure uniqueness and transports their public
values to the programmed payout. Payout valuation remains an external utility.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph Interaction ToEventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty}

/-- The compiled source payout evaluated solely from public native data.
Applications may instead apply any utility or outcome map to `publicSealedStore`.
-/
def publicPayout? (_compilation : SealedCompilation source ty)
    (events : List (SealedProgram.Event Player (L.Val ty))) : Option (Payout Player) :=
  evalPayoffs? (ToEventGraph.compile source.core).payoffs
    ((ToEventGraph.compile source.core).graph.publicSealedStore ty events)

/-- Public payout evaluation is total at every invariant completed native
state, including after timeout defaults. -/
theorem publicPayout?_isSome_of_complete
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.PublicState Player (L.Val ty))
    (hinvariant : SealedResolution.PublicEventInvariant
      (compilation.supported.resolvingRuntime nullValue window) state)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      state = true) :
    ∃ payout, compilation.publicPayout? state.events = some payout := by
  apply evalPayoffs?_isSome_of_available
  intro payoff hpayoff ref href
  exact (compile source.core).graph.publicSealedStore_available_of_complete
    compilation.supported.graphWF compilation.supported.rowType compilation.supported.noSamples
    compilation.supported.revealSource (compilation.supported.resolvingRuntime nullValue window) rfl
    state hinvariant hcomplete ref
    ((ToEventGraph.compile source.core).payoffsWF payoff hpayoff ref href).1


/-- Agreement on typed public reads suffices to identify the programmed
payout. No commitment-service or private-store agreement is required. -/
theorem publicPayout?_eq_graph_of_public_store
    (compilation : SealedCompilation source ty)
    (events : List (SealedProgram.Event Player (L.Val ty))) (store : Store L)
    (hagrees : ∀ ref, (compile source.core).graph.fieldRefPublic ref →
      Store.getAs ((compile source.core).graph.publicSealedStore ty events) ref.field ref.ty =
        Store.getAs store ref.field ref.ty) :
    compilation.publicPayout? events = evalPayoffs? (compile source.core).payoffs store := by
  apply evalPayoffs?_eq_of_getAs_eq
  intro payoff hpayoff ref href
  exact hagrees ref ((compile source.core).payoffsWF payoff hpayoff ref href).1

private theorem payout_source_of_public_store
    (store : Store L) (cfg : ReachableConfig (compile source.core).graph)
    (hterminal : Terminal (compile source.core).graph cfg.1)
    (hagrees : ∀ ref, (compile source.core).graph.fieldRefPublic ref →
      Store.getAs store ref.field ref.ty = Store.getAs cfg.1.store ref.field ref.ty) :
    ∃ terminalEnv : VEnv L (compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (compile source.core).terminalCtx, env := terminalEnv,
          cont := .ret (compile source.core).sourcePayoffs } ∧
      evalPayoffs? (compile source.core).payoffs store =
        some (evalPayoffs (compile source.core).sourcePayoffs terminalEnv) := by
  obtain ⟨terminalEnv, hstar, hcfgPayout, _hbindings⟩ :=
    compile_sourceStar source.core cfg.1 cfg.2 hterminal
  refine ⟨terminalEnv, hstar, ?_⟩
  rw [evalPayoffs?_eq_of_getAs_eq (compile source.core).payoffs store cfg.1.store, hcfgPayout]
  intro payoff hpayoff ref href
  exact hagrees ref ((compile source.core).payoffsWF payoff hpayoff ref href).1

/-- On a successfully decoded native event log, public payout evaluation
agrees with graph payout evaluation. Private accepted values are not read by
the public evaluator. No terminal-state assumption is needed for this equality. -/
theorem publicPayout?_eq_graph_of_decode
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.ApplicationState Player (L.Val ty))
    (hinvariant : SealedResolution.EventInvariant
      (compilation.supported.resolvingRuntime nullValue window) state)
    (cfg : Config (compile source.core).graph)
    (hdecode : (compile source.core).graph.decodeSealedFrom ty state.service
      (Config.initial _) state.visible.events = some cfg) :
    compilation.publicPayout? state.visible.events =
      evalPayoffs? (compile source.core).payoffs cfg.store := by
  apply evalPayoffs?_eq_of_getAs_eq
  intro payoff hpayoff ref href
  exact compilation.supported.publicSealedStore_agrees nullValue window state hinvariant
    cfg hdecode ref ((compile source.core).payoffsWF payoff hpayoff ref href).1

/-- On every decoded terminal source realization, the payout loaded only from
public initial fields and opening events is exactly the written source payout.
The witness is supplied by source adequacy; no private commitment value is
read during public reconstruction. -/
theorem publicPayout?_eq_source_of_terminal
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.ApplicationState Player (L.Val ty))
    (hinvariant : SealedResolution.EventInvariant
      (compilation.supported.resolvingRuntime nullValue window) state)
    (cfg : ReachableConfig (ToEventGraph.compile source.core).graph)
    (hterminal : Terminal (ToEventGraph.compile source.core).graph cfg.1)
    (hdecode : (ToEventGraph.compile source.core).graph.decodeSealedFrom ty state.service
      (Config.initial _) state.visible.events = some cfg.1) :
    ∃ terminalEnv : VEnv L (ToEventGraph.compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (ToEventGraph.compile source.core).terminalCtx,
          env := terminalEnv,
          cont := .ret (ToEventGraph.compile source.core).sourcePayoffs } ∧
      compilation.publicPayout? state.visible.events =
        some (evalPayoffs (ToEventGraph.compile source.core).sourcePayoffs terminalEnv) := by
  exact payout_source_of_public_store _ cfg hterminal
    (compilation.supported.publicSealedStore_agrees nullValue window state hinvariant cfg.1 hdecode)

/-- Public settlement after arbitrary native completion equals the written
source payout of a legal source execution. This includes timeout defaults and
requires neither successful private-state decoding nor timely message service.
It is an existence statement, not a unilateral deviation-law backtranslation. -/
theorem publicPayout?_eq_source_of_complete [Finite Player]
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.PublicState Player (L.Val ty))
    (hinvariant : SealedResolution.PublicEventInvariant
      (compilation.supported.resolvingRuntime nullValue window) state)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      state = true) :
    ∃ terminalEnv : VEnv L (compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (compile source.core).terminalCtx, env := terminalEnv,
          cont := .ret (compile source.core).sourcePayoffs } ∧
      compilation.publicPayout? state.events =
        some (evalPayoffs (compile source.core).sourcePayoffs terminalEnv) := by
  obtain ⟨cfg, hterminal, hagrees, _⟩ :=
    compilation.supported.public_store_graph_of_complete
      (compile_guardLive source.core source.legal) source.compiled_uniqueReveals
      nullValue window state hinvariant hcomplete
  exact payout_source_of_public_store _ cfg hterminal hagrees

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.publicPayout?_eq_source_of_terminal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.publicPayout?_eq_source_of_terminal

/-- info: 'Vegas.SealedCompilation.publicPayout?_eq_source_of_complete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.publicPayout?_eq_source_of_complete
