/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SourcePublicOutcome
import Vegas.Compile.SourceOutcomeExecution
import Vegas.Compile.RevealAccounting
import Vegas.Compile.SealedGraphSettlement

/-! # Public source outcomes of completed sealed states

The public terminal source decoder can be applied directly to a sealed event
log. Every completed state satisfying the public event invariant decodes to the
public projection of a legal terminal written-source execution, including
states completed through deadline defaults.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty}

/-- Recover all public terminal source bindings from the public event log.
Absent or ill-typed required fields produce `none`, independently of private
candidate preparation or accepted hidden values. -/
def publicSourceOutcome? (_compilation : SealedCompilation source ty)
    (events : List (SealedProgram.Event Player (L.Val ty))) :
    Option (Env L.Val (erasePubVCtx (sourceTerminalCtx source.core.prog))) :=
  source.publicSourceOutcome? ((compile source.core).graph.publicSealedStore ty events)

/-- Every completed invariant sealed state decodes to the public projection
of a legal terminal written-source outcome. No private registration value or
normal-completion premise is required. -/
theorem publicSourceOutcome?_source_of_complete [Finite Player]
    (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.PublicState Player (L.Val ty))
    (hinvariant : SealedResolution.PublicEventInvariant
      (compilation.supported.resolvingRuntime nullValue window) state)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      state = true) :
    ∃ final : VEnv L (sourceTerminalCtx source.core.prog),
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := sourceTerminalCtx source.core.prog, env := final,
          cont := .ret (sourceTerminalPayoffs source.core.prog) } ∧
      compilation.publicSourceOutcome? state.events = some final.erasePubEnv := by
  obtain ⟨cfg, hterminal, hagrees, _hdefaults⟩ :=
    compilation.supported.public_store_graph_of_complete
      (compile_guardLive source.core source.legal) source.compiled_uniqueReveals
      nullValue window state hinvariant hcomplete
  let final := decodeSourceOutcome source.core.prog source.core.fresh
    (BuildState.fromInitial
      (initialState source.core.Γ source.core.env source.core.wctx))
    cfg hterminal
  refine ⟨final, decodeSourceOutcome_reachable source.core cfg hterminal, ?_⟩
  unfold publicSourceOutcome?
  calc
    source.publicSourceOutcome?
        ((compile source.core).graph.publicSealedStore ty state.events) =
      source.publicSourceOutcome? cfg.1.store :=
        source.publicSourceOutcome?_eq_of_publicFields_eq _ _ hagrees
    _ = some final.erasePubEnv :=
      source.publicSourceOutcome?_terminal cfg hterminal

/-- Completion and the public event invariant make the native public source
decoder's missing branch unreachable. -/
theorem publicSourceOutcome?_isSome_of_complete [Finite Player]
    (compilation : SealedCompilation source ty)
    (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.PublicState Player (L.Val ty))
    (hinvariant : SealedResolution.PublicEventInvariant
      (compilation.supported.resolvingRuntime nullValue window) state)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      state = true) :
    (compilation.publicSourceOutcome? state.events).isSome := by
  obtain ⟨final, _hsource, hdecode⟩ :=
    compilation.publicSourceOutcome?_source_of_complete
      nullValue window state hinvariant hcomplete
  rw [hdecode]
  rfl

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.publicSourceOutcome?_source_of_complete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.publicSourceOutcome?_source_of_complete
