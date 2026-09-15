/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SourceOutcome
import Vegas.EventGraph.PublicUtility

/-! # Public terminal source outcomes

The compiler's terminal field map can decode the public projection of a source
outcome from an arbitrary graph store without consulting sealed fields. On a
reachable terminal graph configuration this partial decoder agrees with the
public projection of the complete source decoder.
-/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A compiler terminal field allocated for a public source binding is a
declared public graph field with the same type. -/
theorem BuildResult.terminalFieldRefPublic (result : BuildResult P L)
    {name : VarId} {ty : L.Ty}
    (binding : HasVar (erasePubVCtx result.terminalCtx) name ty) :
    result.graph.fieldRefPublic (result.terminalState.fieldRefOfPub binding) := by
  rw [← result.terminal_graph_eq]
  unfold BuildState.fieldRefOfPub BuildState.fieldOfPub
  rcases result.terminalState.fieldOf_spec
      (VHasVar.ofPubVCtx (HasVar.toVHasVarPub binding)) with
    ⟨spec, hspec, hty, howner⟩
  exact ⟨spec, hspec, hty, howner⟩

/-- Reconstruct the public terminal source environment when all of its
compiler-allocated typed fields are present. -/
def BuildResult.publicTerminalEnv (result : BuildResult P L) (store : Store L)
    (available : ∀ {name ty}
      (binding : HasVar (erasePubVCtx result.terminalCtx) name ty),
      ∃ value, Store.getAs store
        (result.terminalState.fieldOfPub binding) ty = some value) :
    Env L.Val (erasePubVCtx result.terminalCtx) :=
  fun _name _ty binding => Classical.choose (available binding)

/-- Decode exactly the public source bindings in a compiler terminal context.
The decoder is partial on arbitrary stores and never reads a sealed field. -/
def BuildResult.decodePublicTerminal? (result : BuildResult P L) (store : Store L) :
    Option (Env L.Val (erasePubVCtx result.terminalCtx)) := by
  classical
  exact if available : ∀ {name ty}
      (binding : HasVar (erasePubVCtx result.terminalCtx) name ty),
      ∃ value, Store.getAs store
        (result.terminalState.fieldOfPub binding) ty = some value then
    some (result.publicTerminalEnv store available)
  else
    none

/-- Successful public decoding returns the typed value stored at each
compiler-allocated public field. -/
theorem BuildResult.decodePublicTerminal?_eq_some_of_getAs
    (result : BuildResult P L) (store : Store L)
    (env : Env L.Val (erasePubVCtx result.terminalCtx))
    (hget : ∀ {name ty}
      (binding : HasVar (erasePubVCtx result.terminalCtx) name ty),
      Store.getAs store (result.terminalState.fieldOfPub binding) ty =
        some (env.get binding)) :
    result.decodePublicTerminal? store = some env := by
  let available : ∀ {name ty}
      (binding : HasVar (erasePubVCtx result.terminalCtx) name ty),
      ∃ value, Store.getAs store
        (result.terminalState.fieldOfPub binding) ty = some value :=
    fun binding => ⟨env.get binding, hget binding⟩
  unfold BuildResult.decodePublicTerminal?
  split
  · rename_i actual
    congr 1
    funext name ty binding
    unfold BuildResult.publicTerminalEnv
    exact Option.some.inj
      ((Classical.choose_spec (actual binding)).symm.trans (hget binding))
  · rename_i absent
    exact (absent available).elim

/-- Public decoding is extensional in precisely the compiler-allocated public
typed fields. -/
theorem BuildResult.decodePublicTerminal?_eq_of_getAs_eq
    (result : BuildResult P L) (left right : Store L)
    (hget : ∀ {name ty}
      (binding : HasVar (erasePubVCtx result.terminalCtx) name ty),
      Store.getAs left (result.terminalState.fieldOfPub binding) ty =
        Store.getAs right (result.terminalState.fieldOfPub binding) ty) :
    result.decodePublicTerminal? left = result.decodePublicTerminal? right := by
  let Available := fun store : Store L =>
    ∀ {name ty} (binding : HasVar (erasePubVCtx result.terminalCtx) name ty),
      ∃ value, Store.getAs store
        (result.terminalState.fieldOfPub binding) ty = some value
  have havailable : Available left ↔ Available right := by
    constructor
    · intro hleft name ty binding
      rcases hleft binding with ⟨value, hvalue⟩
      exact ⟨value, (hget binding).symm.trans hvalue⟩
    · intro hright name ty binding
      rcases hright binding with ⟨value, hvalue⟩
      exact ⟨value, (hget binding).trans hvalue⟩
  unfold BuildResult.decodePublicTerminal?
  split
  · rename_i hleft
    split
    · rename_i hright
      congr 1
      funext name ty binding
      unfold BuildResult.publicTerminalEnv
      have hleftValue := Classical.choose_spec (hleft binding)
      have hrightValue := Classical.choose_spec (hright binding)
      exact Option.some.inj
        (hleftValue.symm.trans ((hget binding).trans hrightValue))
    · rename_i hright
      exact (hright (havailable.mp hleft)).elim
  · rename_i hleft
    split
    · rename_i hright
      exact (hleft (havailable.mpr hright)).elim
    · rfl

/-- Equality on all declared public graph fields is sufficient for equality of
the public source decoder. -/
theorem BuildResult.decodePublicTerminal?_eq_of_publicFields_eq
    (result : BuildResult P L) (left right : Store L)
    (hpublic : ∀ ref, result.graph.fieldRefPublic ref →
      Store.getAs left ref.field ref.ty = Store.getAs right ref.field ref.ty) :
    result.decodePublicTerminal? left = result.decodePublicTerminal? right := by
  apply result.decodePublicTerminal?_eq_of_getAs_eq
  intro name ty binding
  exact hpublic (result.terminalState.fieldRefOfPub binding)
    (result.terminalFieldRefPublic binding)

/-- At a reachable terminal graph state, public decoding returns the public
projection of the complete compiler/source decoder. -/
theorem BuildResult.decodePublicTerminal?_terminal
    (result : BuildResult P L) (cfg : ReachableConfig result.graph)
    (hterminal : Terminal result.graph cfg.1) :
    result.decodePublicTerminal? cfg.1.store =
      some (result.decodeTerminalSource cfg hterminal).erasePubEnv := by
  apply result.decodePublicTerminal?_eq_some_of_getAs
  intro name ty binding
  change Store.getAs cfg.1.store (result.terminalState.fieldOfPub binding) ty =
    some (VEnv.erasePubEnv (result.decodeTerminalSource cfg hterminal) name ty binding)
  rw [VEnv.erasePubEnv_get]
  exact sourceEnvOfStore_get result.terminalState cfg.1.store
    (result.terminalBindingAvailable cfg hterminal)
    (VHasVar.ofPubVCtx (HasVar.toVHasVarPub binding))

end Vegas.ToEventGraph

namespace Vegas.WFProgram

open EventGraph ToEventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

omit [DecidableEq Player] in
private theorem cast_publicProjection {Γ Δ : VCtx Player L} (hctx : Γ = Δ)
    (env : VEnv L Γ) :
    cast (congrArg (fun context => Option (Env L.Val (erasePubVCtx context))) hctx)
        (some env.erasePubEnv) =
      some (cast (congrArg (fun context => VEnv L context) hctx) env).erasePubEnv := by
  cases hctx
  rfl

/-- Decode the public terminal written-source environment from an arbitrary
store of the compiled graph. -/
def publicSourceOutcome? (source : WFProgram Player L) (store : Store L) :
    Option (Env L.Val (erasePubVCtx (sourceTerminalCtx source.core.prog))) :=
  let hctx := compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog
    source.core.fresh
      (BuildState.fromInitial
        (initialState source.core.Γ source.core.env source.core.wctx))
  cast (congrArg (fun Γ => Option (Env L.Val (erasePubVCtx Γ))) hctx)
    ((compile source.core).decodePublicTerminal? store)

/-- The source-facing public decoder depends only on declared public graph
fields. -/
theorem publicSourceOutcome?_eq_of_publicFields_eq
    (source : WFProgram Player L) (left right : Store L)
    (hpublic : ∀ ref, (compile source.core).graph.fieldRefPublic ref →
      Store.getAs left ref.field ref.ty = Store.getAs right ref.field ref.ty) :
    source.publicSourceOutcome? left = source.publicSourceOutcome? right := by
  unfold publicSourceOutcome?
  exact congrArg _
    ((compile source.core).decodePublicTerminal?_eq_of_publicFields_eq left right hpublic)

/-- On a reachable terminal compiled configuration, public source decoding is
the public projection of `decodeSourceOutcome`. -/
theorem publicSourceOutcome?_terminal (source : WFProgram Player L)
    (cfg : ReachableConfig (compile source.core).graph)
    (hterminal : Terminal (compile source.core).graph cfg.1) :
    source.publicSourceOutcome? cfg.1.store =
      some (decodeSourceOutcome source.core.prog source.core.fresh
        (BuildState.fromInitial
          (initialState source.core.Γ source.core.env source.core.wctx))
        cfg hterminal).erasePubEnv := by
  let hctx := compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog
    source.core.fresh
      (BuildState.fromInitial
        (initialState source.core.Γ source.core.env source.core.wctx))
  let decoded := (compile source.core).decodeTerminalSource cfg hterminal
  calc
    source.publicSourceOutcome? cfg.1.store =
        cast (congrArg (fun context => Option (Env L.Val (erasePubVCtx context))) hctx)
          (some decoded.erasePubEnv) := by
      unfold publicSourceOutcome?
      exact congrArg _
        ((compile source.core).decodePublicTerminal?_terminal cfg hterminal)
    _ = some (cast (congrArg (fun context => VEnv L context) hctx) decoded).erasePubEnv :=
      cast_publicProjection hctx decoded
    _ = some (decodeSourceOutcome source.core.prog source.core.fresh
        (BuildState.fromInitial
          (initialState source.core.Γ source.core.env source.core.wctx))
        cfg hterminal).erasePubEnv := by
      rfl

/-- Interpret arbitrary public terminal source outcomes as graph utilities.
Stores missing a public terminal field use the supplied fallback. -/
def graphPublicUtility (source : WFProgram Player L)
    (interpretation :
      Env L.Val (erasePubVCtx (sourceTerminalCtx source.core.prog)) → Player → ℝ)
    (missing : Player → ℝ) : (compile source.core).graph.PublicUtility where
  eval store who := (source.publicSourceOutcome? store).elim
    (missing who) (fun outcome => interpretation outcome who)
  congr left right hpublic who := by
    rw [source.publicSourceOutcome?_eq_of_publicFields_eq left right hpublic]

/-- The public graph utility evaluates a terminal compiled configuration by
interpreting the decoded public written-source outcome. -/
theorem graphPublicUtility_terminal (source : WFProgram Player L)
    (interpretation :
      Env L.Val (erasePubVCtx (sourceTerminalCtx source.core.prog)) → Player → ℝ)
    (missing : Player → ℝ)
    (cfg : ReachableConfig (compile source.core).graph)
    (hterminal : Terminal (compile source.core).graph cfg.1) (who : Player) :
    (source.graphPublicUtility interpretation missing).eval cfg.1.store who =
      interpretation
        (decodeSourceOutcome source.core.prog source.core.fresh
          (BuildState.fromInitial
            (initialState source.core.Γ source.core.env source.core.wctx))
          cfg hterminal).erasePubEnv who := by
  change (source.publicSourceOutcome? cfg.1.store).elim (missing who)
    (fun outcome => interpretation outcome who) = _
  rw [source.publicSourceOutcome?_terminal cfg hterminal]
  rfl

end Vegas.WFProgram

/-- info: 'Vegas.ToEventGraph.BuildResult.decodePublicTerminal?_terminal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ToEventGraph.BuildResult.decodePublicTerminal?_terminal

/-- info: 'Vegas.WFProgram.graphPublicUtility_terminal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.graphPublicUtility_terminal
