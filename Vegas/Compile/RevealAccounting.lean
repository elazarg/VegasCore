/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Core.AccountingIntegrity
import Vegas.Compile.FieldMap
import Vegas.Compile.DecisionSite
import Vegas.Compile.SourceOutcome
import Vegas.EventGraph.Disclosure

/-! # Accounting uniqueness for compiled reveal producers -/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A literal source reveal occurrence. -/
private inductive SourceRevealSite : {Γ : VCtx P L} → VegasCore P L Γ → Type where
  | here {Γ} {publicName sourceName : VarId} {who : P} {ty : L.Ty}
      {source : VHasVar Γ sourceName (.sealed who ty)} {tail} :
      SourceRevealSite (.reveal publicName who sourceName source tail)
  | sample {Γ} {name} {ty} {dist} {tail : VegasCore P L ((name, .pub ty) :: Γ)} :
      SourceRevealSite tail → SourceRevealSite (.sample name dist tail)
  | commit {Γ} {name} {who} {ty} {guard} {tail : VegasCore P L ((name, .sealed who ty) :: Γ)} :
      SourceRevealSite tail → SourceRevealSite (.commit name who guard tail)
  | reveal {Γ} {publicName sourceName} {who} {ty} {source}
      {tail : VegasCore P L ((publicName, .pub ty) :: Γ)} :
      SourceRevealSite tail → SourceRevealSite (.reveal publicName who sourceName source tail)

namespace SourceRevealSite

private def sourceName : {Γ : VCtx P L} → {prog : VegasCore P L Γ} →
    SourceRevealSite prog → VarId
  | _, _, .here (sourceName := name) => name
  | _, _, .sample site | _, _, .commit site | _, _, .reveal site => site.sourceName

private def terminalBinding : {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
    {name : VarId} → {bindTy : BindTy P L} → VHasVar Γ name bindTy →
      VHasVar (sourceTerminalCtx prog) name bindTy
  | _, .ret _, _, _, binding => binding
  | _, .sample _ _ tail, _, _, binding => terminalBinding tail (.there binding)
  | _, .commit _ _ _ tail, _, _, binding => terminalBinding tail (.there binding)
  | _, .reveal _ _ _ _ tail, _, _, binding => terminalBinding tail (.there binding)

private theorem terminalBinding_fieldOf : {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
    (fresh : FreshBindings prog) → (state : BuildState P L Γ) →
    {name : VarId} → {bindTy : BindTy P L} → (binding : VHasVar Γ name bindTy) →
    (compileCore prog fresh state).terminalState.fieldOf
      ((compileCore_terminalCtx_eq_sourceTerminalCtx prog fresh state).symm ▸
        terminalBinding prog binding) =
      state.fieldOf binding
  | _, .ret _, _, _, _, _, _ => rfl
  | _, .sample name dist tail, fresh, state, _, _, binding => by
      simpa [terminalBinding, compileCore] using
        terminalBinding_fieldOf tail fresh.2
          (state.addSampleEvent name dist fresh.1).1 (.there binding)
  | _, .commit name who guard tail, fresh, state, _, _, binding => by
      simpa [terminalBinding, compileCore] using
        terminalBinding_fieldOf tail fresh.2
          (state.addCommitEvent name who guard fresh.1).1 (.there binding)
  | _, .reveal name who sourceName source tail, fresh, state, _, _, binding => by
      simpa [terminalBinding, compileCore] using
        terminalBinding_fieldOf tail fresh.2
          (state.addRevealEvent name who source fresh.1).1 (.there binding)

private def sourceField : {Γ : VCtx P L} → {prog : VegasCore P L Γ} →
    SourceRevealSite prog → FreshBindings prog → BuildState P L Γ → Nat
  | _, .reveal _ _ _ source _, .here, _, state => state.fieldOf source
  | _, .sample name dist _, .sample site, fresh, state =>
      site.sourceField fresh.2 (state.addSampleEvent name dist fresh.1).1
  | _, .commit name who guard _, .commit site, fresh, state =>
      site.sourceField fresh.2 (state.addCommitEvent name who guard fresh.1).1
  | _, .reveal name who _ source _, .reveal site, fresh, state =>
      site.sourceField fresh.2 (state.addRevealEvent name who source fresh.1).1

private theorem exists_terminalSource_fieldOf : {Γ : VCtx P L} →
    {prog : VegasCore P L Γ} →
    (site : SourceRevealSite prog) → (fresh : FreshBindings prog) →
    (state : BuildState P L Γ) →
    ∃ who ty, ∃ binding : VHasVar (compileCore prog fresh state).terminalCtx
        site.sourceName (.sealed who ty),
      (compileCore prog fresh state).terminalState.fieldOf binding =
        site.sourceField fresh state
  | _, .reveal name who sourceName source tail, .here, fresh, state => by
      let binding :=
        (compileCore_terminalCtx_eq_sourceTerminalCtx tail fresh.2
          (state.addRevealEvent name who source fresh.1).1).symm ▸
            terminalBinding tail (.there source)
      refine ⟨who, _, binding, ?_⟩
      have ih := terminalBinding_fieldOf tail fresh.2
        (state.addRevealEvent name who source fresh.1).1 (.there source)
      simpa [sourceField, compileCore] using ih
  | _, .sample _ _ _, .sample site, fresh, state => by
      exact site.exists_terminalSource_fieldOf fresh.2 _
  | _, .commit _ _ _ _, .commit site, fresh, state => by
      exact site.exists_terminalSource_fieldOf fresh.2 _
  | _, .reveal _ _ _ _ _, .reveal site, fresh, state => by
      exact site.exists_terminalSource_fieldOf fresh.2 _

private def depth : {Γ : VCtx P L} → {prog : VegasCore P L Γ} →
    SourceRevealSite prog → Nat
  | _, _, .here => 0
  | _, _, .sample site | _, _, .commit site | _, _, .reveal site => site.depth + 1

private theorem sourceName_mem : {Γ : VCtx P L} → {prog : VegasCore P L Γ} →
    (site : SourceRevealSite prog) → site.sourceName ∈ RevealedSources prog
  | _, _, .here => by simp [sourceName, RevealedSources]
  | _, _, .sample site => by simpa [sourceName, RevealedSources] using site.sourceName_mem
  | _, _, .commit site => by simpa [sourceName, RevealedSources] using site.sourceName_mem
  | _, _, .reveal site => by
      exact List.mem_cons_of_mem _ (by simpa [sourceName] using site.sourceName_mem)

private theorem depth_eq_of_sourceName_eq : {Γ : VCtx P L} →
    {prog : VegasCore P L Γ} →
    (hnodup : (RevealedSources prog).Nodup) → (left right : SourceRevealSite prog) →
    left.sourceName = right.sourceName → left.depth = right.depth
  | _, .ret _, _, left, _, _ => nomatch left
  | _, .sample _ _ _, h, .sample left, .sample right, heq => by
      exact congrArg (fun n : Nat => n + 1)
        (depth_eq_of_sourceName_eq (by simpa [RevealedSources] using h) left right heq)
  | _, .commit _ _ _ _, h, .commit left, .commit right, heq => by
      exact congrArg (fun n : Nat => n + 1)
        (depth_eq_of_sourceName_eq (by simpa [RevealedSources] using h) left right heq)
  | _, .reveal _ _ sourceName _ _, h, left, right, heq => by
      cases left with
      | here =>
          cases right with
          | here => rfl
          | reveal right =>
              have hn := List.nodup_cons.mp (by simpa [RevealedSources] using h)
              have hm := right.sourceName_mem
              change sourceName = right.sourceName at heq
              rw [← heq] at hm
              exact False.elim (hn.1 hm)
      | reveal left =>
          cases right with
          | here =>
              have hn := List.nodup_cons.mp (by simpa [RevealedSources] using h)
              have hm := left.sourceName_mem
              change left.sourceName = sourceName at heq
              rw [heq] at hm
              exact False.elim (hn.1 hm)
          | reveal right =>
              exact congrArg (fun n : Nat => n + 1)
                (depth_eq_of_sourceName_eq
                  (List.nodup_cons.mp (by simpa [RevealedSources] using h)).2 left right heq)

end SourceRevealSite

private def CompiledRevealAt {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (node : Fin (compileCore prog fresh state).graph.nodeCount) : Prop :=
  ∃ site : SourceRevealSite prog,
    (node : Nat) = state.nodes.length + site.depth ∧
      ((compileCore prog fresh state).graph.nodeRow node).sem =
        .reveal (site.sourceField fresh state)

private theorem currentNode_sem
    {Γ : VCtx P L} (state : BuildState P L Γ) (event : EventNode P L)
    (result : BuildResult P L) (hprefix : state.nodes ++ [event] <+: result.nodes)
    (node : Fin result.graph.nodeCount) (hnode : (node : Nat) = state.nodes.length) :
    result.graph.nodeRow node = event := by
  apply Option.some.inj
  rw [← result.graph.nodes_get?_nodeRow node]
  change result.nodes[(node : Nat)]? = some event
  rcases hprefix with ⟨suffix, hsuffix⟩
  rw [← hsuffix, hnode]
  simp

private theorem compileCore_revealNode_covered :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) → (fresh : FreshBindings prog) →
    (state : BuildState P L Γ) →
    (node : Fin (compileCore prog fresh state).graph.nodeCount) →
    state.nodes.length ≤ (node : Nat) → ∀ source,
    ((compileCore prog fresh state).graph.nodeRow node).sem = .reveal source →
      CompiledRevealAt prog fresh state node
  | _, .ret _, _, state, node, hnew, _, _ => by
      have := node.isLt
      change (node : Nat) < state.nodes.length at this
      omega
  | Γ, .sample name dist tail, fresh, state, node, hnew, source, hsem => by
      let event := state.sampleEvent dist
      let added := state.addSampleEvent name dist fresh.1
      let result := compileCore tail fresh.2 added.1
      have hp : state.nodes ++ [event] <+: result.nodes := by
        simpa [added, event] using compileCore_nodes_prefix tail fresh.2 added.1
      by_cases hc : (node : Nat) = state.nodes.length
      · change (result.graph.nodeRow node).sem = .reveal source at hsem
        have hr := currentNode_sem state event result hp node hc
        rw [hr] at hsem
        simp [event] at hsem
      · have hl : added.1.nodes.length ≤ (node : Nat) := by simp [added]; omega
        obtain ⟨site, hi, hs⟩ :=
          compileCore_revealNode_covered tail fresh.2 added.1 node hl source hsem
        refine ⟨.sample site, ?_, hs⟩
        simp [SourceRevealSite.depth, added] at hi ⊢
        omega
  | Γ, .commit name who guard tail, fresh, state, node, hnew, source, hsem => by
      let event := state.commitEvent who guard
      let added := state.addCommitEvent name who guard fresh.1
      let result := compileCore tail fresh.2 added.1
      have hp : state.nodes ++ [event] <+: result.nodes := by
        simpa [added, event] using compileCore_nodes_prefix tail fresh.2 added.1
      by_cases hc : (node : Nat) = state.nodes.length
      · change (result.graph.nodeRow node).sem = .reveal source at hsem
        have hr := currentNode_sem state event result hp node hc
        rw [hr] at hsem
        simp [event] at hsem
      · have hl : added.1.nodes.length ≤ (node : Nat) := by simp [added]; omega
        obtain ⟨site, hi, hs⟩ :=
          compileCore_revealNode_covered tail fresh.2 added.1 node hl source hsem
        refine ⟨.commit site, ?_, hs⟩
        simp [SourceRevealSite.depth, added] at hi ⊢
        omega
  | Γ, .reveal name who sourceName sourceProof tail, fresh, state, node, hnew,
      source, hsem => by
      let event := state.revealEvent who sourceProof
      let added := state.addRevealEvent name who sourceProof fresh.1
      let result := compileCore tail fresh.2 added.1
      have hp : state.nodes ++ [event] <+: result.nodes := by
        simpa [added, event] using compileCore_nodes_prefix tail fresh.2 added.1
      by_cases hc : (node : Nat) = state.nodes.length
      · refine ⟨.here, by simpa [SourceRevealSite.depth] using hc, ?_⟩
        change (result.graph.nodeRow node).sem = _
        rw [currentNode_sem state event result hp node hc]
        rfl
      · have hl : added.1.nodes.length ≤ (node : Nat) := by simp [added]; omega
        obtain ⟨site, hi, hs⟩ :=
          compileCore_revealNode_covered tail fresh.2 added.1 node hl source hsem
        refine ⟨.reveal site, ?_, hs⟩
        simp [SourceRevealSite.depth, added] at hi ⊢
        omega

end Vegas.ToEventGraph

namespace Vegas.WFProgram

open ToEventGraph EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A checked compilation has at most one direct reveal of any source field. -/
theorem compiled_uniqueReveals (source : WFProgram P L) :
    (compile source.core).graph.UniqueReveals := by
  intro left right field hleft hright
  let state := BuildState.fromInitial
    (initialState source.core.Γ source.core.env source.core.wctx)
  obtain ⟨leftSite, hleftIndex, hleftField⟩ :=
    compileCore_revealNode_covered source.core.prog source.core.fresh state left
      (by simp [state]) field hleft
  obtain ⟨rightSite, hrightIndex, hrightField⟩ :=
    compileCore_revealNode_covered source.core.prog source.core.fresh state right
      (by simp [state]) field hright
  have hfields : leftSite.sourceField source.core.fresh state =
      rightSite.sourceField source.core.fresh state := by
    have hl : NodeSem.reveal (leftSite.sourceField source.core.fresh state) =
        NodeSem.reveal field := hleftField.symm.trans (by simpa [compile, state] using hleft)
    have hr : NodeSem.reveal (rightSite.sourceField source.core.fresh state) =
        NodeSem.reveal field := hrightField.symm.trans (by simpa [compile, state] using hright)
    exact NodeSem.reveal.inj (hl.trans hr.symm)
  have hnames : leftSite.sourceName = rightSite.sourceName := by
    obtain ⟨leftOwner, leftTy, leftBinding, hleftBinding⟩ :=
      leftSite.exists_terminalSource_fieldOf source.core.fresh state
    obtain ⟨rightOwner, rightTy, rightBinding, hrightBinding⟩ :=
      rightSite.exists_terminalSource_fieldOf source.core.fresh state
    apply compileCore_terminal_fieldOfNameInjective source.core.prog source.core.fresh state
      (BuildState.fromInitial_fieldOfNameInjective _
        (initialState_fieldOfNameInjective source.core.env source.core.wctx))
      leftBinding rightBinding
    exact hleftBinding.trans (hfields.trans hrightBinding.symm)
  have hdepth := SourceRevealSite.depth_eq_of_sourceName_eq
    (source.accounted.revealedSources_nodup source.core.fresh sealedVars_toFinset_scoped)
    leftSite rightSite hnames
  apply Fin.ext
  omega

end Vegas.WFProgram
