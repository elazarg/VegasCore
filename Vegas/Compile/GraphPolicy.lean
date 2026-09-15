/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.GraphCompiler

/-! # Source and graph policy translations

Policy translation preserves the acting player's observation and authenticated
own-action history. Every graph policy has an exact source-policy preimage.
-/

noncomputable section
namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]

def encodeOwnAction : SourceProgram.OwnAction Player L → Graph.OwnAction Player L
  | .commit owner name payload choice =>
      .bind owner name payload (BoundValue.resultEquiv _ choice)
  | .reveal owner name disclose => .resolve owner name disclose

def decodeOwnAction : Graph.OwnAction Player L → SourceProgram.OwnAction Player L
  | .bind owner name payload choice =>
      .commit owner name payload ((BoundValue.resultEquiv _).symm choice)
  | .resolve owner name disclose => .reveal owner name disclose

omit [DecidableEq Player] R in
@[simp] theorem decode_encodeOwnAction (action : SourceProgram.OwnAction Player L) :
    decodeOwnAction (encodeOwnAction action) = action := by
  cases action <;> simp [encodeOwnAction, decodeOwnAction]

omit [DecidableEq Player] R in
@[simp] theorem encode_decodeOwnAction (action : Graph.OwnAction Player L) :
    encodeOwnAction (decodeOwnAction action) = action := by
  cases action <;> simp [encodeOwnAction, decodeOwnAction]

def encodeOwnHistory (history : List (SourceProgram.OwnAction Player L)) :
    List (Graph.OwnAction Player L) := history.map encodeOwnAction

def decodeOwnHistory (history : List (Graph.OwnAction Player L)) :
    List (SourceProgram.OwnAction Player L) := history.map decodeOwnAction

omit [DecidableEq Player] R in
@[simp] theorem decode_encodeOwnHistory
    (history : List (SourceProgram.OwnAction Player L)) :
    decodeOwnHistory (encodeOwnHistory history) = history := by
  induction history with
  | nil => rfl
  | cons action tail ih =>
      change decodeOwnAction (encodeOwnAction action) ::
          decodeOwnHistory (encodeOwnHistory tail) = action :: tail
      rw [decode_encodeOwnAction, ih]

omit [DecidableEq Player] R in
@[simp] theorem encode_decodeOwnHistory
    (history : List (Graph.OwnAction Player L)) :
    encodeOwnHistory (decodeOwnHistory history) = history := by
  induction history with
  | nil => rfl
  | cons action tail ih =>
      change encodeOwnAction (decodeOwnAction action) ::
          encodeOwnHistory (decodeOwnHistory tail) = action :: tail
      rw [encode_decodeOwnAction, ih]

def encodeHistory (history : SourceProgram.History Player L) : Graph.History Player L :=
  fun who => encodeOwnHistory (history who)

def decodeHistory (history : Graph.History Player L) : SourceProgram.History Player L :=
  fun who => decodeOwnHistory (history who)

omit [DecidableEq Player] R in
@[simp] theorem decode_encodeHistory (history : SourceProgram.History Player L) :
    decodeHistory (encodeHistory history) = history := by
  funext who
  simp [encodeHistory, decodeHistory]

omit [DecidableEq Player] R in
@[simp] theorem encode_decodeHistory (history : Graph.History Player L) :
    encodeHistory (decodeHistory history) = history := by
  funext who
  simp [encodeHistory, decodeHistory]

omit R in
@[simp] theorem decodeHistory_update_append (history : Graph.History Player L)
    (who : Player) (action : Graph.OwnAction Player L) :
    decodeHistory (Function.update history who (history who ++ [action])) =
      Function.update (decodeHistory history) who
        (decodeHistory history who ++ [decodeOwnAction action]) := by
  funext player
  by_cases same : player = who
  · subst player
    simp [decodeHistory, decodeOwnHistory]
  · simp [decodeHistory, decodeOwnHistory, same]

def decodeDecisionView {who : Player} {Γ : SourceCtx Player L}
    (map : PublicationMap (R := R) Γ)
    (view : Graph.DecisionView who (graphCtx (R := R) Γ)) :
    SourceProgram.DecisionView who Γ :=
  (decodeObservation map view.1, decodeOwnHistory view.2)

def encodeDecisionView {who : Player} {Γ : SourceCtx Player L}
    (view : SourceProgram.DecisionView who Γ) :
    Graph.DecisionView who (graphCtx (R := R) Γ) :=
  (encodeObservation view.1, encodeOwnHistory view.2)

omit [DecidableEq Player] in
@[simp] theorem encode_decodeDecisionView {who : Player} {Γ : SourceCtx Player L}
    (map : PublicationMap (R := R) Γ)
    (view : Graph.DecisionView who (graphCtx (R := R) Γ)) :
    encodeDecisionView (decodeDecisionView map view) = view := by
  cases view
  simp [encodeDecisionView, decodeDecisionView, encode_decode_observation]

/-- Compile one player's source policy along exactly the compiler's layout
state transitions. -/
def compileGraphPolicy : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (unique : (Γ.map Prod.fst).Nodup) → (map : PublicationMap (R := R) Γ) →
    (registry : Registry Γ) → (who : Player) → BehavioralPolicy who program →
    Graph.BehavioralPolicy who (compileGraph program unique map registry)
  | _, _, .ret _, _, _, _, _, _ => PUnit.unit
  | _, _, .sample _ fresh _ next, unique, map, registry, who, policy =>
      compileGraphPolicy next (by simp [fresh, unique]) (weakenMap map)
        registry.weaken who policy
  | _, _, .commit name owner fresh guard next, unique, map, registry, who, policy =>
      let obligation : Obligation _ :=
        { owner := owner, subject := name, payload := _, source := .here,
          guard := guard.weaken }
      (fun same view =>
          FinDist.map (BoundValue.resultEquiv _)
            (policy.1 same (decodeDecisionView map view)),
        compileGraphPolicy next (by simp [fresh, unique]) (weakenMap map)
          (obligation :: registry.weaken) who policy.2)
  | Γ, _, .reveal published _ _ (payload := payload) fresh source _ next,
      unique, map, registry, who, policy =>
      let nextMap : PublicationMap (R := R)
          ((published, .publication payload) :: Γ) :=
        resolveMap map unique source (published := published)
      (fun same view => policy.1 same (decodeDecisionView map view),
        compileGraphPolicy next (by simp [fresh, unique]) nextMap registry.weaken who policy.2)

/-- Pull an arbitrary graph policy back to a source policy. -/
def backtranslateGraphPolicy : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (unique : (Γ.map Prod.fst).Nodup) → (map : PublicationMap (R := R) Γ) →
    (registry : Registry Γ) → (who : Player) →
    Graph.BehavioralPolicy who (compileGraph program unique map registry) →
    BehavioralPolicy who program
  | _, _, .ret _, _, _, _, _, _ => PUnit.unit
  | _, _, .sample _ fresh _ next, unique, map, registry, who, policy =>
      backtranslateGraphPolicy next (by simp [fresh, unique]) (weakenMap map)
        registry.weaken who policy
  | _, _, .commit name owner fresh guard next, unique, map, registry, who, policy =>
      let obligation : Obligation _ :=
        { owner := owner, subject := name, payload := _, source := .here,
          guard := guard.weaken }
      (fun same view =>
          FinDist.map (BoundValue.resultEquiv _).symm
            (policy.1 same (encodeDecisionView view)),
        backtranslateGraphPolicy next (by simp [fresh, unique]) (weakenMap map)
          (obligation :: registry.weaken) who policy.2)
  | Γ, _, .reveal published _ _ (payload := payload) fresh source _ next,
      unique, map, registry, who, policy =>
      let nextMap : PublicationMap (R := R)
          ((published, .publication payload) :: Γ) :=
        resolveMap map unique source (published := published)
      (fun same view => policy.1 same (encodeDecisionView view),
        backtranslateGraphPolicy next (by simp [fresh, unique]) nextMap
          registry.weaken who policy.2)

/-- Backtranslation is a right inverse: every graph policy is represented
exactly, including at graph views not reachable from an honest source run. -/
theorem compileGraphPolicy_backtranslate : {Γ : SourceCtx Player L} →
    {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (unique : (Γ.map Prod.fst).Nodup) → (map : PublicationMap (R := R) Γ) →
    (registry : Registry Γ) → (who : Player) →
    (policy : Graph.BehavioralPolicy who (compileGraph program unique map registry)) →
    compileGraphPolicy program unique map registry who
      (backtranslateGraphPolicy program unique map registry who policy) = policy
  | _, _, .ret _, _, _, _, _, policy => by cases policy; rfl
  | _, _, .sample _ fresh _ next, unique, map, registry, who, policy => by
      simp only [compileGraphPolicy, backtranslateGraphPolicy]
      exact compileGraphPolicy_backtranslate next (by simp [fresh, unique])
        (weakenMap map) registry.weaken who policy
  | _, _, .commit _ _ fresh _ next, unique, map, registry, who, policy => by
      simp only [compileGraphPolicy, backtranslateGraphPolicy]
      apply Prod.ext
      · funext same view
        simp only [encode_decodeDecisionView]
        rw [FinDist.map_comp]
        convert FinDist.map_id (policy.1 same view) using 1
        congr 1
        funext choice
        exact Equiv.apply_symm_apply _ choice
      · exact compileGraphPolicy_backtranslate next (by simp [fresh, unique])
          (weakenMap map) _ who policy.2
  | _, _, .reveal published _ _ fresh source _ next, unique, map, registry, who,
      policy => by
      simp only [compileGraphPolicy, backtranslateGraphPolicy]
      apply Prod.ext
      · funext same view
        simp
      · exact compileGraphPolicy_backtranslate next (by simp [fresh, unique])
          (resolveMap map unique source (published := published)) registry.weaken who policy.2

end Vegas.SourceProgram
