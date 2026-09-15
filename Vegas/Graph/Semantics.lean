/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.Basic
import GameTheory.Core.Form

/-! # Policies and exact execution for typed immutable graphs -/

noncomputable section
namespace Vegas.Graph

open GameTheory GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]

def ObservationVal (L : IExpr) : BindTy Player L → Type
  | ⟨τ, .pub⟩ => L.Val τ
  | ⟨τ, .sealed _⟩ => Option (L.Val τ)

structure Observation (L : IExpr) (who : Player) (Γ : VCtx Player L) where
  cells : Env (ObservationVal (Player := Player) L) Γ

def observe (who : Player) {Γ : VCtx Player L} (env : VEnv L Γ) :
    Observation L who Γ :=
  ⟨fun _ binding h => match binding with
    | ⟨_, .pub⟩ => env.get h
    | ⟨_, .sealed owner⟩ => if owner = who then some (env.get h) else none⟩

inductive OwnAction (Player : Type) (L : IExpr) where
  | bind (owner : Player) (name : VarId) (payload : L.Ty)
      (choice : PublicationResult (L.Val payload))
  | resolve (owner : Player) (bindingName : VarId) (disclose : Bool)

abbrev History (Player : Type) (L : IExpr) := Player → List (OwnAction Player L)

abbrev DecisionView (who : Player) (Γ : VCtx Player L) :=
  Observation L who Γ × List (OwnAction Player L)

def BehavioralPolicy (who : Player) : {Γ Δ : VCtx Player L} → Graph Player L Γ Δ → Type
  | _, _, .ret _ => PUnit
  | _, _, .sample _ _ _ next => BehavioralPolicy who next
  | Γ, _, .bind (payload := payload) _ owner _ next =>
      ((owner = who) → DecisionView who Γ →
        FinDist (PublicationResult (L.Val payload))) × BehavioralPolicy who next
  | Γ, _, .resolve _ owner _ _ _ _ next =>
      ((owner = who) → DecisionView who Γ → FinDist Bool) × BehavioralPolicy who next

abbrev BehavioralProfile {Γ Δ : VCtx Player L} (graph : Graph Player L Γ Δ) :=
  ∀ who, BehavioralPolicy who graph

def failurePolicy (who : Player) : {Γ Δ : VCtx Player L} →
    (graph : Graph Player L Γ Δ) → BehavioralPolicy who graph
  | _, _, .ret _ => PUnit.unit
  | _, _, .sample _ _ _ next => failurePolicy who next
  | _, _, .bind _ _ _ next =>
      (fun _ _ => FinDist.pure .failure, failurePolicy who next)
  | _, _, .resolve _ _ _ _ _ _ next =>
      (fun _ _ => FinDist.pure false, failurePolicy who next)

def failureProfile {Γ Δ : VCtx Player L} (graph : Graph Player L Γ Δ) :
    BehavioralProfile graph := fun who => failurePolicy who graph

theorem behavioralProfile_nonempty {Γ Δ : VCtx Player L} (graph : Graph Player L Γ Δ) :
    Nonempty (BehavioralProfile graph) := ⟨failureProfile graph⟩

def afterSample {Γ Δ : VCtx Player L} {name : VarId} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {law : PublicDist (L := L) Γ payload}
    {next : Graph Player L ((name, .pub payload) :: Γ) Δ}
    (profile : BehavioralProfile (Graph.sample name fresh law next)) :
    BehavioralProfile next := fun who => profile who

def afterBind {Γ Δ : VCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ}
    (profile : BehavioralProfile (Graph.bind name owner fresh next)) :
    BehavioralProfile next := fun who => (profile who).2

def afterResolve {Γ Δ : VCtx Player L} {outputName bindingName : VarId}
    {owner : Player} {payload : L.Ty} {fresh : outputName ∉ Γ.map Prod.fst}
    {source : HasVar Γ bindingName (.sealed owner (R.result payload))}
    {checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ))}
    {next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ}
    (profile : BehavioralProfile
      (Graph.resolve outputName owner bindingName fresh source checks next)) :
    BehavioralProfile next := fun who => (profile who).2

def bindKernel {Γ Δ : VCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ}
    (profile : BehavioralProfile (Graph.bind name owner fresh next)) :
    DecisionView owner Γ → FinDist (PublicationResult (L.Val payload)) :=
  (profile owner).1 rfl

def resolveKernel {Γ Δ : VCtx Player L} {outputName bindingName : VarId}
    {owner : Player} {payload : L.Ty} {fresh : outputName ∉ Γ.map Prod.fst}
    {source : HasVar Γ bindingName (.sealed owner (R.result payload))}
    {checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ))}
    {next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ}
    (profile : BehavioralProfile
      (Graph.resolve outputName owner bindingName fresh source checks next)) :
    DecisionView owner Γ → FinDist Bool :=
  (profile owner).1 rfl

def terminalPayoffs : {Γ Δ : VCtx Player L} → (graph : Graph Player L Γ Δ) →
    List (Player × PublicExpr (L := L) Δ L.int)
  | _, _, .ret payoffs => payoffs
  | _, _, .sample _ _ _ next => terminalPayoffs next
  | _, _, .bind _ _ _ next => terminalPayoffs next
  | _, _, .resolve _ _ _ _ _ _ next => terminalPayoffs next

def checksAccepted {Γ : VCtx Player L} (checks : List (GuardCheck (R := R) Γ))
    (env : VEnv L Γ) : Bool :=
  checks.all fun check => check.eval env != .rejected

def proposedResult {Γ : VCtx Player L} {owner : Player} {payload : L.Ty}
    {bindingName : VarId}
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (env : VEnv L Γ) (disclose : Bool) : PublicationResult (L.Val payload) :=
  if disclose then R.valueEquiv _ (env.get source) else .failure

def acceptedResult {Γ : VCtx Player L} {owner : Player} {payload : L.Ty}
    {outputName bindingName : VarId}
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R) ((outputName, .pub (R.result payload)) :: Γ)))
    (env : VEnv L Γ) (disclose : Bool) : PublicationResult (L.Val payload) :=
  let proposed := proposedResult source env disclose
  let tentative := VEnv.cons ((R.valueEquiv _).symm proposed) env
  if checksAccepted checks tentative then proposed else .failure

def runWith : {Γ Δ : VCtx Player L} → (graph : Graph Player L Γ Δ) →
    BehavioralProfile graph → VEnv L Γ → History Player L →
    FinDist (VEnv L Δ)
  | _, _, .ret _, _, env, _ => FinDist.pure env
  | _, _, .sample _ _ law next, profile, env, history =>
      (law.eval env).bind fun value =>
        runWith next (afterSample profile) (VEnv.cons value env) history
  | _, _, .bind name owner _ next, profile, env, history =>
      (bindKernel profile (observe owner env, history owner)).bind fun choice =>
        let history' := Function.update history owner
          (history owner ++ [OwnAction.bind owner name _ choice])
        runWith next (afterBind profile) (VEnv.cons ((R.valueEquiv _).symm choice) env) history'
  | _, _, .resolve _outputName owner bindingName _ source checks next, profile, env, history =>
      (resolveKernel profile (observe owner env, history owner)).bind fun disclose =>
        let accepted := acceptedResult source checks env disclose
        let history' := Function.update history owner
          (history owner ++ [OwnAction.resolve owner bindingName disclose])
        runWith next (afterResolve profile)
          (VEnv.cons ((R.valueEquiv _).symm accepted) env) history'

def run {Γ Δ : VCtx Player L} (graph : Graph Player L Γ Δ)
    (profile : BehavioralProfile graph) (env : VEnv L Γ) :=
  runWith graph profile env (fun _ => [])

def gameSignature {Γ Δ : VCtx Player L} (graph : Graph Player L Γ Δ) :
    GameSignature Player where
  Strategy := fun who => BehavioralPolicy who graph
  Outcome := VEnv L Δ

def gameForm {Γ Δ : VCtx Player L} (graph : Graph Player L Γ Δ) (env : VEnv L Γ) :
    GameForm Player where
  sig := gameSignature graph
  play profile := run graph profile env

def evaluatePayoffs {Γ Δ : VCtx Player L} (graph : Graph Player L Γ Δ)
    (env : VEnv L Δ) : List (Player × Int) :=
  (terminalPayoffs graph).map fun payoff =>
    (payoff.1, L.toInt (payoff.2.eval env))

end Vegas.Graph
