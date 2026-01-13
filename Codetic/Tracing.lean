/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Lean.Meta.Tactic.Simp.SimpTheorems
import Codetic.Util.Basic
public meta import Lean.Parser.Do

public section

open Lean Lean.Meta

namespace Codetic

structure TraceOption where
  traceClass : Name
  option : Lean.Option Bool
  deriving Inhabited

def registerTraceOption (traceName : Name) (descr : String) :
    IO TraceOption := do
  let option ← Option.register (`trace.codetic ++ traceName) {
    defValue := false
    group := "trace"
    descr
  }
  return { traceClass := `codetic ++ traceName, option }

namespace TraceOption

def isEnabled [Monad m] [MonadOptions m] (opt : TraceOption) : m Bool :=
  return opt.option.get (← getOptions)

def withEnabled [MonadWithOptions m] (opt : TraceOption) (k : m α) : m α :=
  withOptions (λ opts => opt.option.set opts true) k

initialize steps : TraceOption ←
  registerTraceOption .anonymous
    "(codetic) Print actions taken by Codetic during the proof search."

initialize ruleSet : TraceOption ←
  registerTraceOption `ruleSet
    "(codetic) Print the rule set before starting the search."

initialize proof : TraceOption ←
  registerTraceOption `proof
    "(codetic) If the search is successful, print the produced proof term."

initialize tree : TraceOption ←
  registerTraceOption `tree
    "(codetic) Once the search has concluded (successfully or unsuccessfully), print the final search tree."

initialize extraction : TraceOption ←
  registerTraceOption `extraction
    "(codetic) Print a trace of the proof extraction procedure."

initialize stats : TraceOption ←
  registerTraceOption `stats
    "(codetic) If the search is successful, print some statistics."

initialize debug : TraceOption ←
  registerTraceOption `debug
    "(codetic) Print various debugging information."

initialize script : TraceOption ←
  registerTraceOption `script
    "(codetic) Print a trace of script generation."

initialize forward : TraceOption ←
  registerTraceOption `forward
    "(codetic) Trace forward reasoning."

initialize forwardDebug : TraceOption ←
  registerTraceOption `forward.debug
    "(codetic) Trace more information about forward reasoning. Mostly intended for performance analysis."

initialize rpinf : TraceOption ←
  registerTraceOption `rpinf
    "(codetic) Trace RPINF calculations."
--自己注册一个trace
initialize zzh_custom : TraceOption ←
  registerTraceOption `zzh_custom
    "(codetic) Custom trace for debugging. Use this for any temporary or experimental tracing."

end TraceOption

section

open Lean.Elab Lean.Elab.Term

private meta def isFullyQualifiedGlobalName (n : Name) : MacroM Bool :=
  return (← Macro.resolveGlobalName n).any (·.fst == n)

meta def resolveTraceOption (stx : Ident) : MacroM Name :=
  withRef stx do
    let n := stx.getId
    let fqn := ``TraceOption ++ n
    if ← isFullyQualifiedGlobalName fqn then
      return fqn
    else
      return n

macro "codetic_trace![" opt:ident "] " msg:(interpolatedStr(term) <|> term) :
    doElem => do
  let opt ← mkIdent <$> resolveTraceOption opt
  let msg := msg.raw
  let msg ← if msg.getKind == interpolatedStrKind then
    `(m! $(⟨msg⟩):interpolatedStr)
  else
    `(toMessageData ($(⟨msg⟩)))
  `(doElem| Lean.addTrace (Codetic.TraceOption.traceClass $opt) $msg)

macro "codetic_trace[" opt:ident "] "
    msg:(interpolatedStr(term) <|> Parser.Term.do <|> term) : doElem => do
  let msg := msg.raw
  let opt ← mkIdent <$> resolveTraceOption opt
  match msg with
  | `(do $action) =>
    `(doElem| do
        if ← Codetic.TraceOption.isEnabled $opt then
          $action)
  | _ =>
    `(doElem| do
        if ← Codetic.TraceOption.isEnabled $opt then
          codetic_trace![$opt] $(⟨msg⟩))

end

def ruleSuccessEmoji    := checkEmoji
def ruleFailureEmoji    := crossEmoji
def ruleProvedEmoji     := "🏁"
def ruleErrorEmoji      := bombEmoji
def rulePostponedEmoji  := "⏳️"
def ruleSkippedEmoji    := "⏩️"
def nodeUnknownEmoji    := "❓️"
def nodeProvedEmoji     := ruleProvedEmoji
def nodeUnprovableEmoji := ruleFailureEmoji
def newNodeEmoji        := "🆕"

def exceptRuleResultToEmoji (toEmoji : α → String) : Except ε α → String
  | .error _ => ruleFailureEmoji
  | .ok r => toEmoji r

section

variable [Monad m] [MonadTrace m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
    [MonadRef m] [AddMessageContext m] [MonadOptions m] [MonadAlwaysExcept ε m]

@[inline, always_inline]
def withCodeticTraceNode (opt : TraceOption)
    (msg : Except ε α → m MessageData) (k : m α) (collapsed := true) : m α :=
  withTraceNode opt.traceClass msg k collapsed

@[inline, always_inline]
def withCodeticTraceNodeBefore [ExceptToEmoji ε α] (opt : TraceOption)
    (msg : m MessageData) (k : m α) (collapsed := true) : m α :=
  withTraceNodeBefore opt.traceClass msg k collapsed

@[inline, always_inline]
def withConstCodeticTraceNode (opt : TraceOption) (msg : m MessageData) (k : m α)
    (collapsed := true) : m α :=
  withCodeticTraceNode opt (λ _ => msg) k collapsed

end

def traceSimpTheoremTreeContents (t : SimpTheoremTree) (opt : TraceOption) :
    CoreM Unit := do
  if ! (← opt.isEnabled) then
    return
  for e in t.values.map (toString ·.origin.key) |>.qsortOrd do
    codetic_trace![opt] e

def traceSimpTheorems (s : SimpTheorems) (opt : TraceOption) : CoreM Unit := do
  if ! (← opt.isEnabled) then
    return
  withConstCodeticTraceNode opt (return "Erased entries") do
    codetic_trace![opt] "(Note: even if these entries appear in the sections below, they will not be used by simp.)"
    for e in PersistentHashSet.toArray s.erased |>.map (toString ·.key) |>.qsortOrd do
      codetic_trace![opt] e
  withConstCodeticTraceNode opt (return "Pre lemmas") do
    traceSimpTheoremTreeContents s.pre opt
  withConstCodeticTraceNode opt (return "Post lemmas") do
    traceSimpTheoremTreeContents s.post opt
  withConstCodeticTraceNode opt (return "Constants to unfold") do
    for e in PersistentHashSet.toArray s.toUnfold |>.map toString |>.qsortOrd do
      codetic_trace![opt] e

end Codetic
