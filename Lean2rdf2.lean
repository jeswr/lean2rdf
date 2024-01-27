import Lean
import Lean.Data.Json.FromToJson
-- This is where most of the elaboration logic lives.
import Lean.Elab.BuiltinCommand
import Lean.Meta.Basic
import Lean.Message
open Lean Elab Term Meta

def ml (s : Syntax): Except String String :=
  match s with
  | Syntax.missing => Except.error "missing"
  | Syntax.node info kind args => Except.ok "node"
  | Syntax.atom info val => Except.ok "atom"
  | Syntax.ident info rawVal val preresolved => Except.ok "ident"

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp


theorem test2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by simp [hp, hq]

def cs: TermElabM Syntax := `(test)
def cs2: TermElabM Syntax := `(test2)


def getExpr (x : TermElabM Syntax) : TermElabM Expr := do
  let synt ← x
  elabTerm synt none

def c := (getExpr cs2).run' {}

-- def getExpr (x : TermElabM Syntax) :=
--   | Term

#eval (getExpr cs2).run' {}
