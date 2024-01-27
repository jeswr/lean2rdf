import Lean
import Lean.Data.Json.FromToJson
-- This is where most of the elaboration logic lives.
import Lean.Elab.BuiltinCommand
import Lean.Meta.Basic
import Lean.Message
open Lean Elab Term Meta

def getExpr (x : TermElabM Syntax) : TermElabM Expr := do
  let synt ← x
  elabTerm synt none


def getTypeStr (n : Name) := do
  let inf ← getConstInfo n
  let t := inf.toConstantVal.type
  let dat ← ppExpr t
  return s!"{dat}"

def getTypeExpr (n : Name) : TermElabM Expr := do
  let inf ← getConstInfo n
  let t := inf.toConstantVal.type
  return t

def getConstType (n : Name) : TermElabM String := do
  let constInfo ← getConstInfo n
  return match constInfo with
    | ConstantInfo.defnInfo _ => "Definition"
    | ConstantInfo.thmInfo _  => "Theorem"
    | ConstantInfo.axiomInfo _ => "Axiom"
    | _ => "Other"

def getConstantBody (n : Name) : TermElabM (Option Expr) := do
  let constInfo ← getConstInfo n
  let constValue := constInfo.value?
  return constValue


def getAllConstsFromConst (n : Name) : TermElabM (Array Name) := do
  let body ← getConstantBody n
  let type ← getTypeExpr n
  let consts1 := match body with
    | some body => body.getUsedConstants
    | none => [].toArray
  let consts2 := type.getUsedConstants
  let res := consts1 ++ consts2
  let set := HashSet.insertMany mkHashSet res
  return set.toArray

def getAllConstsFromNamespace (n : String) : TermElabM (List Name) := do
  let env ← getEnv
  let consts := env.constants.fold (fun res name _ => if name.getRoot.toString == n then name :: res else res) []
  return consts.toArray.toList


structure BFSState :=
  (g : HashMap Name (List Name))
  (outerLayer : List Name)

def getUsedConstantGraph (names : List Name) (depth : Nat) : TermElabM (List (Name × List Name)) := do

  -- make bfs from the specified root node

  -- the goal is to construct a hashmap where the key is the name of the const, and the entry is a list of names of other consts

  -- we keep a list of const names representing the outer layer of the bfs

  -- in each iteration we for each const in the outer layer find its references and that way construct the nodes that will be added to the graph

  -- then we extract the outer layer from the new nodes by looking at the children and checking whether they are already in the graph

  let state ← (List.range depth).foldlM (fun (state : BFSState) (_ : Nat) => do
    let g := state.g
    let outerLayer := state.outerLayer


    let newNodes ← outerLayer.mapM fun name => do
      let consts ← try getAllConstsFromConst name catch | _ => pure #[]
      pure (name, consts)


    let g := newNodes.foldl (fun m p => m.insert p.fst p.snd.toList) g
    let newOuterLayer := newNodes.foldl (fun (set : HashSet Name) (node : Name × Array Name) =>
      let set := set.insertMany node.snd;
      set) mkHashSet
    let newOuterLayer := newOuterLayer.toList.filter (fun n => !(g.contains n))

    return BFSState.mk g newOuterLayer
  )
    (BFSState.mk mkHashMap names)




  return state.g.toList


#synth ToJson (List (Name × List Name))

def writeJsonToFile (filePath : String) (json : Json) : IO Unit := do
  let jsonString := toString json
  IO.FS.withFile filePath IO.FS.Mode.write fun handle => do
    handle.putStr jsonString

-- Convert a Name to a String
def nameToString (n : Name) : String :=
  toString n


-- Convert a Name and List Name pair to JSON
def pairToJson (pair : Name × List Name) : TermElabM (Option Json) := do
  let nameStr := nameToString pair.fst
  let constCategoryStr ← try (getConstType pair.fst) catch | _ => return none
  let nameListStr := pair.snd.map nameToString
  let constTypeStr ← getTypeStr pair.fst
  return Json.mkObj [("name", Json.str nameStr),("constCategory", Json.str constCategoryStr), ("constType", constTypeStr), ("references", Json.arr (nameListStr.map Json.str).toArray)]

-- Serialize a List (Name, List Name) to JSON
def serializeList (l : List (Name × List Name)) : TermElabM Json := do
  let res ← (l.filterMapM pairToJson)
  return Json.arr res.toArray

inductive Source
| Namespace (n : String)
| Constant (s : TermElabM Syntax)

def getConstsFromSource (s : Source) : TermElabM (List Name) := do
  match s with
  | Source.Namespace n => do
    (getAllConstsFromNamespace n)
  | Source.Constant snt => do
    let expr ← getExpr snt
    let name := expr.constName!
    return [name]


def serializeAndWriteToFile (source : Source) (depth : Nat) : TermElabM String := do
  let consts ← getConstsFromSource source
  let g ← getUsedConstantGraph consts depth
  let js ←  serializeList g
  pure (toString js)

-- Edit and uncomment one of the lines below to get your .json file created in the current workspace folder

def reverse (arr: List Nat) : List Nat :=
  match arr with
  | [] => []
  | x :: xs => reverse xs ++ [x]

-- theorem revrev (arr: List Nat) : reverse (reverse arr) = arr :=
--   match arr with
--   | [] => rfl
--   | x :: xs => by simp [reverse, revrev xs]

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

def cs: TermElabM Syntax := `(test)

def matcher (s : Syntax): Except String String :=
  match s with
  | Syntax.missing => Except.error "missing"
  | Syntax.node info kind args => Except.ok "node"
  | Syntax.atom info val => Except.ok "atom"
  | Syntax.ident info rawVal val preresolved => Except.ok "ident"

def Elabmatcher (s : Syntax): Except String String :=
  match s with
  | Syntax.missing => Except.error "missing"
  | Syntax.node info kind args => Except.ok "node"
  | Syntax.atom info val => Except.ok "atom"
  | Syntax.ident info rawVal val preresolved => Except.ok "ident"


-- cs.
#eval cs

#eval serializeAndWriteToFile (Source.Constant `(test)) 1
#eval serializeAndWriteToFile (Source.Constant `(@Nat.add_zero)) 7
#eval serializeAndWriteToFile (Source.Namespace "Nat") 2
