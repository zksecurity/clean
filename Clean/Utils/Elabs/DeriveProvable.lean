import Lean.Meta.Transform
import Lean.Meta.Inductive
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Clean.Circuit.Provable

namespace DerivingProvable

open Std
open Lean
open Lean.Meta
open Lean.Declaration
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Elab.Term
open Lean.Elab.Command
open Lean.Elab.Deriving
open Lean.Elab.Deriving.Context
open Lean.Parser.Term

def mkReprHeader (indVal : InductiveVal) : TermElabM Header := do
  let header ← mkHeader `ProvableType 1 indVal
  return { header with
    binders := header.binders.push (← `(bracketedBinderF| (prec : Nat)))
  }

def mkBodyForStruct (header : Header) (indVal : InductiveVal) : TermElabM Term := do
  let ctorVal ← getConstInfoCtor indVal.ctors.head!
  let fieldNames := getStructureFields (← getEnv) indVal.name
  let numParams  := indVal.numParams
  let target     := mkIdent header.targetNames[0]!
  forallTelescopeReducing ctorVal.type fun xs _ => do
    let mut fields ← `(Format.nil)
    if xs.size != numParams + fieldNames.size then
      throwError "'deriving Repr' failed, unexpected number of fields in structure"
    for h : i in [:fieldNames.size] do
      let fieldName := fieldNames[i]
      dbg_trace "fieldName {fieldName}"
      let fieldNameLit := Syntax.mkStrLit (toString fieldName)
      let x := xs[numParams + i]!
      if i != 0 then
        fields ← `($fields ++ "," ++ Format.line)
      if (← isType x <||> isProof x) then
        fields ← `($fields ++ $fieldNameLit ++ " := " ++ "_")
      else
        let indent := Syntax.mkNumLit <| toString ((toString fieldName |>.length) + " := ".length)
        fields ← `($fields ++ $fieldNameLit ++ " := " ++ (Format.group (Format.nest $indent (repr ($target.$(mkIdent fieldName):ident)))))
    `(Format.bracket "{ " $fields:term " }")

def mkBody (header : Header) (indVal : InductiveVal) : TermElabM Term := do
  if isStructure (← getEnv) indVal.name then
    mkBodyForStruct header indVal
  else
    throwError "deriving ProvableType for inductive types is not supported yet"

def mkAuxFunction (ctx : Elab.Deriving.Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal     := ctx.typeInfos[i]!
  let header     ← mkReprHeader indVal
  let mut body   ← mkBody header indVal
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx `ProvableType header.argNames
    body ← mkLet letDecls body
  let binders    := header.binders
  if ctx.usePartial then
    `(private partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Format := $body:term)
  else
    `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Format := $body:term)

def mkMutualBlock (ctx : Elab.Deriving.Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual
     $auxDefs:command*
    end)

private def mkProvableType (declName : Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "repr" declName
  dbg_trace "mkProvableType {declName}"
  let cmds := #[← mkMutualBlock ctx] ++ (← mkInstanceCmds ctx `ProvableType #[declName])
  dbg_trace "cmds: {cmds}"
  return cmds


def mkProvableInstance (declName : Name) (fieldtype : Expr) : CommandElabM Bool := do
  if ←isInductive declName then
    dbg_trace "mkProvableInstance {declName} {fieldtype}"
    let cmds ← liftTermElabM <| mkProvableType declName
    cmds.forM elabCommand
    return true
  else
    return false

/--
Derive a provable type instance for a type.
The provable instance can be instantiated automatically over types which are parametrized
by only one type T. The supported types are:
- Structures with fields which are either T or a type (recursively) inantiatiable
  to a provable structure over T
-/
elab "derive_provable " type_name:term " as " instance_name:term " with " var_types:term "," val_types:term  : command => do
  dbg_trace "deriving provable for {type_name} {instance_name}"
  dbg_trace "types: {var_types} {val_types}"

  let name : Name ← liftCoreM do
    realizeGlobalConstNoOverloadWithInfo type_name
  let field_type : Expr ← liftTermElabM do
    let field_type ← elabType var_types
    return field_type
  dbg_trace "field_type: {field_type}"
  let _ ← mkProvableInstance name field_type
  return

end DerivingProvable

section --example

#check ProvableType

open DerivingProvable
variable (F : Type)

structure Example2 (T : Type) where
  x : T
  y : T

structure ExampleStruct (T : Type) where
  r : Example2 T
  z : T

-- derive_provable ExampleStruct as Example with Bool, F


end
