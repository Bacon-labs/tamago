import Compiler.ECM

namespace common.ECM

open Compiler.Yul
open Compiler.ECM

def selfAddressModule (resultVar : String) : ExternalCallModule where
  name := "selfAddress"
  numArgs := 1
  resultVars := [resultVar]
  writesState := false
  readsState := false
  axioms := ["self_address_yul_address_opcode"]
  proofStatus := .assumed
  compile := fun _ctx args => do
    match args with
    | [_] => pure [YulStmt.let_ resultVar (YulExpr.call "address" [])]
    | _ => throw "selfAddress expects 1 dummy argument"

end common.ECM
