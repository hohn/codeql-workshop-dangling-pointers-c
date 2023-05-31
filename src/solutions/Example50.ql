/**
 * @name Local variable goes out of scope
 * @description A local variable goes out of scope.
 * @kind problem
 */

import cpp

from PSetEntry pse, InvalidReason reason, LocalVariable lv, ControlFlowNode cfn
where
  pse = PSetInvalid(reason) and
  reason = TVariableOutOfScope(lv, cfn)
select cfn, "Variable $@ goes out of scope here.", lv, lv.getName()

newtype TInvalidReason =
  TUninitialized(DeclStmt ds, LocalVariable lv) { ds.getADeclaration() = lv } or
  TVariableOutOfScope(LocalVariable lv, ControlFlowNode cfn) { goesOutOfScope(lv, cfn) }

private newtype TPSetEntry =
  PSetVar(LocalVariable lv) or
  PSetInvalid(InvalidReason ir) or
  PSetUnknown()

class PSetEntry extends TPSetEntry {
  string toString() {
    exists(LocalVariable lv |
      this = PSetVar(lv) and
      result = "Var(" + lv.toString() + ")"
    )
    or
    this = PSetUnknown() and result = "Unknown"
    or
    exists(InvalidReason ir |
      this = PSetInvalid(ir) and
      result = "Invalid because " + ir.toString()
    )
  }
}

/**
 * Get the scope that `lv` exits from.
 */
predicate goesOutOfScope(LocalVariable lv, ControlFlowNode cfn) {
  exists(BlockStmt scope |
    scope = lv.getParentScope() and
    if exists(scope.getFollowingStmt()) then scope.getFollowingStmt() = cfn else cfn = scope
  )
}

class InvalidReason extends TInvalidReason {
  string toString() {
    exists(DeclStmt ds, LocalVariable lv |
      this = TUninitialized(ds, lv) and
      result = "variable " + lv.getName() + " is unitialized."
    )
    or
    exists(LocalVariable lv, ControlFlowNode cfn |
      this = TVariableOutOfScope(lv, cfn) and
      result = "variable " + lv.getName() + " went out of scope."
    )
  }
  Location getLocation() {
    exists(DeclStmt ds |
      this = TUninitialized(ds, _) and
      result = ds.getLocation()
    )
    or
    exists(ControlFlowNode cfn |
      this = TVariableOutOfScope(_, cfn) and
      result = cfn.getLocation()
    )
  }
}
