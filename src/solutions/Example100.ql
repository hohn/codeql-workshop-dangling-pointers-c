import cpp

// Find dereferences of uninitialized pointers by querying the points-to map.
from PointerDereferenceExpr pde, PSetEntry pse
where pointsToMap(pde, pde.getOperand().(VariableAccess).getTarget(), pse)
// only the invalid entries are interesting:
// and pse = PSetInvalid(_)
select pde, pse

newtype TInvalidReason =
  TUninitialized(DeclStmt ds, LocalVariable lv) { ds.getADeclaration() = lv } or
  TVariableOutOfScope(LocalVariable lv, ControlFlowNode cfn) { goesOutOfScope(lv, cfn) }

private newtype TPSetEntry =
  PSetVar(LocalVariable lv) or
  PSetInvalid(InvalidReason ir) or
  PSetUnknown()

predicate pointsToMap(ControlFlowNode location, LocalVariable lv, PSetEntry pse) {
  // 1. At location, pse is defined for lv
  if isPointsToEntryDefined(location, lv)
  then pse = getADefinedPointsToEntry(location, lv)
  else (
    // 2. pse is not defined at location, so get it from a previous location
    not goesOutOfScope(lv, location) and
    exists(ControlFlowNode prevLocation, PSetEntry prevPse |
      prevLocation = location.getAPredecessor() and
      pointsToMap(prevLocation, lv, prevPse)
    |
      (
        // Check if the points-to set for lv at location contains a PSetVar(otherVariable) to determine if otherVariable is still in scope.
        // 1. If it is not in scope, then replace that entry with invalid/out of scope.
        // 2. If it is in scope, then keep the entry as is.
        exists(LocalVariable otherVariable |
          prevPse = PSetVar(otherVariable) and
          goesOutOfScope(otherVariable, location) and
          pse = PSetInvalid(TVariableOutOfScope(otherVariable, location))
        )
        or
        pse = prevPse and
        not exists(LocalVariable otherVariable |
          prevPse = PSetVar(otherVariable) and goesOutOfScope(otherVariable, location)
        )
      )
    )
  )
}

predicate isPointsToEntryDefined(ControlFlowNode location, LocalVariable lv) {
  // 1. A pointer variable is declared
  exists(DeclStmt ds | ds.getADeclaration() = lv | location = ds)
  or
  // 2. A pointer variable is assigned a value
  lv.getAnAssignedValue() = location
}

PSetEntry getADefinedPointsToEntry(ControlFlowNode location, LocalVariable lv) {
  // char *ptr => uninitialized
  exists(DeclStmt ds | location = ds and ds.getADeclaration() = lv |
    result = PSetInvalid(TUninitialized(ds, lv))
  )
  or
  exists(Expr assign |
    assign = lv.getAnAssignedValue() and
    location = assign
  |
    // Case
    // p = &other;
    exists(LocalVariable v | v = assign.(AddressOfExpr).getOperand().(VariableAccess).getTarget() |
      result = PSetVar(v)
    )
    or
    // p = otherPointer
    exists(VariableAccess va |
      va = assign and
      va.getTarget().(LocalScopeVariable).getType() instanceof PointerType and
      // pointsToMap(assign.getAPredecessor(), va.getTarget(), result)
      result = PSetVar(va.getTarget())
    )
    or
    // Other cases => unknown
    not assign instanceof AddressOfExpr and
    not assign instanceof VariableAccess and
    result = PSetUnknown()
  )
}

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
