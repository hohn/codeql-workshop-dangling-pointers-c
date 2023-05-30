import cpp

//  TUninitialized
from DeclStmt ds, LocalVariable lv
where ds.getADeclaration() = lv
select lv, ds, lv.getInitializer()
// 
// // // TVariableOutOfScope
// from LocalVariable lv, ControlFlowNode cfn
// where goesOutOfScope(lv, cfn)
// select lv

/**
 * Get the scope that `lv` exits from.
 */
predicate goesOutOfScope(LocalVariable lv, ControlFlowNode cfn) {
  exists(BlockStmt scope |
    scope = lv.getParentScope() and
    if exists(scope.getFollowingStmt()) then scope.getFollowingStmt() = cfn else cfn = scope
  )
}
