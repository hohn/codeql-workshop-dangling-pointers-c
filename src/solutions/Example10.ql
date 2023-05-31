import cpp

//  TUninitialized
from DeclStmt ds, LocalVariable lv
where ds.getADeclaration() = lv
select lv, ds

newtype TInvalidReason =
  TUninitialized(DeclStmt ds, LocalVariable lv) { ds.getADeclaration() = lv } 