
# Table of Contents

1.  [Dangling pointers](#dangling-pointers)
    1.  [Algebraic data types](#orge8b9ea8)
    2.  [Summary](#org823d791)
    3.  [Exercise 1.0](#org710d1fd)
        1.  [Hints](#orgaaddc49)
        2.  [Solution](#org5dbc7bc)
        3.  [First 5 results](#orgd580a1c)
    4.  [Exercise 2.0](#orgc63ee9c)
        1.  [Hints](#org2062ab0)
        2.  [Solution](#org5fda262)
        3.  [First 5 results](#org7a532ab)
    5.  [Exercise 3.0](#orge53e8d8)
        1.  [Solution](#orgc9e47f0)
        2.  [First 5 results](#org1fb35e2)
    6.  [Exercise 4.0](#org54a0b62)
        1.  [ADT](#orgdd223d0)
        2.  [Derived Class](#org31161ff)
        3.  [Query](#org8445615)
        4.  [Solution](#org6c26a55)
        5.  [First 5 results](#org13afbb8)
    7.  [Exercise 5.0](#org0301f83)
        1.  [Solution](#org97aaed6)
        2.  [First 5 results](#orga5c512d)
    8.  [Exercise 6.0 &#x2013; start pointsToMap](#org67d4793)
        1.  [Solution](#org5d443a5)
        2.  [First 5 results](#org5f1db0f)
    9.  [Exercise 7.0 &#x2013; cases for getADefinedPointsToEntry](#orgdfd0f6f)
        1.  [Solution](#orgd45c10b)
        2.  [First 5 results](#orgf666653)
    10. [Exercise 8.0 &#x2013; continue pointsToMap](#orgc028dac)
        1.  [Solution](#orgd156880)
        2.  [First 5 results](#orgd5104c5)
    11. [Exercise 9.0](#org0bc3b81)
    12. [Exercise 10.0](#orgd41c8a6)
        1.  [Solution](#orgc8c7a2c)
        2.  [First 5 results](#org2758685)
    13. [Exercise 2](#exercise-2)
        1.  [Hints](#hints)
        2.  [Solution](#solution-1)
    14. [Exercise 3](#exercise-3)
        1.  [Solution](#solution-2)
    15. [Exercise 4](#exercise-4)
        1.  [Solution](#solution-3)
    16. [Full solution](#full-solution)


<a id="dangling-pointers"></a>

# Dangling pointers

A dangling pointer is a memory safety violation where the pointer does
not point to a valid object. These dangling pointers are the result of
not modifying the value of the pointer after the pointed to object is
destructed or not properly initializing the pointer.

The use of a dangling pointer can result in a security issue.
Specifically in C++ if the pointer is used to invoke a *virtual* method
and an attacker was able to overwrite the parts of the memory that would
have contained the `vtable` of the object.

The following snippet shows how a dangling pointer can occur.

    void dangling_pointer() {
        char **p = nullptr;
        {
            char * s = "hello world";
            p = &s;
        }
        printf("%s", *p);
    }

A less obvious case is

    void dangling_pointer() {
        std::string_view s = "hello world"s;
        std::cout << s << std::endl;
    }

After the full expression is evaluated, the temporary object is
destroyed.

Many more interesting examples discussed here
<https://herbsutter.com/2018/09/20/lifetime-profile-v1-0-posted/>

To find these issues we can implement an analysis that tracks lifetimes.
A nice specification for a local lifetime analysis is given by
<https://github.com/isocpp/CppCoreGuidelines/blob/master/docs/Lifetime.pdf>

The gist of the analysis is to track for each local variable the things
it can point to at a particular location in the program. These are other
local variables and special values for global variables, null values,
and invalid values. Whenever a variable goes out of scope, each
reference to that variable in a points-to set is invalidated.

In the next few exercises, we are going to implement a simplified
version of the lifetime profile to find the dangling pointer in the
following example:

    extern void printf(char *, ...);
    
    void simple_dangling_pointer() {
        char **p;
        {
            char *s = "hello world!";
            p = &s;
        }
        printf("%s", *p);
        char *s = "hello world!";
        p = &s;
        printf("%s", *p);
        return;
    }

At the end, we want to find dereferences of uninitialized pointers by querying
the points-to map.  This query will be trivial; all the effort is in predicates
and classes.  We will get a relation

    predicate pointsToMap(ControlFlowNode location, LocalVariable lv, PSetEntry pse) 

that for a `location` and a local variable `lv` will give us information via a
point-set entry value `pse`.


<a id="orge8b9ea8"></a>

## Algebraic data types

ADTs give us dynamic typing, just like unions in C:

    typedef enum {
        TUninitialized = 0,
        TVariableOutOfScope
    } TInvCase;
    
    typedef struct {
        TInvCase the_case;
        union {
            DeclStmt ds;
            LocalVariable lv;
        };
    } TInvalidReason;

An algebraic datatype consists of a number of mutually disjoint branches;
the algebraic datatype itself is the union of all the branch types.

Simple ADT:

    newtype TNum =
        TFloat(float) or
        TInt(int)


<a id="org823d791"></a>

## Summary

The simplified version of the lifetime profile will track 3 possible *points-to*
values, with one of two values in one case:

1.  Variable; A pointer points to another pointer. We will only consider
    local variables represented by the class `LocalVariable`.
2.  Invalid; A pointer
    1.  is not initialized or
    2.  points to a variable that went out of scope.
3.  Unknown; A pointer is assigned something other than the address of
    another `LocalVariable` (e.g., the address of a string.).

In the following, we implement 2 ADTs in bottom-up order.  First, the invalid
cases (#2), then the 3-case *points-to* ADT.


<a id="org710d1fd"></a>

## Exercise 1.0

Define the uninitialized case

    TUninitialized(DeclStmt ds, LocalVariable lv)

as part of

    newtype TInvalidReason 

This uses the relation `TUninitialized` to *connect* `lv` and `ds`.  The `DeclStmt`
may still contain an initializer, but that's not relevant here; the initializer
always runs *after* the stack allocation.


<a id="orgaaddc49"></a>

### Hints

Find the `DeclStmt` s for all `LocalVariable` s.


<a id="org5dbc7bc"></a>

### Solution

    import cpp
    
    //  TUninitialized
    from DeclStmt ds, LocalVariable lv
    where ds.getADeclaration() = lv
    select lv, ds
    
    newtype TInvalidReason =
      TUninitialized(DeclStmt ds, LocalVariable lv) { ds.getADeclaration() = lv } 


<a id="orgd580a1c"></a>

### First 5 results

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />
</colgroup>
<tbody>
<tr>
<td class="org-left">test.c:4:10:4:10</td>
<td class="org-left">p</td>
<td class="org-left">test.c:4:3:4:11</td>
<td class="org-left">declaration</td>
</tr>


<tr>
<td class="org-left">test.c:6:11:6:11</td>
<td class="org-left">s</td>
<td class="org-left">test.c:6:5:6:29</td>
<td class="org-left">declaration</td>
</tr>


<tr>
<td class="org-left">test.c:10:9:10:9</td>
<td class="org-left">s</td>
<td class="org-left">test.c:10:3:10:27</td>
<td class="org-left">declaration</td>
</tr>
</tbody>
</table>


<a id="orgc63ee9c"></a>

## Exercise 2.0

Define the out-of-scope case

    TVariableOutOfScope(LocalVariable lv, ControlFlowNode cfn) { }

as part of

    newtype TInvalidReason 


<a id="org2062ab0"></a>

### Hints


<a id="org5fda262"></a>

### Solution

    import cpp
    
    // TVariableOutOfScope
    from LocalVariable lv, ControlFlowNode cfn
    where goesOutOfScope(lv, cfn)
    select lv
    
    newtype TInvalidReason =
      TUninitialized(DeclStmt ds, LocalVariable lv) { ds.getADeclaration() = lv } or
      TVariableOutOfScope(LocalVariable lv, ControlFlowNode cfn) { goesOutOfScope(lv, cfn) }
    
    /**
     * Get the scope that `lv` exits from.
     */
    predicate goesOutOfScope(LocalVariable lv, ControlFlowNode cfn) {
      exists(BlockStmt scope |
        scope = lv.getParentScope() and
        if exists(scope.getFollowingStmt()) then scope.getFollowingStmt() = cfn else cfn = scope
      )
    }


<a id="org7a532ab"></a>

### First 5 results

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="org-left" />

<col  class="org-left" />
</colgroup>
<tbody>
<tr>
<td class="org-left">test.c:4:10:4:10</td>
<td class="org-left">p</td>
</tr>


<tr>
<td class="org-left">test.c:6:11:6:11</td>
<td class="org-left">s</td>
</tr>


<tr>
<td class="org-left">test.c:10:9:10:9</td>
<td class="org-left">s</td>
</tr>
</tbody>
</table>


<a id="orge53e8d8"></a>

## Exercise 3.0

Define a class `InvalidReason` to handle the printing of the `TInvalidReason`
ADT.


<a id="orgc9e47f0"></a>

### Solution

    import cpp
    
    // TVariableOutOfScope
    from LocalVariable lv, ControlFlowNode cfn
    where goesOutOfScope(lv, cfn)
    select lv
    
    newtype TInvalidReason =
      TUninitialized(DeclStmt ds, LocalVariable lv) { ds.getADeclaration() = lv } or
      TVariableOutOfScope(LocalVariable lv, ControlFlowNode cfn) { goesOutOfScope(lv, cfn) }
    
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
    }


<a id="org1fb35e2"></a>

### First 5 results

WARNING: Unused class InvalidReason (/Users/hohn/local/codeql-workshop-dangling-pointers-c/src/solutions/Example30.ql:22,7-20)

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="org-left" />

<col  class="org-left" />
</colgroup>
<tbody>
<tr>
<td class="org-left">test.c:4:10:4:10</td>
<td class="org-left">p</td>
</tr>


<tr>
<td class="org-left">test.c:6:11:6:11</td>
<td class="org-left">s</td>
</tr>


<tr>
<td class="org-left">test.c:10:9:10:9</td>
<td class="org-left">s</td>
</tr>
</tbody>
</table>


<a id="org54a0b62"></a>

## Exercise 4.0


<a id="orgdd223d0"></a>

### ADT

Define an ADT

    newtype TPSetEntry =...

to handle the outer cases, using the names indicated
in the following:

1.  Variable; A pointer points to another pointer. We will only consider
    local variables represented by the class `LocalVariable`.
    Use 
    
        PSetVar(LocalVariable lv) or
2.  Invalid; A pointer
    
    1.  is not initialized or
    2.  points to a variable that went out of scope.
    
    Use
    
        PSetInvalid
    
    and our previously defined
    
        InvalidReason ir
3.  Unknown; A pointer is assigned something other than the address of
    another `LocalVariable` (e.g., the address of a string.).
    Use
    
        PSetUnknown()


<a id="org31161ff"></a>

### Derived Class

Define the class

    class PSetEntry extends TPSetEntry

that implements the `toString()` predicate.


<a id="org8445615"></a>

### Query

Write a simple query to show where variables go out of scope, 

    select cfn, "Variable $@ goes out of scope here.", lv, lv.getName()

Ignore the `TUninitialized` case for now.


<a id="org6c26a55"></a>

### Solution

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
    }


<a id="org13afbb8"></a>

### First 5 results

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />
</colgroup>
<tbody>
<tr>
<td class="org-left">test.c:3:32:14:1</td>
<td class="org-left">{ &#x2026; }</td>
<td class="org-left">Variable $@ goes out of scope here.</td>
<td class="org-left">test.c:4:10:4:10</td>
<td class="org-left">p</td>
<td class="org-left">p</td>
</tr>


<tr>
<td class="org-left">test.c:3:32:14:1</td>
<td class="org-left">{ &#x2026; }</td>
<td class="org-left">Variable $@ goes out of scope here.</td>
<td class="org-left">test.c:10:9:10:9</td>
<td class="org-left">s</td>
<td class="org-left">s</td>
</tr>


<tr>
<td class="org-left">test.c:9:3:9:19</td>
<td class="org-left">ExprStmt</td>
<td class="org-left">Variable $@ goes out of scope here.</td>
<td class="org-left">test.c:6:11:6:11</td>
<td class="org-left">s</td>
<td class="org-left">s</td>
</tr>
</tbody>
</table>


<a id="org0301f83"></a>

## Exercise 5.0

Add the `getLocation()` predicates to

    class InvalidReason

so the results show a location.


<a id="org97aaed6"></a>

### Solution

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


<a id="orga5c512d"></a>

### First 5 results

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />
</colgroup>
<tbody>
<tr>
<td class="org-left">test.c:3:32:14:1</td>
<td class="org-left">{ &#x2026; }</td>
<td class="org-left">Variable $@ goes out of scope here.</td>
<td class="org-left">test.c:4:10:4:10</td>
<td class="org-left">p</td>
<td class="org-left">p</td>
</tr>


<tr>
<td class="org-left">test.c:3:32:14:1</td>
<td class="org-left">{ &#x2026; }</td>
<td class="org-left">Variable $@ goes out of scope here.</td>
<td class="org-left">test.c:10:9:10:9</td>
<td class="org-left">s</td>
<td class="org-left">s</td>
</tr>


<tr>
<td class="org-left">test.c:9:3:9:19</td>
<td class="org-left">ExprStmt</td>
<td class="org-left">Variable $@ goes out of scope here.</td>
<td class="org-left">test.c:6:11:6:11</td>
<td class="org-left">s</td>
<td class="org-left">s</td>
</tr>
</tbody>
</table>


<a id="org67d4793"></a>

## Exercise 6.0 &#x2013; start pointsToMap

XX:

In this predicate we consider the three cases

1.  At a location, the point-set entry is defined for a local variable.
2.  At a location, the point-set entry is not defined for a local variable, so
    get it from a previous location.
3.  The local variable `lv` is not assigned, but points to a variable
    that went out of scope at location `cfn` so we need to invalidate the
    entry for that variable.

Start on the predicate

    pointsToMap

to handle the first two cases, using helper predicates

    isPointsToEntryDefined

and

    getADefinedPointsToEntry(location, lv)

The third case will be added later.


<a id="org5d443a5"></a>

### Solution

    import cpp
    
    from LocalVariable lv, ControlFlowNode location
    where isPointsToEntryDefined(location, lv)
    select location, lv
    
    predicate pointsToMap(ControlFlowNode location, LocalVariable lv, PSetEntry pse) {
      // 1. At location, pse is defined for lv
      if isPointsToEntryDefined(location, lv)
      then pse = getADefinedPointsToEntry(location, lv)
      else
        // 2. pse is not defined at location, so get it from a previous location
        any()
    }
    
    predicate isPointsToEntryDefined(ControlFlowNode location, LocalVariable lv) {
      // 1. A pointer variable is declared
      exists(DeclStmt ds | ds.getADeclaration() = lv | location = ds)
      or
      // 2. A pointer variable is assigned a value
      lv.getAnAssignedValue() = location
    }
    
    PSetEntry getADefinedPointsToEntry(ControlFlowNode location, LocalVariable lv) { none() }
    
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


<a id="org5f1db0f"></a>

### First 5 results

WARNING: Unused predicate pointsToMap (/Users/hohn/local/codeql-workshop-dangling-pointers-c/src/solutions/Example60.ql:7,11-22)

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />
</colgroup>
<tbody>
<tr>
<td class="org-left">test.c:4:3:4:11</td>
<td class="org-left">declaration</td>
<td class="org-left">test.c:4:10:4:10</td>
<td class="org-left">p</td>
</tr>


<tr>
<td class="org-left">test.c:6:5:6:29</td>
<td class="org-left">declaration</td>
<td class="org-left">test.c:6:11:6:11</td>
<td class="org-left">s</td>
</tr>


<tr>
<td class="org-left">test.c:6:15:6:28</td>
<td class="org-left">hello world!</td>
<td class="org-left">test.c:6:11:6:11</td>
<td class="org-left">s</td>
</tr>


<tr>
<td class="org-left">test.c:7:9:7:10</td>
<td class="org-left">&amp; &#x2026;</td>
<td class="org-left">test.c:4:10:4:10</td>
<td class="org-left">p</td>
</tr>
</tbody>
</table>


<a id="orgdfd0f6f"></a>

## Exercise 7.0 &#x2013; cases for getADefinedPointsToEntry

XX:

    // p = &other;
    
    // p = otherPointer
    
    // Other cases => unknown


<a id="orgd45c10b"></a>

### Solution

    import cpp
    
    from LocalVariable lv, ControlFlowNode location
    where isPointsToEntryDefined(location, lv)
    select location, lv
    
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
      else
        // 2. pse is not defined at location, so get it from a previous location
        any()
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


<a id="orgf666653"></a>

### First 5 results

WARNING: Unused predicate pointsToMap (/Users/hohn/local/codeql-workshop-dangling-pointers-c/src/solutions/Example70.ql:16,11-22)

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />
</colgroup>
<tbody>
<tr>
<td class="org-left">test.c:4:3:4:11</td>
<td class="org-left">declaration</td>
<td class="org-left">test.c:4:10:4:10</td>
<td class="org-left">p</td>
</tr>


<tr>
<td class="org-left">test.c:6:5:6:29</td>
<td class="org-left">declaration</td>
<td class="org-left">test.c:6:11:6:11</td>
<td class="org-left">s</td>
</tr>


<tr>
<td class="org-left">test.c:6:15:6:28</td>
<td class="org-left">hello world!</td>
<td class="org-left">test.c:6:11:6:11</td>
<td class="org-left">s</td>
</tr>


<tr>
<td class="org-left">test.c:7:9:7:10</td>
<td class="org-left">&amp; &#x2026;</td>
<td class="org-left">test.c:4:10:4:10</td>
<td class="org-left">p</td>
</tr>
</tbody>
</table>


<a id="orgc028dac"></a>

## Exercise 8.0 &#x2013; continue pointsToMap

XX:

Check if the points-to set for lv at location contains a PSetVar(otherVariable)
to determine if otherVariable is still in scope.

1.  If it is not in scope, then replace that entry with invalid/out of scope. 
    This is the third case mentioned previously.
2.  If it is in scope, then keep the entry as is.


<a id="orgd156880"></a>

### Solution

    import cpp
    
    from LocalVariable lv, ControlFlowNode location
    where isPointsToEntryDefined(location, lv)
    select location, lv
    
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


<a id="orgd5104c5"></a>

### First 5 results

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />
</colgroup>
<tbody>
<tr>
<td class="org-left">test.c:4:3:4:11</td>
<td class="org-left">declaration</td>
<td class="org-left">test.c:4:10:4:10</td>
<td class="org-left">p</td>
</tr>


<tr>
<td class="org-left">test.c:6:5:6:29</td>
<td class="org-left">declaration</td>
<td class="org-left">test.c:6:11:6:11</td>
<td class="org-left">s</td>
</tr>


<tr>
<td class="org-left">test.c:6:15:6:28</td>
<td class="org-left">hello world!</td>
<td class="org-left">test.c:6:11:6:11</td>
<td class="org-left">s</td>
</tr>


<tr>
<td class="org-left">test.c:7:9:7:10</td>
<td class="org-left">&amp; &#x2026;</td>
<td class="org-left">test.c:4:10:4:10</td>
<td class="org-left">p</td>
</tr>


<tr>
<td class="org-left">test.c:10:3:10:27</td>
<td class="org-left">declaration</td>
<td class="org-left">test.c:10:9:10:9</td>
<td class="org-left">s</td>
</tr>
</tbody>
</table>


<a id="org0bc3b81"></a>

## Exercise 9.0

XX:

Examine pointsToMap results and summarize


<a id="orgd41c8a6"></a>

## Exercise 10.0

XX:

Find dereferences of uninitialized pointers by querying the points-to map.
This query will be trivial; all the effort is in predicates and classes.


<a id="orgc8c7a2c"></a>

### Solution

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


<a id="org2758685"></a>

### First 5 results

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />
</colgroup>
<tbody>
<tr>
<td class="org-left">test.c:9:16:9:17</td>
<td class="org-left">* &#x2026;</td>
<td class="org-left">Invalid because variable s went out of scope.</td>
</tr>


<tr>
<td class="org-left">test.c:12:16:12:17</td>
<td class="org-left">* &#x2026;</td>
<td class="org-left">Var(s)</td>
</tr>
</tbody>
</table>


<a id="exercise-2"></a>

## Exercise 2

With the *points-to* set entries modeled we can start to implement parts
of our *points-to* set that will associate *points-to* set entries to
local variables at a program location. That map will be implemented by
the predicate `pointsToMap`.

The following snippet shows the skeleton of that predicate.

    predicate pointsToMap(ControlFlowNode cfn, LocalVariable lv, PSEntry pse) {
    }

In this predicate we must consider three cases:

1.  The local variable `lv` is assigned a value at location `cfn` that
    defines the *points-to* set entry `pse`.
2.  The local local variable `lv` is not assigned so we have to propagate
    the *points-to* set entry from a previous location.
3.  The local variable `lv` is not assigned, but points to a variable
    that went out of scope at location `cfn` so we need to invalid the
    entry for that variable.

In this exercise we are going to implement the first case by
implementing the two predicates `isPSetReassigned` and
`getAnAssignedPSetEntry`.

-   The predicate `isPSetReassigned` should hold if a new *points-to*
    entry should be assigned at that location. This happens when:
    -   A local variable is declared and is uninitialized.
    -   A local variable is assigned a value.
-   The predicate `getAnAssignedPSEntry` should relate a program location
    and variable to a *points-to* entry.

The following snippet provides the skeleton that needs to be completed.

    predicate pointsToMap(ControlFlowNode cfn, LocalVariable lv, PSEntry pse) {
        if isPSetReassigned(cfn, lv)
        then pse = getAnAssignedPSetEntry(cfn, lv)
        else
            ...
    }
    
    predicate isPSetReassigned(ControlFlowNode cfn, LocalVariable lv) {
    
    }
    
    PSEntry getAnAssignedPSetEntry(ControlFlowNode cfn, LocalVariable lv) {
    
    }


<a id="hints"></a>

### Hints

1.  The class `DeclStmt` models a declaration statement and the predicate
    `getADeclaration` relates what is declared (e.g., a `Variable`)
2.  For a `Variable` we can get the `Expr` that represent the value that
    is assigned to the variable with the predicate `getAnAssignedValue`.
3.  The `AddressOfExpr` models address taken of operation that when
    assigned to a variable can be used to determine if one variable
    points-to another variable.


<a id="solution-1"></a>

### Solution

The local variable `lv` gets assigned a *points-to* entry when it is
declared or assigned a value.

    predicate isPSetReassigned(ControlFlowNode cfn, LocalVariable lv) {
      exists(DeclStmt ds |
        cfn = ds and
        ds.getADeclaration() = lv and
        lv.getType() instanceof PointerType
      )
      or
      cfn = lv.getAnAssignedValue()
    }
    
    PSEntry getAnAssignedPSetEntry(ControlFlowNode cfn, LocalVariable lv) {
      exists(DeclStmt ds |
        cfn = ds and
        ds.getADeclaration() = lv
      |
        lv.getType() instanceof PointerType and
        result = PSetInvalid(TUninitialized(ds, lv))
      )
      or
      exists(Expr assign |
        assign = lv.getAnAssignedValue() and
        cfn = assign
      |
        exists(LocalVariable v | v = assign.(AddressOfExpr).getOperand().(VariableAccess).getTarget() |
          result = PSetVar(v)
        )
        or
        exists(VariableAccess va |
          va = assign and
          va.getTarget().(LocalScopeVariable).getType() instanceof PointerType and
          pointsToMap(assign.getAPredecessor(), va.getTarget(), result)
        )
        or
        not assign instanceof AddressOfExpr and
        not assign instanceof VariableAccess and
        result = PSetUnknown()
      )
    }


<a id="exercise-3"></a>

## Exercise 3

With case 1 of the `pointsToMap` being implemented we are going to
implement case 2 and 3. For case 2 we need to propagate a *points-to*
entry from a previous location and for case 3 we need to invalidate a
*points-to* entry if the entry at the previous location is a `PSetVar`
for which the variable goes out of scope at our current location `cfn`.

Note that we only consider case 2 and case 3 if the variable doesn't go
out of scope at the current location, otherwise we stop propagation for
of *points-to* entries for that variable.

    predicate pointsToMap(ControlFlowNode cfn, LocalVariable lv, PSEntry pse) {
        if isPSetReassigned(cfn, lv)
        then pse = getAnAssignedPSetEntry(cfn, lv)
        else
            exists(ControlFlowNode pred, PSEntry prevPse |
                pred = cfn.getAPredecessor() and
                pointsToMap(pred, lv, prevPse) and
                not goesOutOfScope(lv, cfn)
            |
                // case 2
                or
                // case 3
            )
    }


<a id="solution-2"></a>

### Solution

    predicate pointsToMap(ControlFlowNode cfn, LocalVariable lv, PSetEntry pse) {
      if isPSetReassigned(cfn, lv)
      then pse = getAnAssignedPSetEntry(cfn, lv)
      else
        exists(ControlFlowNode predCfn, PSetEntry prevPse |
          predCfn = cfn.getAPredecessor() and
          pointsToMap(predCfn, lv, prevPse) and
          not goesOutOfScope(lv, cfn)
        |
          pse = prevPse and
          not exists(LocalVariable otherLv |
            prevPse = PSetVar(otherLv) and
            goesOutOfScope(otherLv, cfn)
          )
          or
          exists(LocalVariable otherLv |
            prevPse = PSetVar(otherLv) and
            goesOutOfScope(otherLv, cfn) and
            pse = PSetInvalid(TVariableOutOfScope(otherLv, cfn))
          )
        )
    }


<a id="exercise-4"></a>

## Exercise 4

With the *points-to* map implemented we can find *uses* of dangling
pointers.

Implement the class `DanglingPointerAccess` that finds uses of dangling
points.

    class DanglingPointerAccess extends PointerDereferenceExpr {
      DanglingPointerAccess() {
        exists(LocalVariable lv, PSetEntry pse |
          this.getOperand().(VariableAccess).getTarget() = lv and
          ...
        )
      }
    }


<a id="solution-3"></a>

### Solution

    class DanglingPointerAccess extends PointerDereferenceExpr {
      DanglingPointerAccess() {
        exists(LocalVariable lv, PSetEntry pse |
          this.getOperand().(VariableAccess).getTarget() = lv and
          pointsToMap(this, lv, pse) and
          pse = PSetInvalid(TVariableOutOfScope(_, _))
        )
      }
    }


<a id="full-solution"></a>

## Full solution

    import cpp
    
    newtype TInvalidReason =
      TUninitialized(DeclStmt ds, LocalVariable lv) { ds.getADeclaration() = lv } or
      TVariableOutOfScope(LocalVariable lv, ControlFlowNode cfn) { goesOutOfScope(lv, cfn) }
    
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
    }
    
    newtype TPSetEntry =
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
    
    predicate goesOutOfScope(LocalVariable lv, ControlFlowNode cfn) {
      exists(BlockStmt scope |
        scope = lv.getParentScope() and
        if exists(scope.getFollowingStmt()) then scope.getFollowingStmt() = cfn else cfn = scope
      )
    }
    
    private predicate isPSetReassigned(ControlFlowNode cfn, LocalVariable lv) {
      exists(DeclStmt ds |
        cfn = ds and
        ds.getADeclaration() = lv and
        lv.getType() instanceof PointerType
      )
      or
      cfn = lv.getAnAssignedValue()
    }
    
    private PSetEntry getAnAssignedPSetEntry(ControlFlowNode cfn, LocalVariable lv) {
      exists(DeclStmt ds |
        cfn = ds and
        ds.getADeclaration() = lv
      |
        lv.getType() instanceof PointerType and
        result = PSetInvalid(TUninitialized(ds, lv))
      )
      or
      exists(Expr assign |
        assign = lv.getAnAssignedValue() and
        cfn = assign
      |
        exists(LocalVariable otherLv |
          otherLv = assign.(AddressOfExpr).getOperand().(VariableAccess).getTarget()
        |
          result = PSetVar(otherLv)
        )
        or
        exists(VariableAccess va |
          va = assign and
          va.getTarget().(LocalScopeVariable).getType() instanceof PointerType and
          pointsToMap(assign.getAPredecessor(), va.getTarget(), result)
        )
        or
        not assign instanceof AddressOfExpr and
        not assign instanceof VariableAccess and
        result = PSetUnknown()
      )
    }
    
    predicate pointsToMap(ControlFlowNode cfn, LocalVariable lv, PSetEntry pse) {
      if isPSetReassigned(cfn, lv)
      then pse = getAnAssignedPSetEntry(cfn, lv)
      else
        exists(ControlFlowNode predCfn, PSetEntry prevPse |
          predCfn = cfn.getAPredecessor() and
          pointsToMap(predCfn, lv, prevPse) and
          not goesOutOfScope(lv, cfn)
        |
          pse = prevPse and
          not exists(LocalVariable otherLv |
            prevPse = PSetVar(otherLv) and
            goesOutOfScope(otherLv, cfn)
          )
          or
          exists(LocalVariable otherLv |
            prevPse = PSetVar(otherLv) and
            goesOutOfScope(otherLv, cfn) and
            pse = PSetInvalid(TVariableOutOfScope(otherLv, cfn))
          )
        )
    }
    
    class DanglingPointerAccess extends PointerDereferenceExpr {
      DanglingPointerAccess() {
        exists(LocalVariable lv |
          this.getOperand().(VariableAccess).getTarget() = lv and
          pointsToMap(this, lv, PSetInvalid(TVariableOutOfScope(_, _)))
        )
      }
    }
    
    from DanglingPointerAccess dpa
    select dpa

