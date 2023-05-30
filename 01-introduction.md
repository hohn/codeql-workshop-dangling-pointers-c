---
layout: workshop-overview
title: Introduction
course_number: LDF-204
banner: banner-code-graph-shield.png
octicon: package
toc: false
---

## Introduction
A dangling pointer is a memory safety violation where the pointer does not point to a valid object.
These dangling pointers are the result of not modifying the value of the pointer after the pointed to object is destructed or not properly initializing the pointer.

The use of a dangling pointer can result in a security issue, particularly in C++ if that dangling pointer is used to invoke a *virtual* method and an attacker was able to overwrite the parts of the memory that would have contained the `vtable` of the object.

The following snippet demonstrates how a dangling pointer can occur:

```cpp
void dangling_pointer() {
	char **p = nullptr;
	{
		char * s = "hello world";
		p = &s;
	}
	printf("%s", *p);
}
```

Another less obvious case is:

```cpp
void dangling_pointer() {
	std::string_view s = "hello world"s;
	std::cout << s << std::endl;
}
```

After the full expression from the preceding example is evaluated, the temporary object is destroyed.

Many more interesting examples are discussed here: https://herbsutter.com/2018/09/20/lifetime-profile-v1-0-posted/

To find these issues, we can implement an analysis that tracks lifetimes. A nice specification for a local lifetime analysis is given by https://github.com/isocpp/CppCoreGuidelines/blob/master/docs/Lifetime.pdf.

The gist of the analysis is, for each local variable, to track the things that it can point to at a particular _location_ in the program. These _locations_ are other local variables and special values for global variables, null values, and invalid values. Whenever a variable goes out of scope, each reference to that variable in a points-to set is invalidated.


In the next few exercises, we are going to implement a simplified version of the lifetime profile to find the dangling pointer in the following example:

```cpp
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
```

The simplified version will track 3 possible *points-to* values.

1. Variable; A pointer points to another pointer. We will only consider local variables represented by the class `LocalVariable`.
2. Invalid; A pointer is not initialized or points to a variable that went out of scope.
3. Unknown; A pointer is assigned something other than the address of another
   `LocalVariable` (e.g., the address of a string.).
   
