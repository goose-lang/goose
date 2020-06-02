## Plan for Implementation

### Basic Interfaces
[X] Create tuple of methods, ie `(catHello, catBye)`
[X] Return (method, typeDescriptor, value) when interface is called, value is a pointer to original value 
[X] Create interfaceT type in coq, defined by a list of arrowT methods, including `interfaceT []` empty interface 
[X] No proofs for now, including typecheck

### Type Switches 

[X] Handle empty interfaces, ie 
```
func switch(x interface{}) ...
```

[X] Built method table as collection of methods, string, anyT (needs dynamic value)
[] Sort order of methods
[X] Use struct for collection of methods (use search field by name function), ie

```
(getMethod x.1 "Get" )
```

[] Checking types, ie `if x.2 == "Get" then x.3 else panic`

[] Optimization: Definitions for structs to interfaces (all combinations), ie 
```
Definition catToAnimal := 
    (catHello, catBye)
```

### Special cases

[] Slice (fail)
[] Map
[] Downcast interfaces (fail) 
[] Make sure there aren't double pointers, ie
```
cat := x.(*Cat)
cat := x.(Cat)
```