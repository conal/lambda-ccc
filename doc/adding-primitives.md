## Notes on adding primitive operations and types

*[Please suggest where more details as needed below.]*

### Primitive operations

*   Start with the `Prim` GADT definition in circat's `Circat.Prim`.
*   Add a new constructor for your primitive.
*   Search the circat and lambda-ccc projects (e.g., using git-grep) for a similar, already-existing `Prim` constructor, and support for your new constructor.
*   Compile, and look for errors and warnings, particularly for non-exhaustive or overlapping pattern matching.

### Primitive types

When possible, give a way to interpret your type in terms of simpler types, rather than adding a primitive primitively.
See `Circat.Rep`.
In case you really need a new primitive:

*   Start with the `Lit` GADT definition in circat's `Circat.Prim`.
*   Add a new constructor for your primitive type.
*   Search for an existing `Lit` constructor in circat and lambda-ccc, and add similar support for your type.


----

To explain:

*   `Circat.Classes`: `OkDom`
*   `Circat.Circuit`:
    *   `Buses`. Search for `IntB` references, and add similar.
    *   `Ty`. Search for `IntT` references, and add similar.
