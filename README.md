# kiddoo interpreter

Reference implementation of an interpreter for the kiddoo language. Language motivated by the use of math expressions to functionally compute answers. Note, an earlier iteration of the idea can be found [here](https://github.com/erziebart/kiddoo), but is no longer being worked on.

### Feature highlights

1. human-readable expressions: meant to mimic the way someone might write math in a marked-up format; includes support for all standard operations (+ - \* \\ ^), implicit multiplication, and short circuits.

2. boolean algebra and comparison: operators (== != < > <= >= & |) allow manipulation of true/false values; can be combined with piecewise operator (;) to achieve conditionals and control flow.

3. user-defined functions: identifiers fully extensible, unlimited nesting with intuitive scoping, support for full recursion to achieve loops.

4. control of evaluation order: functions defined with the 'def' keyword are evaluated lazily; can alternately use 'con' keyword to define an eagerly evaluated constant. Can pass normal function arguments to evaluate applicatively or pass function references to achieve normal order evalutation.
