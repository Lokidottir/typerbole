# typerbole ![hackage](https://img.shields.io/hackage/v/typerbole.svg?style=flat-square)

Parameterized typesystems, lambda cube typeclasses, and typechecking interfaces.

## Parameterized Typesystems

Like how datatypes such as `List a` (`[a]`), `Set a`, `Tree a` etc. in haskell have a parameter for a contained type, this library is based on the idea that a datatype that represents expressions can have a parameter for a typesystem.

### An Example: The Lambda Calculus

As an example, we can put together a datatype that represents the syntax for the Lambda Calculus:

```haskell
data LambdaTerm c v t =
      Variable v -- a variable bound by a lambda abstraction
    | Constant c -- a constant defined outside of the term
    | Apply (LambdaTerm c v t) (LambdaTerm c v t) -- an application of one term to another
    | Lambda (v, t) (LambdaTerm c v t) -- A lambda abstraction
```

This datatype has 3 parameters. The first two parameters represent constants and variables respectively, what's important is the final parameter `t` which is the parameter for the typesystem being used.

We can use the typesystem `SimplyTyped` in `Compiler.Typesystem.SimplyTyped` as the typesystem to make this a simply-typed lambda calculus, or we could slot in `SystemF`, `SystemFOmega`, `Hask`, to change the typesystem associcated with with it.

Sadly there's no magic that builds typecheckers for these (yet). Instead, using the language extensions `MultiParamTypeClasses` and `FlexibleInstances` and the `Typecheckable` typeclass from `Control.Typecheckable` we write a typechecker for each of these occurences.

```haskell
instance (...) => Typecheckable (LambdaTerm c v) (SimplyTyped m) where
    ...
instance (...) => Typecheckable (LambdaTerm c v) (SystemF m p) where
    ...
instance (...) => Typecheckable (LambdaTerm c v) (SystemFOmega m p k) where
    ...
-- and so on.
```

Or we can just ignore it all and turn it into an untyped lambda calculus:

```haskell
type UntypedLambdaTerm c v = LambdaTerm c v ()
```

## The Lambda Cube

The lambda cube describes the properties of a number of typesystems, an overview can be found [**here**](./lambdacube-overview.md). It is the basis for the library's classification of typesystems, a typeclass hierarchy where each axis is represented by a typeclass whose methods and associated types are indicitive of the properties of the axis.

![](https://github.com/Lokidottir/typerbole/blob/master/diagrams/typeclass-hierarchy.png?raw=true)

***

### TODOs

- [ ] Explore homotopy type theory (massive undertaking, don't have the energy)
- [ ] Remove all extensions that aren't light syntactic sugar from `default-extensions` and declare them explicitly in the modules they're used.
- [ ] Listen to `-Wall`
- [ ] Elaborate on the `Typecheck` type. Maybe make it a typeclass.

### Papers, Sites and Books read during development

* Introduction to generalized type systems, Dr Henk Barendregt (Journal of Functional Programming, April 1991)

* A Modern Perspective on Type Theory [(x)](https://www.amazon.co.uk/Modern-Perspective-Type-Theory-Origins/dp/1402023340)

* A proof of correctness for the Hindley-Milner type inference algorithm, Dr Jeff Vaughan [(x)](http://www.jeffvaughan.net/docs/hmproof.pdf)

* Compositional Type Checking for Hindley-Milner Type Systems with Ad-hoc Polymorphism, Dr. Gergő Érdi [(x)](https://gergo.erdi.hu/elte/thesis.pdf)

* Many wikipedia pages on type theory.
