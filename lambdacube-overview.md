### Overview of Lambda Cube typesystems

#### Simply-typed lambda calculus

The simply-typed lambda calculus is the simplest and least expressive typesystem of the lambda cube. In the simply-typed lambda calculus, there are only two constructs: Mono types (such as `Int`, `Bool`, or whatever else is defined) and the `->` constructor.

```haskell
-- Functions and values in the simply-typed lambda calculus.
zero : Int
zero = 0

isFive : Int -> Bool
isFive 5 = True
isFive _ = False
```

On it's own the simply-typed lambda calculus lacks the ability to express recursion without typerrors or functions and values whose type is generic, and many other useful constructs. Each axis of the lambda cube adds different kinds of expressiveness, allowing more and more programs to be validated at compile time safely.

#### Polymorphism

Polymorphism allows you to write type expressions that expose poly types (also referred to as type variables). In a non-polymorphic type expression associated with the identity function we'd need to declare a new identity function for every type.

```haskell
-- Identity functions in the simply-typed lambda calculus.
identityInt : Int -> Int
identityInt x = x

identityBool : Bool -> Bool
identityBool x = x

identityIntToInt : (Int -> Int) -> (Int -> Int)
identityIntToInt x = x
...
-- Etc. Do for the infinite number of types that exist.
```

Instead, a single identity function can work **for all** types.

```haskell
-- identity function (just the one!) in a polymorphic lambda calculus.
identity : forall a. a -> a
identity x = x
```

#### Higher-order types

Higher-order types allow for compound types (Like `IO String` or `Set Int` in haskell).

```haskell
listOfInt : [Int]
listOfInt = [1,2,3,4,5]

setOfInt : Set Int
setOfInt = fromList [1,2,3,4,5]
```

#### Dependent types
