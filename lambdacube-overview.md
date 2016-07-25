# Overview of Lambda Cube typesystems

## Simply-typed lambda calculus

The simply-typed lambda calculus is *the most simple typesystem* in the lambda cube. It lets you have type constants[1] (`Int`, `Bool`, `String` etc.) and the function arrow `->` to make functions from one type to another.

```haskell
-- Functions and values in the simply-typed lambda calculus.
zero : Int
zero = 0

isFive : Int -> Bool
isFive 5 = True
isFive _ = False

thisFunctionTakesAFunction : (Int -> String) -> String
thisFunctionTakesAFunction f = f 20
```

On it's own, the simply-typed lambda calculus is okay for simple programs. Additionally, if a way to do recursion isn't provided in languages using the STLC then the programs are strongly normalising (they will always terminate).

It's the simplest typesystem in the cube though, there's a low limit to what it can express. Each axis of the lambda cube extends the kind of programs that can be written in a typesafe way.

## Polymorphism

When working in a simply-typed lambda calculus, you can end up writing a lot of duplicate code just because of different types. Like below, an example of writing identity functions for every type (there's an infinite number of them).

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

Wouldn't it be useful if we could abstract the type away and have a **variable** type that lets us have a single identity function **for all** types like we do for values in the lambda calculus with `\a -> ...`?

So we do just that in the polymorphic lambda calculus, a type variable[2] stands in, able to be replaced by any other type.

```haskell
-- identity function (just the one!) in a polymorphic lambda calculus.
identity : forall a. a -> a
identity x = x
```

And we can use this on all types:

```haskell
-- Ints...
> identity 5
5
-- ...and Strings...
> identity "Type theory is pretty"
"Type theory is pretty"
-- ...and Bools...
> identity False
False
-- ...and functions!
> identity ((\i -> i + 1) : Int -> Int)
(\i -> i + 1) : Int -> Int
```

#### A note on typeclasses

The idea pf typeclass constraints (`Show a => a -> String` and the like) is an extension or syntactic sugar for the polymorphic lambda calculus, and isn't a part of polymorphic lambda calculi by default. They allow a lot more abstraction and generalisation and are not covered in this document.

## Higher-order types

Higher-order types allow for compound types (Like `IO String` or `Set Int` in haskell).

```haskell
listOfInt : [Int]
listOfInt = [1,2,3,4,5]

setOfInt : Set Int
setOfInt = fromList [1,2,3,4,5]
```

## Dependent types

Dependent types lets us have values in types at compile time. This can seem confusing, but when using typerbole you are manipulating type expressions as values, this just gives this ability to a programming language targeting a dependent lambda calculus by letting the programmer embed lambda terms (in this library, this means being able to convert a `LambdaTerm` value to a type) at the type level.

<!-- Example wanted -->

***
##### Footnotes

[1] In typerbole's source code type constants are called mono types because of the lambda calculus implementation uses the names `Variable` and `Constant`.

[2] In typerbole's source type variables are reffered to as poly types, see [1]

***

##### Contribution

This is an educational document, pull requests for better (though accessable) explainations, typos, citations, or signposting to more information for those interested are welcome.
