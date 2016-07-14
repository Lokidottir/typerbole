# Maintainance and Contribution

## Design

This library was influenced by [Subhask](https://github.com/mikeizbicki/subhask), though using it is avoided in this project for the sake of not making the library more complex than it already is.

### Deep-seated problems

This library was developed by me (@Lokidottir, at time of writing) while I was learning type theory as a personal project, in fairly deep isolation from anyone who had already studied it. There's a good chance my assumptions about what things mean conflicts with the literature, I would apprecite any issues or pull requests made pointing out or addressing issues related to this.

Additionally, this library uses an extensive number of GHC extensions. While this has made this project as flexible as it is, it also means that compile times are awful and that some ideas such as Type Families or even just the appearence of `forall`s may not be familiar to people who have learnt plain Haskell2010.

### Comments

There's no such thing as self-documenting code or too many comments. Code like below should be avoided, even if it's "obvious" what's going on.

```haskell
{-| ... <docs> ... -}
(⊑) :: (Polymorphic t) => t -> t -> Bool
t ⊑ t' = fromRight False $ do
    subs <- resolveMutuals <$> substitutionsM t' t
    applySubs <- applyAllSubsGr subs
    return (t' ≣ applySubs t)
```

The code below is better, if a bit much. This level of explaination is usually only needed in important functions with fine details, it's appreciated though.

```haskell
{-| ... <docs> ... -}
(⊑) :: (Polymorphic t) => t -> t -> Bool
t ⊑ t' =
    -- if we get a Left value then return false, the type expressions are
    -- incompatable and ordering isn't even a possibility.
    fromRight False $ do
        -- Get the substitution from both types then resolve their mutual
        -- substitutions
        subs <- resolveMutuals <$> substitutionsM t' t
        -- Make a function that applies all substitutions between t and t' to a
        -- given type expression.
        applySubs <- applyAllSubsGr subs
        -- Test if t with all substitutions applied to it is equivalent to t'.
        return (t' ≣ applySubs t)
```

### New typesystems

Introducing new typesystem classifications as typeclasses is welcomed, there's not yet a concrete structure to how the 
