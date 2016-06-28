# typerbole

Type theory that isn't so scary.

### Lambda Calculus

This library uses a minimal lambda calculus representation as an AST to manipulate and typecheck expressions:

```haskell
data LambdaExpr v t =
      Var v
    | Apply (LambdaExpr v t) (LambdaExpr v t)
    | Lambda (v, t) (LambdaExpr v t)
```

An important part of this datatype is the parameter `t`, which represents the type system used. With this being a parameterized part of the AST, we can slot in any typesystem we choose!

### Type Expressions

> `forall a. a`, `Int -> Int`, `forall a. a -> IO Bool`...

***

### Supported lambda-cube axies

- [x] Simply-typed lambda calculus
- [x] Polymorphic lambda calculus
- [x] Higher-order lambda calculus
- [ ] Dependently-typed lambda calculus

### TODOs

- [ ] Document the type expression psudocode
- [ ] Design a typeclass for typesystems with haskell-like (`Num a => a`) typeclass constraints.
- [ ] Add constants to the lambda calculus AST.
- [ ] Provide a default way of evaluating lambda expressions.
- [ ] Make the quasiquoters use the lambda cube typeclasses instead of specific typesystem implementations.
- [ ] Have a typeclass for evaluatable calculi (Kappa calculus and the like). This may be unnecessary abstraction.
- [ ] Subhask-style automated test writing.
- [ ] More formally represent typing rules instead of just implementing typesystems ad-hoc and hoping they are at least equivalent. (Would require a significant amount of refectoring)
