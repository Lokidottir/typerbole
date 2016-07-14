# typerbole

Type theory that isn't so scary.

## Purpose

This library came from wanting to have a framework for developing typesystems that wasn't too restrictive and also signposted people unfamiliar with type theory.

## The Library

### Lambda Calculus

This library uses a minimal lambda calculus representation as an AST to manipulate and typecheck expressions:

```haskell
data LambdaTerm c v t =
      Variable v
    | Constant c
    | Apply (LambdaTerm v t) (LambdaTerm v t)
    | Lambda (v, t) (LambdaTerm v t)
```

An important part of this datatype is the parameter `t`, which represents the type system used. With this being a parameterized part of the AST, we can slot in any typesystem we choose!

### The Lambda Cube

The lambda cube describes the properties of a number of typesystems, an overview can be found [here](./lambdacube-overview.md).

The lambda cube is the basis for the library's classification of typesystems, a typeclass hierarchy

***

### Supported lambda-cube axies

- [x] Simply-typed lambda calculus
- [x] Polymorphic lambda calculus
- [x] Higher-order lambda calculus
- [ ] Dependently-typed lambda calculus

### TODOs

- [ ] Put together a working travis file.
- [ ] Document the type expression psudocode
- [ ] Design a typeclass for typesystems with haskell-like (`Num a => a`) typeclass constraints.
- [ ] Add constants to the lambda calculus AST.
- [ ] Provide a default way of evaluating lambda expressions.
- [ ] Make the quasiquoters use the lambda cube typeclasses instead of specific typesystem implementations.
- [ ] Have a typeclass for evaluatable calculi (Kappa calculus and the like). This may be unnecessary abstraction.
- [ ] Subhask-style automated test writing.
- [ ] More formally represent typing rules instead of just implementing typesystems ad-hoc and hoping they are at least equivalent (Would require a significant amount of refectoring, if it gets to a point where the library becomes less accessable then stick with the ad-hoc approach).
