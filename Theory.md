# Polynomial functor theory

This library is based on polynomial functors. This document outlines the necessary theory in order to develop the tools.

## Containers/Polynomials in a nutshell

Polynomial functors are defined as a pair of a set and a family indexed over that set. Using types we could write
the following in pseudocode:

```
type Container = (x : Type, f : x -> Type)
```

"Sets" and "indexed families" are terms removed from the practice of programming instead we are going to use the
terms "types" and "dependent type". This way, a container is a pair of a _type_ and a _dependent type_. The
dependency stems from the use of the first value of the pair.

## Martin-lof type theory

Martin-lof type theory is a dependent type theory that allows us to express those concepts in a programming language.
Type theories are written using inference rules, those are syntax in order to define what we can deduce in our
type-system:

```
Γ ⊢ A    Γ ⊢ B  <- premisse
--------------
  Γ ⊢ A ∧ B  <- conclusion
  \_______/
      |
      v
   judgement
```

The judgement of a martin-lof type theory are as follow:

#### Unit

```
       <- no premisses
---------
Γ ⊢ Unit
```
The unit type exists
```
       <- no premisses
---------
Γ ⊢ () : Unit
```
We can create a value of type `Unit`

#### Void

There is no way to construct an empty type but if we have an empty
type in our context we can deduce any other value.

```
Γ ⊢ A : Type
------------
Γ, x : Void ⊢ end : A
```

#### Pi/"dependent function" types

```
Γ, x : X ⊢ A(x) : Type
----------------------
Γ ⊢ (x : X) -> A(x) : Type
```

If we apply `x` to `A` and obtian a valid type then we can write the
dependent function type `(x : X) -> A(x)` and it's also a valid type,
it abstracts away the dependency on `x`.

```
Γ, x : X ⊢ a(x) : A(x)
----------------------
Γ ⊢ (λ (x : X) => a(x)) : (x : X) -> A(x)
```

If we have a value `a(x)` that depends on `x` then we can abstract it into a lambda that expects to take an `x` as
argument and return `a(x)`. It's type is the corresponding dependent function type.

```
Γ ⊢ f : (x : X) -> A(x)    Δ ⊢ v : X
------------------------------------
Γ, Δ ⊢ f(v) : A(v)
```

If we have a value `f` whose type is a function type, we can apply it to a value `v` of type `X` which is the
type of the input of the function, and obtain a value `A(v)` which is the type of the output of the function
when applied to the value `v`.

#### Sigma/"Dependent product" types

```
Γ, x : X ⊢ A(x) : Type
----------------------
Γ ⊢ Σ(x : X, A(x)) : Type
```

The premisse is the same than for dependent function types but the conclusion is different. We're going to see
how it differs in the next rule:

```
Γ ⊢ v : X    Γ ⊢ a : A(v)

Γ ⊢ Σ(x : X, A(x)) : Type
--------------------------
Γ ⊢ (v, a) : Σ(x : X, A(x))
```

This premisse has three judgement, the first two say that we need both a value `v` of type `X` and a value `a` of type
`A(v)`. Finally we also need a Sigma type using the same types as

```
Γ ⊢ s : Σ(x : X, A(x))

Δ, (x : X), (y : A(x)) ⊢ b(x, y) : B((x, y))
----------------------------------------
Γ, Δ ⊢ match s with (λ (x : X) => λ (y : A(x)) => b(x, y)) : B(s)
```

## Containers in Martin-lof type theory

Using the previous rules we can define containers as a combination of Sigma and Pi types:

```
------------
Γ ⊢ Container : Type
```
Containers are types.

```
Γ ⊢ X : Type    Γ ⊢ f : (x : X) -> Type
---------------------------------------
Γ ⊢ MkCont X f : Container
```
If you have a type and a dependent type that depends on the firs type you can make a container.

```
Γ ⊢ c : Container

Δ, (x : Type), (y : x -> Type) ⊢ b(MkCont x y) : B(c)
--------------------------------------------
Γ, Δ ⊢ match c with (λ (x : Type) => λ (y : x -> Type) => b(x, y)) : B(c)
```

This is how you destructure containers.

With this we can finally develop the necessary technology to manipulate containers in different ways.
We're interested in monoidal operations on containers, so things of type `Container -> Container -> Container`
in particular there are three operations that allow us to compose state machines: product, coproduct and tensor,
here they are:

#### Product

```
Γ ⊢ c1 : Container
Γ ⊢ c2 : Container
------------------
Γ ⊢ match c1 with λ s1 => λ p1 =>
    match c2 with λ s2 => λ p2 =>
      MkCont (c1, c2) (λx => match x with
        λ a => λ b => p1(a) + p2(b)
```

where `+` is the coproduct on types, we can define it as `type (+) a b = Σ(Bool, λb => if b then a else b)`
assming we have `Bool` in our type theory.

#### coproduct
```
Γ ⊢ c1 : Container
Γ ⊢ c2 : Container
------------------
Γ ⊢ match c1 with λ s1 => λ p1 =>
    match c2 with λ s2 => λ p2 =>
      MkCont (c1 + c2) (λx => match x with
        λ a => p1(a)
        λ b => p2(b)
```

#### Tensor

```
Γ ⊢ c1 : Container
Γ ⊢ c2 : Container
------------------
Γ ⊢ match c1 with λ s1 => λ p1 =>
    match c2 with λ s2 => λ p2 =>
      MkCont (c1, c2) (λx => match x with
        λ a => λ b => (p1(a), p2(b))
```
