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

Γ ⊢ Σ[x : X] A(x) : Type
--------------------------
Γ ⊢ (v, a) : Σ[x : X] A(x)
```

This premisse has three judgement, the first two say that we need both a value `v` of type `X` and a value `a` of type
`A(v)`. Finally we also need a Sigma type using the same types as

```
Γ, (X : Type), (A : X -> Type) ⊢ s : Σ(x : X, A(x))
Γ, (X : Type), (y : (_ : X) -> Type) ⊢ B((x, y)) : Type

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
Γ ⊢ c : Container     Γ ⊢ B : Container -> Type

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

let prod = (\x y ->
  polyElim (\_ => Poly) (\s1 p1 ->
  polyElim (\_ => Poly) (\s2 p2 ->
    MkPoly (Prod s1 s2)
           (elimSigma (\_ _ -> *)
                      (\a b -> Sum (p1 a) (p2 b)))
    y) x) :: Poly -> Poly -> Poly

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

## A type theory around containers

Containers can be implemented in a martin-lof type theory but could we possibly define a language based solely
on containers? What would the rules of such language be?


```
Γ ⊢ x : Type
Γ ⊢ y : Type
-------------------- MkContainer
Γ ⊢ m : Container

Γ ⊢ m : Container
Δ, a : x, y : Type ⊢ ty
Δ, s : a, p : y ⊢ val
------------------------- ElimCont
Γ, Δ ⊢ (case m of
  MkCont s p -> val) : ty

Γ ⊢ m1 : Container
Γ ⊢ m2 : Container
----------------------- coproduct
Γ ⊢ m1 + m2 : Container

-- I have no idea what I'm doing
Γ ⊢ m1 : Container
Γ ⊢ m2 : Container
Δ, a1 : x1, y1 : Type ⊢ ty1
Δ, a2 : x2, y2 : Type ⊢ ty2
Δ, s1 : a1, p2 : y1 ⊢ val1
Δ, s1 : a2, p2 : y2 ⊢ val2
----------------------------- ElimCont+
Γ, Δ ⊢ (case m1 + m2 of
  MkCont s1 p2 -> val1
  MkCont s1 p2 -> val2) : ty
```

## A graphical user interface

Polynomial functors are useful to describe state machine and their _interfaces_ in this project we are solely interested
in representing the interface. This provides us with the ability to tell which state machines are compatible with
each other, how to extend existing state machines and what are the tools available to contruct new machines out of
existing ones.

### Compose state machines

We've seen 3 operators on state machines: +, * and × each of them has a different meaning when composing state
machine interfaces.

#### Product *

Given state machines `m1` and `m2` we can create state machine `m1 * m2` which will be a machine that expects
an input designed for either `m1` or `m2`. If the `m1`input is given, the first machine will run, if the `m2`
input is given, the second machine will be run. Regardless of which machine runs on input, the combined machine
will return the output of both machines.

#### Coproduct +

Much like `*`, combining two machines with `+` will give the choice of running either the first or second machine.
The difference is that the combined machine will only return the result of the machine that corresponds to the input
you've given it. So if you give an input for `m1` you get the output of `m1` without the current state of `m2`.

#### Tensor ×

This operators runs two machines in parallel, as such you need to provide inputs for both machines are the same time
and the output will be the output of both machines.

### Fibonacci graphically


Using the previous combinators we can build a machine that generate the fibonacci sequence, compositionally.

First we need a machine that performs a `+n` operation where `n` is the previously computed value, such machine has a `Nat` input and a `Nat` output
therefor we can represent it as a polynomial functor `Nat X^Nat`

We run both those machines in parallel, resulting in the container `Nat*Nat X^{Nat*Nat}` this is because one
machine will update the last value of the state independently.

In order to extract the fibonacci value out of the pair of numbers we need to map it to a single number.
`Nat * Nat` returns the pair of the last two fibonacci number so to get the next one we need to add them together
this is done by sequencing our machine with a `Nat * Nat X^Nat` polynomial.



