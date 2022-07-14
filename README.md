
# Polynomial Functors library

A haskell library to manipulate dynamical systems using _polynomial functors_.

A Polynomial functor can be represented as a dependent type: `Σ_{i: Type}. i -> Type`
We can see those polynomial functors as APIs or _interfaces_ for dynamical systems,
typically state machines or diagramatic processes. Because they benefits from lots
of monoidal products, we can use those monoidal product to combine together multiple
polynomial functors leading to accurate representation of complex systems.

The interface of a dynamical system is its `input/output` pair, which we represent
as a polynomial functor as `output X^input`, that is, the first part of the polynomial
are the outputs and the second is the input.

## Tensor

The tensor of two polynomial functors `c1, c2 : Poly` is the product of it's components.
This ensures the running of both systems at the same time by providing inputs to both
systems simultaneously.

```
(×) : Poly -> Poly -> Poly
(out1, in1) × (out2, in2) = (out1 * out2, λ(o1, o2) . in1 o1 * in2 o2)
```
## Product

The product of two polynomial functors `c1, c2 : Poly` is the product of it's outputs
and the coproduct of its inputs. Effectively giving the choice of which system to
interact with, but updating both at once.

```
(*) : Poly -> Poly -> Poly
(out1, in1) * (out2, in2) = (out1 * out2, λ(o1, o2) . in1 o1 * in2 o2)
```

## Coproduct

The coproduct of two polynomial functors `c1, c2 : Poly` is the product of it's outputs
and the coproduct of its inputs. Effectively giving the choice of which system to
interact with, but updating both at once.

```
(+) : Poly -> Poly -> Poly
(out1, in1) + (out2, in2) = (out1 + out2, λx. case x of
                                                   inl l -> in1 l
                                                   inr r -> in2 r)
```

