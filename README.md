
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

## Operations on poly

Polynomial functors benefit from a lot of (monoidal) operations on them. Here are the
ones we are going to use for combining dynamical systems.

### Tensor

The tensor of two polynomial functors `c1, c2 : Poly` is the product of it's components.
This ensures the running of both systems at the same time by providing inputs to both
systems simultaneously.

```
(×) : Poly -> Poly -> Poly
(out1, in1) × (out2, in2) = (out1 * out2, λ(o1, o2) . in1 o1 * in2 o2)
```
### Product

The product of two polynomial functors `c1, c2 : Poly` is the product of it's outputs
and the coproduct of its inputs. Effectively giving the choice of which system to
interact with, but updating both at once.

```
(*) : Poly -> Poly -> Poly
(out1, in1) * (out2, in2) = (out1 * out2, λ(o1, o2) . in1 o1 + in2 o2)
```

### Coproduct

The coproduct of two polynomial functors `c1, c2 : Poly` is the product of it's outputs
and the coproduct of its inputs. Effectively giving the choice of which system to
interact with, but updating both at once.

```
(+) : Poly -> Poly -> Poly
(out1, in1) + (out2, in2) = (out1 + out2, λx. case x of
                                                   inl l -> in1 l
                                                   inr r -> in2 r)
```


## Simulating systems

David Spivak's $Poly$ book gives us a way to implement state machines using polynomial
functor morphisms. In that context, the state of a machine is given by the codomain
of the morphism and the interface is given by the domain.

## How to use

There are three ways of interacting with the _Poly-Engine_:

- Compile a file
- Run a REPL
- Import the engine as a library

### Compile a file

```bash
cabal run lp -- file.lp
```

This will compile the file, import all the definitions and start an interactive session.

### Run as REPL

```bash
cabal run lp
```

This will run the repl without any definitions

### Import as library

This is the most involved but also the most useful since it allows to interact with the
engine from Haskell, a language which cannot deal with the full expressivity of Polynomial functors.

First you need to import all the core-modules:

```haskell
import LambdaPi.AST (ITerm, Value)
import LambdaPi.Common (Name (..))
import LambdaPi.Init (MLTT' (..), PolyState, lpaddData, initialContext)
import LambdaPi.Parser (parseLet)
import LambdaPi.Printer (cPrint)
import LambdaPi.Quote (quote0)
import LambdaPi.REPL (Interpreter (..), LangState (..), LangTerm (..), check, parsePure)
```

This imports all the constructors for terms, types, contexts and interactive sessions.

Interacting with the engine involved supplying an existing context, a new term and obtaining a resulting
context from typechecking this term. One can achieve this functionality with the `check` function. It
allows to customise the printing and update of the state.

However this is quite generic, for an easier interface see `checkSimple` or `checkPure`, both work with
the same principles.

The engine makes use of the `capability` library which eases the embedding of the engine within existing
monad stacks. Chose the monad stack to use and run the engine within it.

## Demos

### Baby steps

A good first example of a Polynomial is what `x` represents, to be perfectly explicit, it's `1 * x ^ 1`.
In the poly engine we create a new polynomial by calling the constructor `MkPoly` and providing it two
arguments, in this case the unit type. The Poly-Engine doesn't have a unit-type but we can create one:

```
> data Unit = MkUnit
Unit :: *
> let u = MkPoly Unit (\_ -> Unit)
u :: [Poly]
```

The second argument is a lambda because it is _indexed_ over the first argument, in that case we need to
write a function `Unit -> Type` but because we always return unit no matter what, we simply ignore the
argument.

This creates the polynomial `x`.

### Combining polys

The Poly-Engine has the ability to combine multiple polynomials using the `parallel`, `multiplication`, and
`choice` functions from `stdlib.lp`. Using the unit polynomial from above and the `poly1` value from
stdlib we can build bigger expressions. `poly1` is defined as `MkPoly Nat Fin`. The library also has `poly2`
defined as `MkPoly Nat (Vect Nat)`. To familiarize yourself with the monoidal operations on poly, try the 
following:

```
> choice u poly1
> parallel u u
> multiplication poly1 poly2
```

You will notice the resulting terms are quite large and hard to read, this is due to two things:
- basic data types like pairs are encoded with their more generic `Sigma` variant which introduces some noise.
- In general printing lambda is a bit fraught. If we ignore the arugment we could chose to print only the body
  but then two terms with the same type will have different printed strings if they have different implementations.

### Building dynamical systems

A typical example of a dynamical system is one that increments a number. In that case the interface is `(Unit , Nat)`
we represent this with the poly `let api = MkPoly Nat (\_ -> Unit)` the state will be a natural number so we represent it as
`let state = MkUnit Nat (\_ -> Nat)`

/!\ unimplemented
The full interactive system would be defined as the morphism between `state` and `api`.

### The standard library

The file `stdlib.lp` provides a good demonstration of the engine by implementing a lot of the code
datastructures. In particular it defines the three operators above and also demonstrates that we
can create more as necessary. 

```
cabal run lp -- stdlib.lp
```


