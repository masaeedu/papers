{-# LANGUAGE TypeFamilies #-}
module Main where

import Prelude hiding (id, (.))
import Control.Category

-- The paper is about the the ability to express monadic computations using "composable continuations". Composable continuations (in languages that don't support them) can in turn can be represented using "ordinary" non-composable continuations and state.
-- TODO:
-- - obtain precise definitions of "composable" and "non-composable" continuations


{- 1.1 - Background and overview
- Monadic effects are useful for representing state, control operators, I/O etc.
- In impure functional programming, both linguistic constructs like exception handling and external effects like I/O "obey a monadic discipline"
- The paper aims to show that any monadic effect expressible in a functional language can be synthesized from first-class continuations and a storage cell
- Outline of paper:
  - 1.2: introduction to monads and "monadic reflection" as an internalization of monadic bind into a language
  - 2:
    - Formal correspondence betweeen "monadic style" and CPS
    - Expressing operations on monadic computations in terms of two operations for composable continuations
    - Expresssing the two operations in terms of non-composable continuations and state
  - 5: Complete embedding as executable code
-}

{- 1.2  - Monads and monadic reflection
A monad consists of the following operations:

class Functor m => Monad m
  where
  return :: a -> m a                 -- η in the paper
  bind  :: (a -> m b) -> m a -> m b -- _* postfix operator in the paper

The laws for these are the annoying version of the monad laws:
-}

bind :: Monad m => (a -> m b) -> m a -> m b
bind = (=<<)

lid1, lid2 :: Monad m => m a -> m a
lid1 = bind return; lid2 = id

rid1, rid2 :: Monad m => (m a -> m a) -> m a -> m a
rid1 f = bind f . return; rid2 f = f

assoc1, assoc2 :: Monad m => (b -> m c) -> (a -> m b) -> m a -> m c
assoc1 f g = bind (bind f . g)
assoc2 f g = bind f . bind g

{-
In the paper, they discuss an impure call-by-value functional language in which the monadicity of computations is baked into the language.

In other words, the language is based on "Moggi's principle", which is to say:

> Computations of type α correspond to values of type Tα

Thus a side-effect free computation takes the form `η a` (where `η = return`), and applying an effectful transformation to an effectful value takes the form `f* t`.

More precisely, we can add model this "monadic reflection" principle in the judgment rules of the language. So we say:

```
Γ ⊢ E : Tα
__________
Γ ⊢ μ(E) : α
```

and:

```
Γ ⊢ E : α
__________
Γ ⊢ [E] : Tα
```

Where the linguistic constructs μ and [_] are referred to as monadic "reflection" and "reification" respectively. The way we are supposed to think about these is I think as a way to sort of shuffle effects under the linguistic rug, then recover them when necessary.

Then they proceed to an example with exceptions. So they have:

```
T(α) := α + exn
η = λa → inl a
f* = λt → case t of inl a → f a ‖ inr e → inr e
```

TODO: What exactly do these expressions represent? Are they types/terms of a language or something to do with the semantics of a language yet to be described?

They give an example of some operations that can be implemented in a language with "monadic reflection" for the exception monad given above:

```
raise E          := μ(inr E)
E1 handle e ⇒ E2 := case [E1] of inl a → a ‖ inr e → E2
```

So for `E : α + exn`, `raise E : α`, i.e. the monadic effect has been swallowed up into the language. To implement the `handle` language construct, we go the other direction, `E1 : α`, but in terms of the evaluation semantics this term might represent an effectful computation. So we can reflect the monadic context of the term using `[E] : α + exn` and then case analyze it to do error handling.

TODO: This is a bit confusing. Does `[E] : α + exn` mean that `α` might contain yet more exceptions (since the rule is that computations of type `α` are impure?

There is a relationship between `μ` and `[_]`, called the "correspondence principle":

```
μ([E]) ≡ E : α
[μ(V)] ≡ V : Tα
```

I think I would summarize this section as `μ = "run"`, `[-] = "suspend"`.

-}

{- 2 - Monads and CPS

Now they describe two translations from an impure language with this monadic reflection business into a pure lambda calculus in which the monad and its operations exist. They only deal with impure "functions", primitive variables, and "reflected" terms, but say that sums, products etc. can be dealt with straightforwardly.

We will just use Haskell itself as the pure metalanguage that is the target of the translation.

Here is a representation of the types and terms for the impure CBV language:

-}

data LangType b
  where
  BaseType   :: b -> LangType b
  (:=>:)     :: LangType b -> LangType b -> LangType b
  Reflection :: LangType b -> LangType b

data Var (a :: LangType *) = Var String

data LangTerm (x :: LangType *)
  where
  Lit :: x
      -> LangTerm ('BaseType x)

  Ref :: Var a
      -> LangTerm a

  Lam :: Var a
      -> LangTerm b
      -> LangTerm (a ':=>: b)

  App :: LangTerm (a ':=>: b)
      -> LangTerm a
      -> LangTerm b

  Mu  :: LangTerm ('Reflection x)
      -> LangTerm x               -- "Monadic reflection"

  Brk :: LangTerm x
      -> LangTerm ('Reflection x) -- "Monadic reification"

newtype LHom a b = LHom { runLHom :: LangTerm (a ':=>: b) }

instance Category LHom
  where
  id = LHom $ Lam (Var "x") $ Ref $ Var "x"
  LHom bc . LHom (Lam a b) = LHom $ Lam a $ App bc b

-- Imagine a category where:
-- - the objects are the types of the lambda calculus we're modeling
-- - the set of morphisms between two types is terms representing functions with the appropriate domain and codomain

class Category p => Closed (hom :: k -> k -> k) (p :: k -> k -> *)
  where
  closed :: p a' a -> p b b' -> p (hom a b) (hom a' b')

instance Closed ('(:=>:)) LHom
  where
  closed a'a bb' =
    let f = Var "f"
    in LHom $ Lam f (runLHom $ bb' . LHom (Ref f) . a'a) -- TODO: Missing alpha substitution here

{-

and now we have to translate this into Haskell code:

-}

data Context :: forall a. a -> * -> *

type family Translate (c :: * -> * -> *) (m :: * -> *) (it :: LangType *) :: *
  where
  Translate c m ('BaseType b)   = b
  Translate c m (a ':=>: b)     = c (Translate c m a) (m (Translate c m b))
  Translate c m ('Reflection a) = m (Translate c m a)

mapContext :: (b -> b') -> Context a b -> Context a b'
mapContext = _

firstContext :: Context a b -> Context a' b
firstContext = _

noContext :: a -> Context x a
noContext = _

distributeContext :: Monad m => m (Context a b) -> Context a (m b) 
distributeContext = _

-- dimapContext :: (a -> a') -> (b -> b') -> Context a b -> Context a' b'
-- dimapContext = _

-- translate :: Monad m => LangTerm Context x -> m (Translate Context m x)
-- translate (Lit x)   = return x
-- translate (Lam ab)  = return $ firstContext $ mapContext translate $ ab
-- translate (App f v) = _ (bind (\f' -> bind f' $ translate v)) (translate f)
-- translate (Mu c)    = bind id $ translate c
-- translate (Brk v)   = return $ translate v

main :: IO ()
main = putStrLn "Hello, Haskell!"
