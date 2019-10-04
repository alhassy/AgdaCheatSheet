-- Interacting with the real world ---Compilation, Haskell, and IO
-- :PROPERTIES:
-- :header-args: :tangle "CompilingAgda.agda" :comments org
-- :CUSTOM_ID: agda-interacting-with-the-real-world
-- :END:

-- # C-c C-v C-t tangles the following code into CompilingAgda.agda.
-- # Then we may compile the result using:
-- # (shell-command "NAME=CompilingAgda; time agda --compile $NAME.agda; ./$NAME")
-- #
-- # Btw: (find-file "./MAlonzo/Code/CompilingAgda.hs")

-- #+latex: {\color{white}.} \vspace{-1em}
-- #+begin_quote org
-- /Let's demonstrate how we can reach into Haskell, thereby subverting Agda!/
-- #+end_quote

-- An Agda program module containing a ~main~ function is compiled into a standalone executable
-- with ~agda --compile myfile.agda~. If the module has no main file, use the flag ~--no-main~.
-- If you only want the resulting Haskell, not necessarily an executable program, then use the flag
-- ~--ghc-dont-call-ghc~.

-- The type of ~main~ should be ~Agda.Builtin.IO.IO A~, for some ~A~;
-- this is just a proxy to Haskell's ~IO~.
-- We may ~open import IO.Primitive~ to get /this/ ~IO~, but
-- this one works with costrings, which are a bit awkward.
-- Instead, we use the standard library's wrapper type, also named ~IO~.
-- Then we use ~run~ to move from ~IO~ to ~Primitive.IO~; conversely one uses ~lift~.

-- #+latex: \begin{minipage}[c]{0.55\linewidth}
-- #+latex: \begin{tiny}

open import Data.Nat                 using (ℕ; suc)
open import Data.Nat.Show            using (show)
open import Data.Char                using (Char)
open import Data.List as L           using (map; sum; upTo)
open import Function                 using (_$_; const; _∘_)
open import Data.String as S         using (String; _++_; fromList)
open import Agda.Builtin.Unit        using (⊤)
open import Codata.Musical.Colist    using (take)
open import Codata.Musical.Costring  using (Costring)
open import Data.BoundedVec.Inefficient as B using (toList)
open import Agda.Builtin.Coinduction using (♯_)
open import IO as IO                 using (run ; putStrLn ; IO)
import IO.Primitive as Primitive

-- #+latex: \end{tiny}
-- #+latex: \end{minipage} % no space if you would like to put them side by side
-- #+latex: \begin{minipage}[c]{0.5\linewidth}
-- #+begin_quote org
-- /Agda has *no* primitives for side-effects, instead it allows arbitrary/
-- /Haskell functions to be imported as axioms, whose definitions are only/
-- /used at run-time./
-- #+end_quote
-- #+latex: \end{minipage}

-- Agda lets us use “do”-notation as in Haskell.
-- To do so, methods named ~_>>_~ and ~_>>=_~ need to be in scope ---that is all.
-- The type of ~IO._>>_~ takes two “lazy” IO actions and yield a non-lazy IO action.
-- The one below is a homogeneously typed version.

infixr 1 _>>=_ _>>_

_>>=_ : ∀ {ℓ} {α β : Set ℓ} → IO α → (α → IO β) → IO β
this >>= f = ♯ this IO.>>= λ x → ♯ f x

_>>_ : ∀{ℓ} {α β : Set ℓ} → IO α → IO β → IO β
x >> y = x >>= const y

-- Oddly, Agda's standard library comes with ~readFile~ and
-- ~writeFile~, but the symmetry ends there since it provides ~putStrLn~
-- but not [[https://hackage.haskell.org/package/base-4.12.0.0/docs/Prelude.html#v:getLine][~getLine~]]. Mimicking the ~IO.Primitive~ module, we define /two/
-- versions ourselves as proxies for Haskell's ~getLine~ ---the second one
-- below is bounded by 100 characters, whereas the first is not.

postulate
  getLine∞ : Primitive.IO Costring

{-# FOREIGN GHC
  toColist :: [a] -> MAlonzo.Code.Codata.Musical.Colist.AgdaColist a
  toColist []       = MAlonzo.Code.Codata.Musical.Colist.Nil
  toColist (x : xs) =
    MAlonzo.Code.Codata.Musical.Colist.Cons x (MAlonzo.RTE.Sharp (toColist xs))
#-}

{- Haskell's prelude is implicitly available; this is for demonstration. -}
{-# FOREIGN GHC import Prelude as Haskell #-}
{-# COMPILE GHC getLine∞  = fmap toColist Haskell.getLine #-}

-- (1)
-- getLine : IO Costring
-- getLine = IO.lift getLine∞

getLine : IO String
getLine = IO.lift
  $ getLine∞ Primitive.>>= (Primitive.return ∘ S.fromList ∘ B.toList ∘ take 100)


-- We obtain ~MAlonzo~ strings, then convert those to colists, then
-- eventually lift those to the wrapper ~IO~ type.

-- Let's also give ourselves Haskell's ~read~ method.

postulate readInt  : L.List Char → ℕ
{-# COMPILE GHC readInt = \x -> read x :: Integer  #-}

-- Now we write our ~main~ method.

main : Primitive.IO ⊤
main = run do putStrLn "Hello, world! I'm a compiled Agda program!"

              putStrLn "What is your name?"
              name ← getLine

              putStrLn "Please enter a number."
              num ← getLine
              let tri = show $ sum $ upTo $ suc $ readInt $ S.toList num
              putStrLn $ "The triangle number of " ++ num ++ " is " ++ tri

              putStrLn "Bye, "
              -- IO.putStrLn∞ name  {- If we use approach (1) above. -}
              putStrLn $ "\t" ++ name
