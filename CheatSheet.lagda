# -*- org -*-
# | ~C-x C-a~ | transform org ~org-agda~ blocks to literate Agda blocs        |
# | ~C-x C-a~ | transform literate Agda code delimiters to org ~org-agda~ src |

#+TITLE: Agda CheatSheet
# SUBTITLE: ---Reference Sheet for “What I'm Currently Learning”---
#+MACRO: blurb Basics of Agda, a total and dependently-typed functional language (•̀ᴗ•́)و
#+AUTHOR: [[http://www.cas.mcmaster.ca/~alhassm/][Musa Al-hassy]]
#+EMAIL: alhassy@gmail.com
#+INCLUDE: CheatSheet/CheatSheetSetup.org
#+PROPERTY: header-args :results none
#+TODO: Todo | spacing LaTeX

* LaTeX Extra, Local, Setup  :ignore:

# Empty by default.
#+LATEX_HEADER: \def\cheatsheeturl{https://github.com/alhassy/AgdaCheatSheet}

# The following are the defaults & may be omitted.
#+LATEX_HEADER: \def\cheatsheetcols{2}
#+LATEX_HEADER: \landscapetrue
#+LATEX_HEADER: \def\cheatsheetitemsep{-0.5em}

# Example unicode declarations; see section “unicode” below.
#+LATEX_HEADER: \newunicodechar{‼}{\ensuremath{!\!!}}
#+LATEX_HEADER: \newunicodechar{𝕨}{\ensuremath{\mathbb{w}}}
#+LATEX_HEADER: \newunicodechar{≈}{\ensuremath{\approx}}
#+LATEX_HEADER: \newunicodechar{ℓ}{\ensuremath{\ell}}
#+LATEX_HEADER: \newunicodechar{ω}{\ensuremath{\omega}}
#+LATEX_HEADER: \newunicodechar{⁰}{\ensuremath{^0}}
#+LATEX_HEADER: \newunicodechar{⁴}{\ensuremath{^4}}
#+LATEX_HEADER: \newunicodechar{♯}{\ensuremath{\sharp}}
#+LATEX_HEADER: \newunicodechar{α}{\ensuremath{\alpha}}
#+LATEX_HEADER: \newunicodechar{β}{\ensuremath{\beta}}


#+LATEX_HEADER: \newunicodechar{⇨}{\ensuremath{\circlearrowright}}

#
# LATEX_HEADER: \newunicodechar{⇨}{\ensuremath{\rotatebox[origin=c]{180}{$\Lsh$}}}

* Contents :TOC:QUOTE:
#+BEGIN_QUOTE
- [[#administrivia][Administrivia]]
- [[#dependent-functions][Dependent Functions]]
- [[#reads][Reads]]
- [[#dependent-datatypes][Dependent Datatypes]]
- [[#the-curry-howard-correspondence----propositions-as-types][The Curry-Howard Correspondence ---“Propositions as Types”]]
  - [[#adding-to-the-table][Adding to the table]]
- [[#equality][Equality]]
- [[#break][break]]
- [[#modules----namespace-management][Modules ---Namespace Management]]
  - [[#anonymous-modules-and-variables][Anonymous Modules and Variables]]
  - [[#break][break]]
  - [[#module-keywords][Module Keywords]]
- [[#records][Records]]
- [[#interacting-with-the-real-world----compilation-haskell-and-io][Interacting with the real world ---Compilation, Haskell, and IO]]
- [[#absurd-patterns][Absurd Patterns]]
  - [[#preconditions-as-proof-object-arguments][Preconditions as proof-object arguments]]
- [[#mechanically-moving-from-bool-to-set----avoiding-boolean-blindness][Mechanically Moving from ~Bool~ to ~Set~ ---Avoiding “Boolean Blindness”]]
#+END_QUOTE

* COMMENT ~LaTeX~ commands ↦ ~#+latex: \LaTeX~

  Execute the following block, with ~C-c C-c~ anywhere inside it,
  to hide all LaTeX specific items away so that, for example, the generated HTML
  does not show them.

  #+BEGIN_SRC emacs-lisp :results no
(defun my/replace-in-buffer (this that)
  "Replace every occurance of regexp ‘this’ with ‘that’
   in the current buffer."
   (interactive)
   (save-excursion
    (beginning-of-buffer)
    (while (re-search-forward this nil t)
      (replace-match that)
    ))
)

;; Replace newline, any number of space, then room or vspace with a #+latex: beforehand.
(let (this that)
  (dolist (kp '( ( "^[ ]*\\\\room" . "#+latex: \\\\room")
         ( "^[ ]*\\\\vspace" . "#+latex: \\\\vspace")
         ( "^[ ]*\\\\newpage" . "#+latex: \\\\newpage")
         ( "^[ ]*\\\\columnbreak" . "#+latex: \\\\columnbreak")
         ))
    (setq this (car kp))
    (setq that (cdr kp))
    (my/replace-in-buffer this that)
   )
)
  #+END_SRC

  #+RESULTS:

* Administrivia

    #+latex: \hspace{-1.3em}
  Agda is based on @@latex:Martin-L{\"o}f's@@ intuitionistic type theory.

  | Agda | ≈ | Haskell + Harmonious Support for Dependent Types |

In particular, /types ≈ terms/ and so, for example,
~ℕ ∶ Set = Set₀~ and ~Setᵢ ∶ Setᵢ₊₁~.
One says /universe/ ~Setₙ~ has /level/ $n$.

⇨ It is a programming language and a proof assistant.
#+latex: \newline {\color{white}.}\hspace{0.3em}
  A proposition is proved by writing a program of the corresponding type.

⇨ Its Emacs interface allows programming by gradual refinement
  of incomplete type-correct terms. One uses the “hole” marker ~?~
  as a placeholder that is used to stepwise write a program.

⇨ Agda allows arbitrary mixfix Unicode lexemes, identifiers.
+ Underscores are used to indicate where positional arguments.
+ Almost anything can be a valid name; e.g., ~[]~ and ~_∷_~ below.
  Hence it's important to be liberal with whitespace: ~e:T~ is a valid identifier
  whereas ~e ∶ T~ declares ~e~ to be of type ~T~.

#+latex: \begin{parallel}

#+latex: \begin{tiny}
#+BEGIN_SRC agda
module CheatSheet where

open import Level using (Level)
open import Data.Nat
open import Data.Bool hiding (_<?_)
open import Data.List using (List; []; _∷_; length)
#+END_SRC
#+latex: \end{tiny} \columnbreak

Every Agda file contains at most one top-level module whose name
corresponds to the name of the file.
This document is generated from a ~.lagda~ file.

#+latex: \end{parallel} \vspace{-1em}

* Dependent Functions

    #+latex: \hspace{-1.3em}
A /dependent function type/ has those functions whose result /type/ depends
on the /value/ of the argument. If ~B~ is a type depending on a type ~A~, then
~(a ∶ A) → B a~ is the type of functions ~f~ mapping arguments ~a ∶ A~ to values ~f a ∶ B a~.
Vectors, matrices, sorted lists, and trees of a particular height are all examples of dependent types.

#+latex: \begin{parallel}
For example, /the/ generic identity function takes as /input/ a type ~X~ and returns as /output/
a function ~X → X~. Here are a number of ways to write it in Agda.

#+latex: \vspace{0.5em}\hrule\vspace{0.5em}

All these functions explicitly require the type ~X~ when we use them, which is silly since
it can be inferred from the element ~x~.

#+latex: \columnbreak

#+BEGIN_SRC agda
id₀ : (X : Set) → X → X
id₀ X x = x

id₁ id₂ id₃ : (X : Set) → X → X

id₁ X = λ x → x
id₂   = λ X x → x
id₃   = λ (X : Set) (x : X) → x
#+END_SRC

#+latex: \end{parallel} \vspace{-1em}

Curly braces make an argument /implicitly inferred/ and so it may be omitted.
E.g., the ~{X ∶ Set} → ⋯~ below lets us make a polymorphic function
since ~X~ can be inferred by inspecting the given arguments. This is akin to
informally writing $\mathsf{id}_X$ versus $\mathsf{id}$.

#+latex: \begin{parallel}
#+BEGIN_SRC agda
id : {X : Set} → X → X
id x = x

sad : ℕ
sad = id₀ ℕ 3

nice : ℕ
nice = id 3
#+END_SRC
#+latex: \columnbreak
#+BEGIN_SRC agda
explicit : ℕ
explicit = id {ℕ} 3

explicit′ : ℕ
explicit′ = id₀ _ 3
#+END_SRC
#+latex: \end{parallel}

#+latex: \vspace{-1em}
Notice that we may provide an implicit argument /explicitly/ by enclosing the value in braces
in its expected position. Values can also be inferred when the ~_~ pattern is supplied in a value position.

Essentially wherever the typechecker can figure out a value ---or a type---, we may use ~_~.
In type declarations, we have a contracted form via ~∀~---which is *not* recommended since it slows down typechecking
and, more importantly, types /document/ our understanding and it's useful to have them explicitly.

In a type, ~(a : A)~ is called a /telescope/ and they can be combined for convenience.

#+latex: \begin{parallel}
#+BEGIN_EXAMPLE agda
   {x : _} {y : _} (z : _) → ⋯
≈  ∀ {x y} z → ⋯
#+END_EXAMPLE
#+latex: \columnbreak
#+BEGIN_EXAMPLE agda
   (a₁ : A) → (a₂ : A) → (b : B) → ⋯
≈  (a₁ a₂ : A) (b : B) → ⋯
#+END_EXAMPLE
#+latex: \end{parallel} \vspace{-1.5em}

* Reads

#+latex: {\color{white}.} \vspace{-1.5em}

  + [[http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf][Dependently Typed Programming in Agda]]
    - Aimed at functional programmers
  + [[https://agda.readthedocs.io/en/v2.6.0.1/getting-started/tutorial-list.html][Agda Meta-Tutorial]] and [[https://wiki.portal.chalmers.se/agda/pmwiki.php][The Agda Wiki]]
  + [[https://mazzo.li/posts/AgdaSort.html][Agda by Example: Sorting]]
    - One of the best introductions to Agda
    # + [[https://people.inf.elte.hu/divip/AgdaTutorial/Index.html][Péter Diviánszky's Agda Tutorial]]
    # - Small digestible portions of Agda in enjoyable HTML
  + [[https://plfa.github.io/][Programming Language Foundations in Agda]]
    - Online, well-organised, and accessible book
  + [[https://alhassy.github.io/PathCat/][Graphs are to categories as lists are to monoids]]
    - A brutal second tutorial
  + [[https://oxij.org/note/BrutalDepTypes/][Brutal {Meta}Introduction to Dependent Types in Agda]]
    - A terse but accessible tutorial
  + [[http://learnyouanagda.liamoc.net/][Learn You An Agda (and achieve enlightenment)]]
    - Enjoyable graphics
  + [[https://github.com/agda][The Agda Github Umbrella]]
    - Some Agda libraries
  + [[https://cs.ru.nl/~wouters/Publications/ThePowerOfPi.pdf][The Power of Pi]]
    - Design patterns for dependently-typed languages, namely Agda
  + [[https://alhassy.github.io/next-700-module-systems/prototype/package-former.html][Making Modules with Meta-Programmed Meta-Primitives]]
    - An Emacs editor extension for Agda
  + [[https://github.com/alhassy/gentle-intro-to-reflection][A gentle introduction to reflection in Agda]] ---Tactics!
    # + [[https://github.com/alhassy/org-agda-mode][org-agda-mode]]
    # - Literate Agda with Org-mode, as used in the source of this document
  + [[http://dx.doi.org/10.1007/11546382_3][Epigram: Practical Programming with Dependent Type]]

    - “If it typechecks, ship it!” ...
    - Maybe not; e.g., ~if null xs then tail xs else xs~
    - /We need a static language capable of expressing the significance of
      particular values in legitimizing some computations rather than others./

  # View from the left
  # Why dependent types matter

* Dependent Datatypes

#+latex: \hspace{-1.3em}
Algebraic datatypes are introduced with a ~data~ declaration, giving the name,
arguments, and type of the datatype as well as the constructors and their types.
Below we define the datatype of lists of a particular length.
The Unicode below is entered with ~\McN, \::~, and ~\to~.

#+BEGIN_SRC agda
data Vec {ℓ : Level} (A : Set ℓ) : ℕ → Set ℓ where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (1 + n)

#+END_SRC

Notice that, for a given type ~A~, the type of ~Vec A~
is ~ℕ → Set~. This means that ~Vec A~ is a family of types
indexed by natural numbers: For each number ~n~, we have a type ~Vec A n~.

One says ~Vec~ is /parametrised/ by ~A~ (and ℓ), and /indexed/ by ~n~.

  They have different roles:
  ~A~ is the type of elements in the vectors,
  whereas ~n~ determines the ‘shape’ ---length--- of the vectors
  and so needs to be more ‘flexible’ than a parameter.

Notice that the indices say that the only way to make an element of ~Vec A 0~ is to
use ~[]~ and the only way to make an element of ~Vec A (1 + n)~ is to use ~_∷_~.
Whence, we can write the following safe function since ~Vec A (1 + n)~ denotes
non-empty lists and so the pattern ~[]~ is impossible.
#+BEGIN_SRC agda

head : {A : Set} {n : ℕ} → Vec A (1 + n) → A
head (x ∷ xs) = x

#+END_SRC

The ℓ argument means the ~Vec~ type operator is /universe polymorphic/: We can make
vectors of, say, numbers but also vectors of types. Levels are essentially natural numbers:
We have ~lzero~ and ~lsuc~ for making them, and ~_⊔_~ for taking the maximum of two levels.
/There is no universe of all universes:/
~Setₙ~ has type ~Setₙ₊₁~ /for any n/, however the /type/ ~(n : Level) → Set n~ is /not/ itself typeable
---i.e., is not in ~Setₗ~ for any ~l~--- and Agda errors saying it is a value of ~Setω~.

Functions are defined by pattern matching, and must cover all possible cases.
Moreover, they must be terminating and so recursive calls must be made on structurally smaller
arguments; e.g., ~xs~ is a sub-term of ~x ∷ xs~ below and catenation is defined recursively on the first argument.
Firstly, we declare a /precedence rule/ so we may omit parenthesis in seemingly ambiguous expressions.
:Hide:
#+BEGIN_SRC agda
module cat where
#+END_SRC
:End:
#+BEGIN_SRC agda
 infixr 40 _++_

 _++_ : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
 []       ++ ys  =  ys
 (x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)
#+END_SRC
Notice that the *type encodes a useful property*: The length of the catenation
is the sum of the lengths of the arguments.

+ Different types can have the same constructor names.

+ Mixifx operators can be written prefix by having all underscores mentioned; e.g.,
  ~x ∷ xs~ is the same as ~_∷_ x xs~.

+ In a function definition, if you don't care about an argument
  and don't want to bother naming it, use ~_~ with whitespace around it.
  This is the “wildcard pattern”.

+ Exercise: Define the Booleans then define the /control flow construct/ ~if_then_else_~.

* The Curry-Howard Correspondence ---“Propositions as Types”

    #+latex: \hspace{-1.3em}
   Programming and proving are two sides of the same coin.

   #+macro: twolines @@latex:\begin{tabular}[l]{@{}l@{}}$1\\$2\end{tabular}@@
   #+macro: hfill @@latex:\hfill@@

   # +latex: \vspace{-1em}
   | *Logic*                  | *Programming*                           | Example Use in Programming                                                  |
   |------------------------+---------------------------------------+-----------------------------------------------------------------------------|
   | proof / proposition    | element / type                        | “$p$ is a proof of $P$” ≈ “$p$ is of type $P$”                              |
   |------------------------+---------------------------------------+-----------------------------------------------------------------------------|
   | $true$                 | singleton type                        | return type of side-effect only methods                                     |
   | $false$                | empty type                            | return type for non-terminating methods                                     |
   |------------------------+---------------------------------------+-----------------------------------------------------------------------------|
   | ⇒                      | function type  {{{hfill}}}   →        | methods with an input and output type                                       |
   | ∧                      | product type   {{{hfill}}}  ×         | simple records of data and methods                                          |
   | ∨                      | sum type       {{{hfill}}} +          | enumerations or tagged unions                                               |
   |------------------------+---------------------------------------+-----------------------------------------------------------------------------|
   | ∀                      | dependent function type {{{hfill}}} Π | return type varies according to input \emph{value}                          |
   | ∃                      | dependent product type {{{hfill}}}  Σ | record fields depend on each other's \emph{values}                          |
   |------------------------+---------------------------------------+-----------------------------------------------------------------------------|
   | natural deduction      | type system                           | ensuring only ``meaningful'' programs                                       |
   | hypothesis             | free variable                         | global variables, closures                                                  |
   |------------------------+---------------------------------------+-----------------------------------------------------------------------------|
   | modus ponens           | function application                  | executing methods on arguments                                              |
   | ⇒-introduction         | λ-abstraction                         | {{{twolines(parameters acting as local variables, to method definitions)}}} |
   |------------------------+---------------------------------------+-----------------------------------------------------------------------------|
   | {{{twolines(induction;, elimination rules)}}} | Structural recursion                  | ~for~-loops are precisely ℕ-induction                                         |

** COMMENT Not an iso … well, a set of three props and three types are definitely in bijection with each other
   # Now,
      | *Not An Isomorphism!* |

   # Why,
   + *Proposition* $P$ is either $true$ or $false$.
   + *Type* $P$ may have more than 2 elements!

** Adding to the table
   Let's augment the table a bit:
   | *Logic*                   | *Programming*                                 |
   | Signature, term         | Syntax; interface, record type, ~class~       |
   | Algebra, Interpretation | Semantics; implementation, instance, object |
   | Free Theory             | Data structure                              |
   | Inference rule          | Algebraic datatype constructor              |
   | Monoid                  | Untyped programming / composition           |
   | Category                | Typed programming / composition             |

   #+latex: \vspace{-1em}

** COMMENT Pure LaTeX form

       #+latex: \def\twolines#1#2{\begin{tabular}[c]{@{}c@{}}#1\\#2\end{tabular}}
    #+latex: \begin{tabular}{cll}
    #+begin_export latex
      \textbf{Logic} & \textbf{Programming} & Example Use in Programming \\ \hline
      % \thead{proof \\ p is a proof of P } & \thead{typing \\ p is of type P} & hi \\ \hline

      $true$ & singleton type
           &{\footnotesize return type of side-effect only methods} \\
                            % similar to C's \texttt{void} \\

     $false$ & empty type
           &{\footnotesize return type for non-terminating methods } \\ \hline

      ⇒ & function type \hfill →
         &{\footnotesize methods with an input and output type } \\

      ∧ & product type \hfill ×
         &{\footnotesize simple records of data and methods } \\

      ∨ & sum type \hfill +
         &{\footnotesize enumerations or tagged unions} \\ \hline

      ∀ & dependent function type \hfill Π
         & {\footnotesize return type varies according to input \emph{value} } \\

      ∃ & dependent product type \hfill Σ
         &{\footnotesize record fields depend on each other's \emph{values} } \\ \hline

      \twolines{natural}{deduction}
      & type system
      &{\footnotesize ensuring only ``meaningful'' programs } \\

      {\footnotesize hypothesis} & free variables
      &{\footnotesize global variables, closures } \\

      ⇒-elimination & function application
      &{\footnotesize executing methods on arguments } \\

      ⇒-introduction
      & λ-abstraction
      & \twolines{\hspace{-0.0em}parameters acting as local variables}
       {\hspace{-0.0em}to method definitions} \\
   #+end_export
   #+latex:\end{tabular}

* Equality

  #+latex: \hspace{-1.3em}
An example of propositions-as-types is a definition of the identity relation
---the least reflexive relation.
# For a type ~A~ and an element ~x~ of ~A~, we define the family of proofs of
# “being equal to $x$” by declaring only one inhabitant at index ~x~.

#+latex: \begin{parallel}[2]
#+BEGIN_SRC agda
data _≡_ {A : Set} : A → A → Set
  where
    refl : {x : A} → x ≡ x
#+END_SRC
#+latex: \columnbreak

This states that ~refl {x}~ is a proof of ~l ≡ r~
whenever ~l~ and ~r~ simplify, by definition chasing only, to ~x~.

:calc:
#+BEGIN_EXAMPLE agda
  p
≡⟨ reason why p ≡ q ⟩
  q
≡⟨ reason why q ≡ r ⟩
  r
∎
#+END_EXAMPLE
:End:

#+latex: \end{parallel} \vspace{-1em}

This definition makes it easy to prove [[https://en.wikipedia.org/wiki/Identity_of_indiscernibles][Leibniz's substitutivity rule]],
“equals for equals”:
#+BEGIN_SRC agda
subst : {A : Set} {P : A → Set} {l r : A}
      → l ≡ r → P l → P r
subst refl it = it
#+END_SRC
Why does this work?
An element of ~l ≡ r~ must be of the form ~refl {x}~ for some
canonical form ~x~; but if ~l~ and ~r~ are both ~x~, then ~P l~ and ~P r~
are the /same type/. Pattern matching on a proof of ~l ≡ r~
gave us information about the rest of the program's type!

** COMMENT and Calculational Proofs
School math classes show calculations as follows.

We can treat these pieces as Agda /mixfix/ identifiers and associate to the right
to obtain: ~p ≡⟨ reason₁ ⟩ (q ≡⟨ reason₂ ⟩ (r ∎))~. We can code this up!

#+latex: \begin{parallel}[2]
#+BEGIN_SRC agda
infixr 5 _≡⟨_⟩_
infix  6 _∎

_∎ : {A : Set} (a : A) → a ≡ a
_ ∎ = refl

_≡⟨_⟩_ : {A : Set} (p {q r} : A)
       → p ≡ q → q ≡ r → p ≡ r
_ ≡⟨ refl ⟩ refl = refl
#+END_SRC
#+latex: \end{parallel} \vspace{-1em}

* spacing break                                                      :ignore:
#+latex: \columnbreak
* Modules ---Namespace Management

  #+latex: \hspace{-1.3em}
Modules are not a first-class construct, yet.

+ Within a module, we may have nested module declarations.
+ All names in a module are public, unless declared ~private~.
#
#+latex: \begin{parallel}[4]
_A Simple Module_
#+latex: \vspace{0.5em}
#+BEGIN_SRC agda
module M where

  𝒩 : Set
  𝒩 = ℕ

  private
    x : ℕ
    x = 3

  y : 𝒩
  y = x + 1
#+END_SRC
#+latex: \columnbreak
_Using It_
#+latex: \vspace{0.5em}
#+BEGIN_SRC agda
use₀ : M.𝒩
use₀ = M.y

use₁ : ℕ
use₁ = y
  where open M
#+END_SRC

#+BEGIN_EXAMPLE agda

open M

use₂ : ℕ
use₂ = y
#+END_EXAMPLE
#+latex: \columnbreak
_Parameterised Modules_
#+latex: \vspace{0.5em}
#+BEGIN_SRC agda
module M′ (x : ℕ)
  where
    y : ℕ
    y = x + 1
#+END_SRC
#+latex: \vfill
_Names are Functions_
#+latex: \vspace{0.2em}
#+BEGIN_SRC agda
exposed : (x : ℕ)
        → ℕ
exposed = M′.y
#+END_SRC
#+latex: \columnbreak

_Using Them_
#+latex: \vspace{0.5em}
#+BEGIN_SRC agda
use′₀ : ℕ
use′₀ = M′.y 3

module M″ = M′ 3

use″ : ℕ
use″ = M″.y

use′₁ : ℕ
use′₁ = y
  where
    open M′ 3
#+END_SRC

#+latex: \end{parallel}

+ Public names may be accessed by qualification or by opening them locally or globally.
+ Modules may be parameterised by arbitrarily many values and types ---but not by other modules.

:Repeated:
Modules may be parameterised by arbitrarily many values and types ---but not by other modules.
#+latex: \begin{parallel}
begin{code}
module M′ (x : ℕ) where
  y : ℕ
  y = x + 1
end{code}
#+latex: \columnbreak
begin{code}
exposed : (x : ℕ) → ℕ
exposed = M′.y
end{code}
#+latex: \end{parallel}
:End:

Modules are essentially implemented as syntactic sugar: Their declarations are treated
as top-level functions that takes the parameters of the module as extra arguments.
In particular, it may appear that module arguments are ‘shared’ among their declarations,
but this is not so.

“Using Them”:
+ This explains how names in parameterised modules are used: They are treated as functions.
+ We may prefer to instantiate some parameters and name the resulting module.
+ However, we can still ~open~ them as usual.

:Repeated:
#+latex: \begin{parallel}[3]
_Names are functions_
begin{code}
use′₀ : ℕ
use′₀ = M′.y 3
end{code}
#+latex: \columnbreak
_Instantiate parameters_
begin{code}
module M″ = M′ 3

use″ : ℕ
use″ = M″.y
end{code}
#+latex: \columnbreak
_Usual ~open~ clauses_
begin{code}
use′₁ : ℕ
use′₁ = 𝕨
  where open M′ 3
             renaming (y to 𝕨)
end{code}
#+latex: \end{parallel}
:End:

** Anonymous Modules and Variables

Anonymous modules correspond to named-then-immediately-opened modules,
and serve to approximate the informal phrase “for any ~A ∶ Set~ and ~a ∶ A~, we have ⋯”.
This is so [[https://people.inf.elte.hu/divip/AIMXXVIII.pdf][common]] that the ~variable~ keyword was introduced and it's [[https://agda.readthedocs.io/en/v2.6.0.1/language/generalization-of-declared-variables.html][clever]]:
Names in ~⋯~ are functions of /only/ those ~variable~-s they actually mention.

#+latex: \begin{parallel}
#+BEGIN_EXAMPLE agda
   module _ {A : Set} {a : A} ⋯
≈
   module T {A : Set} {a : A} ⋯
   open T
#+END_EXAMPLE
#+latex: \columnbreak
#+BEGIN_EXAMPLE agda
variable
  A : Set
  a : A
⋯
#+END_EXAMPLE
#+latex: \end{parallel} \vspace{-1em}

** spacing break :ignore:
   #+latex: \columnbreak
** Module Keywords :ignore:

When opening a module, we can control which names are brought into scope with
the ~using, hiding,~ and ~renaming~ keywords.
| ~open M hiding (𝓃₀; …; 𝓃ₖ)~               | Essentially treat ~𝓃ᵢ~ as private      |
| ~open M using  (𝓃₀; …; 𝓃ₖ)~               | Essentially treat /only/ ~𝓃ᵢ~ as public  |
| ~open M renaming (𝓃₀ to 𝓂₀; …; 𝓃ₖ to 𝓂ₖ)~ | Use names ~𝓂ᵢ~ instead of ~𝓃ᵢ~ |

Splitting a program over several files will improve type checking performance,
since when you are making changes the type checker only has to check the files
that are influenced by the change.
+ ~import X.Y.Z~: Use the definitions of module ~Z~ which lives in file ~./X/Y/Z.agda~.
+ ~open M public~: Treat the contents of ~M~ as if they were public contents of the current module.

* Records

  #+latex: \hspace{-1.3em}
  A record type is declared much like a datatype where the
  fields are indicated by the ~field~ keyword.

  | ~record~ | ≈ | ~module~ +  ~data~ with one constructor |

#+latex: \begin{parallel}
#+BEGIN_SRC agda
record PointedSet : Set₁ where
  constructor MkIt  {- Optional -}
  field
    Carrier : Set
    point   : Carrier

  {- It's like a module,
  we can add derived definitions -}
  blind : {A : Set} → A → Carrier
  blind = λ a → point
#+END_SRC
#+latex: \columnbreak
#+BEGIN_SRC agda
ex₀ : PointedSet
ex₀ = record {Carrier = ℕ; point = 3}

ex₁ : PointedSet
ex₁ = MkIt ℕ 3

open PointedSet

ex₂ : PointedSet
Carrier ex₂ = ℕ
point   ex₂ = 3
#+END_SRC
#+latex: \end{parallel} \vspace{-1em}

Start with ~ex₂ = ?~, then in the hole enter ~C-c C-c RET~
to obtain the /co-pattern/ setup.
Two tuples are the same when they have the same components,
likewise a record is defined by its projections, whence /co-patterns/.
If you're using many local definitions, you likely want to use co-patterns!

To allow projection of the fields from a record, each record type comes
with a module of the same name. This module is parameterised by an element
of the record type and contains projection functions for the fields.

#+latex: \begin{parallel}
#+BEGIN_SRC agda
use⁰ : ℕ
use⁰ = PointedSet.point ex₀
#+END_SRC
#+BEGIN_EXAMPLE agda

use¹ : ℕ
use¹ = point where open PointedSet ex₀

#+END_EXAMPLE
# Spec since this clashes with the previous open.
#+BEGIN_SRC agda
open PointedSet

use² : ℕ
use² = blind ex₀ true
#+END_SRC
#+latex: \columnbreak

You can even pattern match on records
\\
---they're just ~data~ after all!
#+latex: \vspace{1em}
#+BEGIN_SRC agda
use³ : (P : PointedSet) → Carrier P
use³ record {Carrier = C; point = x}
  = x

use⁴ : (P : PointedSet) → Carrier P
use⁴ (MkIt C x)
  = x
#+END_SRC
#+latex: \end{parallel} \vspace{-1em}

* Interacting with the real world ---Compilation, Haskell, and IO
:PROPERTIES:
:header-args: :tangle "CompilingAgda.agda" :comments org
:CUSTOM_ID: agda-interacting-with-the-real-world
:END:

# C-c C-v C-t tangles the following code into CompilingAgda.agda.
# Then we may compile the result using:
# (shell-command "NAME=CompilingAgda; time agda --compile $NAME.agda; ./$NAME")
#
# Btw: (find-file "./MAlonzo/Code/CompilingAgda.hs")

#+latex: {\color{white}.} \vspace{-1em}
#+begin_quote org
/Let's demonstrate how we can reach into Haskell, thereby subverting Agda!/
#+end_quote

An Agda program module containing a ~main~ function is compiled into a standalone executable
with ~agda --compile myfile.agda~. If the module has no main file, use the flag ~--no-main~.
If you only want the resulting Haskell, not necessarily an executable program, then use the flag
~--ghc-dont-call-ghc~.

The type of ~main~ should be ~Agda.Builtin.IO.IO A~, for some ~A~;
this is just a proxy to Haskell's ~IO~.
We may ~open import IO.Primitive~ to get /this/ ~IO~, but
this one works with costrings, which are a bit awkward.
Instead, we use the standard library's wrapper type, also named ~IO~.
Then we use ~run~ to move from ~IO~ to ~Primitive.IO~; conversely one uses ~lift~.

#+latex: \begin{minipage}[c]{0.55\linewidth}
#+latex: \begin{tiny}
#+BEGIN_SRC agda
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
#+END_SRC
#+latex: \end{tiny}
#+latex: \end{minipage} % no space if you would like to put them side by side
#+latex: \begin{minipage}[c]{0.5\linewidth}
#+begin_quote org
/Agda has *no* primitives for side-effects, instead it allows arbitrary/
/Haskell functions to be imported as axioms, whose definitions are only/
/used at run-time./
#+end_quote
#+latex: \end{minipage}

Agda lets us use “do”-notation as in Haskell.
To do so, methods named ~_>>_~ and ~_>>=_~ need to be in scope ---that is all.
The type of ~IO._>>_~ takes two “lazy” IO actions and yield a non-lazy IO action.
The one below is a homogeneously typed version.

#+BEGIN_SRC agda
infixr 1 _>>=_ _>>_

_>>=_ : ∀ {ℓ} {α β : Set ℓ} → IO α → (α → IO β) → IO β
this >>= f = ♯ this IO.>>= λ x → ♯ f x

_>>_ : ∀{ℓ} {α β : Set ℓ} → IO α → IO β → IO β
x >> y = x >>= const y
#+END_SRC

Oddly, Agda's standard library comes with ~readFile~ and
~writeFile~, but the symmetry ends there since it provides ~putStrLn~
but not [[https://hackage.haskell.org/package/base-4.12.0.0/docs/Prelude.html#v:getLine][~getLine~]]. Mimicking the ~IO.Primitive~ module, we define /two/
versions ourselves as proxies for Haskell's ~getLine~ ---the second one
below is bounded by 100 characters, whereas the first is not.

#+BEGIN_SRC agda
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
#+END_SRC
We obtain ~MAlonzo~ strings, then convert those to colists, then
eventually lift those to the wrapper ~IO~ type.

Let's also give ourselves Haskell's ~read~ method.
#+BEGIN_SRC agda
postulate readInt  : L.List Char → ℕ
{-# COMPILE GHC readInt = \x -> read x :: Integer  #-}
#+END_SRC

Now we write our ~main~ method.
#+BEGIN_SRC agda
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
#+END_SRC
For example, the $12^{th}$ [[https://en.wikipedia.org/wiki/Triangular_number][triangle number]] is $\sum_{i=0}^{12} i = 78$.
Interestingly, when an integer parse fails, the program just crashes!
Super cool dangerous stuff!

Calling this file ~CompilingAgda.agda~, we may compile then run it with:
#+BEGIN_SRC shell :tangle no
NAME=CompilingAgda; time agda --compile $NAME.agda; ./$NAME
#+END_SRC

The very first time you compile may take ∼80 seconds since some prerequisites need to be compiled,
but future compilations are within ∼10 seconds.

The generated Haskell source lives under the newly created MAlonzo directory; namely
~./MAlonzo/Code/CompilingAgda.hs~. Here's some fun: Write a parameterised module with multiple declarations,
then use those in your ~main~; inspect the generated Haskell to see that the module is thrown away in-preference
to top-level functions ---as mentioned earlier.

# *Debugging*
- When compiling you may see an error ~Could not find module ‘Numeric.IEEE’~.
- Simply open a terminal and install the necessary Haskell library:
  #+BEGIN_SRC shell :tangle no
cabal install ieee754
#+END_SRC

* Absurd Patterns

#+latex: \hspace{-1.3em}
When there are no possible constructor patterns, we may match on the pattern ~()~
and provide no right hand side ---since there is no way anyone could provide an argument
to the function.

For example, here we define the datatype family of numbers smaller than a given natural number:
~fzero~ is smaller than ~suc n~ for any ~n~, and if ~i~ is smaller than ~n~ then ~fsuc i~ is smaller
than ~suc n~.

#+latex: \begin{parallel}
#+BEGIN_SRC agda
{- Fin n  ≅  numbers i with i < n -}
data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc  : {n : ℕ}
        → Fin n → Fin (suc n)
#+END_SRC
#+latex: \columnbreak

For each $n$, the type ~Fin n~ contains $n$ elements;
e.g., ~Fin 2~ has elements ~fsuc fzero~ and ~fzero~,
whereas ~Fin 0~ has no elements at all.

#+latex: \end{parallel} \vspace{-1em}

Using this type, we can write a safe indexing function that never “goes out of bounds”.
#+BEGIN_SRC agda

_‼_ : {A : Set} {n : ℕ} → Vec A n → Fin n → A
[] ‼ ()
(x ∷ xs) ‼ fzero  = x
(x ∷ xs) ‼ fsuc i = xs ‼ i
#+END_SRC

When we are given the empty list, ~[]~, then ~n~ is necessarily ~0~,
but there is no way to make an element of type ~Fin 0~ and so we have the absurd pattern.
That is, since the empty type ~Fin 0~ has no elements there is nothing to define
---we have a definition by /no cases/.

Logically [[https://en.wikipedia.org/wiki/Principle_of_explosion][“anything follows from false”]] becomes the following program:
#+BEGIN_SRC agda
data False : Set where

magic : {Anything-you-want : Set} → False → Anything-you-want
magic ()
#+END_SRC

Starting with ~magic x = ?~ then casing on ~x~ yields the program above
since there is no way to make an element of ~False~
---we needn't bother with a result(ing right side), since there's no way to make
an element of an empty type.

** Preconditions as proof-object arguments

Sometimes it is not easy to capture a desired precondition in the types, and
an alternative is to use the following ~isTrue~-approach of passing around
explicit proof objects.

#+latex: \begin{parallel}
#+BEGIN_SRC agda
{- An empty record has only
   one value: record {} -}
record True : Set where

isTrue : Bool → Set
isTrue true  = True
isTrue false = False
#+END_SRC
#+latex: \columnbreak
#+BEGIN_SRC agda
_<₀_ : ℕ → ℕ → Bool
_ <₀ zero      = false
zero <₀ suc y  = true
suc x <₀ suc y = x <₀ y
#+END_SRC
#+latex: \end{parallel} \vspace{-1em}

#+BEGIN_SRC agda
find : {A : Set} (xs : List A) (i : ℕ) → isTrue (i <₀ length xs) → A
find [] i ()
find (x ∷ xs) zero pf    = x
find (x ∷ xs) (suc i) pf = find xs i pf

head′ : {A : Set} (xs : List A) → isTrue (0 <₀ length xs) → A
head′ [] ()
head′ (x ∷ xs) _ = x
#+END_SRC

Unlike the ~_‼_~ definition, rather than there being no index into the empty list,
there is no proof that a natural number ~i~ is smaller than 0.

* Mechanically Moving from ~Bool~ to ~Set~ ---Avoiding “Boolean Blindness”

  #+latex: \hspace{-1.3em}
In Agda we can represent a proposition as a type whose elements denote proofs
of that proposition. Why would you want this? Recall how awkward it was to request
an index be “in bounds” in the ~find~ method, but it's much easier to encode this
using ~Fin~ ---likewise, ~head′~ obtains a more elegant type when the non-empty precondition
is part of the datatype definition, as in ~head~.

Here is a simple recipe to go from Boolean functions to inductive datatype families.
0. Write the Boolean function.
1. Throw away all the cases with right side ~false~.
2. Every case that has right side ~true~ corresponds to a new nullary constructor.
3. Every case that has $n$ recursive calls corresponds to an ~n~-ary constructor.

Following these steps for ~_<₀_~, from the left side of the page, gives us:

#+BEGIN_SRC agda
data _<₁_ : ℕ → ℕ → Set where
  z< : {y : ℕ} → zero <₁ y
  s< : {x y : ℕ} → x <₁ y → suc x <₁ suc y
#+END_SRC

To convince yourself you did this correctly, you can prove “soundness”
---constructed values correspond to Boolean-true statements---
and “completeness” ---true things correspond to terms formed from constructors.
The former is ensured by the second step in our recipe!

#+BEGIN_SRC agda
completeness : {x y : ℕ} → isTrue (x <₀ y) → x <₁ y
completeness {x}     {zero}  ()
completeness {zero}  {suc y} p = z<
completeness {suc x} {suc y} p = s< (completeness p)
#+END_SRC

We began with ~completeness {x} {y} p = ?~, then we wanted to case on ~p~
but that requires evaluating ~x <₀ y~ which requires we know the shapes of ~x~ and ~y~.
/The shape of proofs usually mimics the shape of definitions they use/; e.g., ~_<₀_~ here.

* COMMENT Other things to consider adding
  + [ ] instances
  + [ ] subst
** Todo COMMENT Syntax; ≡ combinators

   -- Z-notation for sums
 open import Data.Product using (Σ ; proj₁ ; proj₂ ; _×_ ; _,_)
 Σ∶• : {a b : Level} (A : Set a) (B : A → Set b) → Set (a ⊍ b)
 Σ∶• = Σ
 infix -666 Σ∶•
 syntax Σ∶• A (λ x → B) = Σ x ∶ A • B

 -- Equalities
 open import Relation.Binary.PropositionalEquality using (_≗_ ; _≡_)
   renaming (sym to ≡-sym ; refl to ≡-refl ; trans to _⟨≡≡⟩_
            ; cong to ≡-cong ; cong₂ to ≡-cong₂
            ; subst to ≡-subst ; subst₂ to ≡-subst₂ ; setoid to ≡-setoid)
 Notice that we renamed transitivity to be an infix combinator.

 Let us make equational-style proofs available for any type.

 module _ {i} {S : Set i} where
     open import Relation.Binary.EqReasoning (≡-setoid S) public
 We intend our proofs to be sequences of formulae interleaved with justifications for how the formulae are related. At times, the justifications are by definition and so may be omitted, but we may want to mention them for presentational –pedagogical?– purposes. Hence, we introduce the combinator notation lhs ≡⟨" by definition of something "⟩′ rhs.

 open import Agda.Builtin.String

 defn-chasing : ∀ {i} {A : Set i} (x : A) → String → A → A
 defn-chasing x reason supposedly-x-again = supposedly-x-again

 syntax defn-chasing x reason xish = x ≡⟨ reason ⟩′ xish

 infixl 3 defn-chasing

 While we’re making synonyms for readability, let’s make another:

 _even-under_ : ∀ {a b} {A : Set a} {B : Set b} {x y} → x ≡ y → (f : A → B) → f x ≡ f y
 _even-under_ = λ eq f → ≡-cong f eq
 Example usage would be to prove mor G (mor F Id) ≡ mor G Id directly by ≡-cong (mor G) (id F) which can be written more clearly as functor F preserves-identities even-under (mor G), while longer it is also much clearer and easier to read and understand –self-documenting in some sense.

** COMMENT With Construct

   When pattern matching on an expression in a dependently-typed language,
   you not only learn about the shape of the expression, but you can also learn things about
   other expressions. E.g., matching on an expression of type ~Vec A n~ reveals information
   about the shape of ~n~.

   Whereas Haskell provides a ~case~ construct, Agda has ~with~ to permit pattern matching
   on intermediate computations. If we want to pattern match on expressions ~e₁, …, eₙ~ in
   the definition of a function ~f~, we effectively add $n$ new arguments which can then be matched on
   in the usual fashion:

   #+BEGIN_EXAMPLE agda
  f : T₁ → ⋯ → Tₘ → T
  f x₁ … xₘ with e₁ | ⋯ | eₙ
  f x₁ … xₘ | y₁ | ⋯ yₙ = ?
   #+END_EXAMPLE

   Now you have access to new ‘arguments’ ~yᵢ~ and may pattern match on them as you would on the
   normal arguments ~xᵢ~. When matching on the ~eᵢ~ doesn't tell us anything interesting about
   the arguments ~xᵢ~, we may contract ~f x₁ ⋯ xₘ~ in subsequent lines with just the literal ~⋯~,
   inputted by ~\ldots~.

   Expressions abstracted using ~with~ are abstracted over the entire context ---essentialy acting
   as arguments. That is, if expression ~eᵢ~ occurs in the type of an argument, ~Tⱼ~, or in the result
   type, ~T~, this occurance of ~eᵢ~ will be replaced by ~yᵢ~.

   # TODO: Give an example by writing a decider via ~Dec~?

   Unfortunately, the cost of such new ‘arguments’ is that to /prove/ anything about ~f~, one
   will usually need to make the /same/ ~with~ clauses so that ~f~ can reduce to a value.
   Agda notates this in goals by showing ~⋯(f x | e)⋯~ to indicate casing along ~e~ is necessary
   for the computation of ~f x~ to reduce.

   *Instead, it's preferable to define helper functions and prove properties about those!*

** COMMENT Dot Patterns

   Patterns provide new variable names which must be unique.
   However, sometimes casing on one pattern has its variables necessarily /identical/ to others
   and this is noted by prefixing them with a dot.

 #+BEGIN_SRC agda
map₀ : {A B : Set} (n : ℕ) → (A → B) → Vec A n → Vec B n
map₀ .0 f []             = []
map₀ .(suc _) f (x ∷ xs) = f x ∷ map₀ _ f xs
 #+END_SRC

 When we pattern match, we learn the length of a list:
 Starting with ~map₀ n f xs = ?~ then refining the hole with ~C-c C-e xs~
 cases on ~xs~ /then/ it knowns the lengths and placed those dots above
 to denote /dervied information/. Then we are given two new holes, and ~C-c C-a~
 filled in both of them. This is an example of programming as a dialogue between user and machine.

 Unlike Haskell, the types here document the property that ~map~ preserves the length of lists.

** Why Mechanisation ---Benefits of the formal approach

   + Unicode and mixfix operators ⇒ Mechanisation is readable and not significantly
     more effort than a conventional presentation in LaTeX.

   + Agda as a type checker for doing mathematics —manipulating symbols according
     to specified rules.

       Mechanised mathematical notation
     ⇒ *Confidence in results!*
     ⇒ Dispel silly conjectures/errors!

   + Agda enables a natural treatment of theories and their direct use as modules of executable programs.

   + Formalisations can be used both for theoretical reasoning and for executable implementations

   + Finally, formal proofs are fool-proof! *No “an exercise to the reader”!*

* COMMENT What if I want ~N~ columns? Or non-landscape? Or multiple formats?

Press ~C-c C-c~ on the following incantation to produce a single column portrait of the cheat sheet.
#+name: make-portrait
#+BEGIN_SRC emacs-lisp :results none
(with-temp-buffer
    (insert
    "#+EXPORT_FILE_NAME: CheatSheet_Portrait.pdf
     ,#+LATEX_HEADER_EXTRA: \\landscapefalse \\def\\cheatsheetcols{1}
     ,#+INCLUDE: CheatSheet.lagda
    ")

    (let ((org-export-use-babel nil))
      (org-mode)
      (org-latex-export-to-pdf)
      )
)
#+END_SRC

* COMMENT Making ~README.org~

  Evaluate the following source block with ~C-c C-c~
  to produce a ~README~ file.

#+NAME: make-readme
#+BEGIN_SRC emacs-lisp
(with-temp-buffer
    (insert
    "#+EXPORT_FILE_NAME: README.org
     # HTML: <h1> Easily Making CheatSheets with Org-mode </h1>
     ,#+OPTIONS: toc:nil d:nil
     # Toc is displayed below at a strategic position.

     {{{blurb}}}

    ,*The listing sheet, as PDF, can be found
     [[file:CheatSheet.pdf][here]]*,
     or as a [[file:CheatSheet_Portrait.pdf][single column portrait]],
     while below is an unruly html rendition.

     # Markdown links: [title](target)

     This reference sheet is built from a
     [[https://github.com/alhassy/CheatSheet][CheatSheets with Org-mode]]
     system. This is a /literate/ Agda file written in Org-mode using
     [[https://github.com/alhassy/org-agda-mode][org-agda-mode]].

     ,#+TOC: headlines 2
     ,#+INCLUDE: CheatSheet.lagda
    ")

    ;; No code execution on export
    ;; ⟪ For a particular block, we use “:eval never-export” ⟫
    ;;
    (let ((org-export-use-babel nil))
      (org-mode)
      ; (org-md-export-to-markdown)
      ; (package-install 'toc-org)
      (toc-org-mode)
      (toc-org-insert-toc)
      ; (setq org-toc-noexport-regexp ".*:ignore:.*") MA: Doesn't work.
      ; (delete "TOC" org-export-exclude-tags)
      ; (pop org-export-exclude-tags)
      (org-org-export-to-org)
      ; (add-to-list 'org-export-exclude-tags "TOC")
      )
)
#+END_SRC

Note that the ~blurb~ macro is defined by the user, to provide a terse description of the project.
   - Think the one-line statement at the top of a github repo page.

#    The ~d:nil~ ensures the ‘drawer’ ~:Hide: ⋯ :End:~ is not exported; it's there for me
#    as a reminder.

* COMMENT footer

The agda and literate.el come from:
https://github.com/alhassy/agda-mode

*Warning*
➪ C-c C-v C-t, org-babel-tangle, works as expected however Agda does not allow two files of the
  shape ~X.lagda~ and ~X.agda~, and so tangled code should ideally be relocated or not even bothered
  with in-favour of using org-mode with agda.
➪ agda does not respect Org-mode's COMMENT mechanism. but acknowledges EXAMPLEs in-place of SRCs.

Need to ensure org-indent-mode is off when going to agda.
(setq org-src-preserve-indentation 't)

# Local Variables:
# eval: (setq org-src-preserve-indentation 't)
# eval: (load-file "~/org-agda-mode/literate.el")
# End:
