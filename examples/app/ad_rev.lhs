```include
other/header.md
```

concat: Playing with reverse mode automatic differentiation (AD)
===

This [literate Haskell](https://wiki.haskell.org/Literate_programming) document provides an example of using the _reverse mode AD_ machinery available in _concat_.

Original author: [David Banas](mailto:capn.freako@gmail.com)  
Original date:   November 30, 2018

Copyright &copy; 2018 David Banas; all rights reserved World wide.

Contents
---

- [Code](#code)
- [Output](#output)

code
---

[ghc options](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/flags.html#flag-reference)
---

\begin{code}
{-# OPTIONS_GHC -cpp #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
\end{code}

[pragmas](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/lang.html)
---

\begin{code}
-- doctest doesn't look at the cabal file, so you need pragmas here
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
\end{code}

[libraries](https://www.stackage.org/)
---

- [optparse-generic](https://www.stackage.org/package/optparse-generic)
- [vector-sized](https://www.stackage.org/package/vector-sized)
- [finite-typelits](https://www.stackage.org/package/finite-typelits)
- [text](https://www.stackage.org/package/text)

\begin{code}
import Options.Generic

import Data.Maybe

import ConCat.AD
\end{code}

- [hoogle](https://www.stackage.org/package/hoogle)

\begin{code}
-- #define DEBUG

{----------------------------------------------------------------------
  Constant definitions.
----------------------------------------------------------------------}

mdFilename = "out/ad_rev.md"

{----------------------------------------------------------------------
  Command line options defintions.
----------------------------------------------------------------------}

data Opts w = Opts
    { dummy :: w ::: Maybe Bool <?>
        "Not used."
    }
    deriving (Generic)

instance ParseRecord (Opts Wrapped)

{----------------------------------------------------------------------
  main()
----------------------------------------------------------------------}

main :: IO ()
main = do
  -- Process command line options.
  o :: Opts Unwrapped <-
    unwrapRecord "A toy for playing w/ concat-based reverse mode automatic differentiation."
  let unUsed = fromMaybe False (dummy o)

  -- Construct a simple, fully-connected, neural network.
  
  -- Print test message.
  writeFile  mdFilename "\n### Test message:\n\n"
  appendFile mdFilename "Hello, World!\n"
  putStrLn "Program complete."

  -- Debug.
#ifdef DEBUG
  {-
  appendFile mdFilename "\n## Debugging Information:\n\n"
  -}
#endif

\end{code}

output
---

```include
out/ad_rev.md
```

***

<div class="footer">
Powered by [haskell](https://haskell-lang.org/), [stack](https://docs.haskellstack.org/en/stable/README/) and [pandoc](http://pandoc.org/).
</div>

