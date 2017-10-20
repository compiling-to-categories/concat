-- -*-Haskell-*-

#define OPINLINE INLINE [0]
-- #define OPINLINE INLINE CONLIKE [3]
-- #define OPINLINE NOINLINE

#define Op(nm,ty) \
{- | C.nm without the eager inlining -}; \
nm :: ty; \
nm = C.nm ;\
{-# OPINLINE nm #-}

#define OpRule0(nm) {-# RULES "reveal op0" \
  reveal nm = C.nm #-}
#define OpRule1(nm) {-# RULES "reveal op1" forall a1. \
  reveal (nm a1) = C.nm (reveal a1) #-}
#define OpRule2(nm) {-# RULES "reveal op2" forall a1 a2. \
  reveal (nm a1 a2) = C.nm (reveal a1) (reveal a2) #-}

#define IpRule0(nm) {-# RULES "reveal ip0" \
  reveal (nm) = (C.nm) #-}
#define IpRule1(nm) {-# RULES "reveal ip1" forall a1. \
  reveal ((nm) a1) = (C.nm) (reveal a1) #-}
#define IpRule2(nm) {-# RULES "reveal ip2" forall a1 a2. \
  reveal ((nm) a1 a2) = (C.nm) (reveal a1) (reveal a2) #-}

#define Op0(nm,ty) Op(nm,ty); OpRule0(nm)
#define Op1(nm,ty) Op(nm,ty); OpRule1(nm)
#define Op2(nm,ty) Op(nm,ty); OpRule2(nm)

#define Ip(nm,ty) \
{- | (C.nm) without the eager inlining -}; \
(nm) :: ty; \
(nm) = (C.nm) ;\
{-# OPINLINE (nm) #-}

#define Ip1(nm,ty) Ip(nm,ty); IpRule1(nm)
#define Ip2(nm,ty) Ip(nm,ty); IpRule2(nm)

-- I use semicolons and the {- | ... -} style Haddock comment because CPP macros
-- generate a single line. I want to inject single quotes around the C.foo and
-- (C.op) names to form Haddock links, but CPP interprets them as preventing
-- macro argument insertion.

-- Can I get the operation names (nm) into the rule names?

{--------------------------------------------------------------------
    Capture class ops
--------------------------------------------------------------------}

-- Basic
#define Catify(op,meth) {-# RULES "catify" [~0] op = meth #-}
-- Same name as in Prelude
#define CatifyP(nm)  Catify(P.nm,nm)
#define CatifyPI(op) Catify((P.op),(op))
-- Curried
#define CatifyC(op,meth) Catify(op,curry (meth))
