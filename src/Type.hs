module Type where

import Data.Text.Prettyprint.Doc

type IsRec = Bool
type Name = String

recursive, nonRecursive :: IsRec
recursive    = True
nonRecursive = False

bindersOf = map fst
rhssOf = map snd

type Alter a = (Int, [a], Expr a)
type CoreAlt = Alter Name
corealt :: Int -> [Name] -> CoreExpr -> CoreAlt
corealt tag vars expr = (tag,vars,expr)

type Defn a = (a, Expr a)
type CoreDefn = (Name, Expr Name)
coredefn :: Name -> CoreExpr -> CoreDefn
coredefn ident meaning = (ident, meaning)

data Expr a
  = EVar Name
  | ENum Int
  | EConstr Int Int
  | EAp (Expr a) (Expr a)
  | ELet
       IsRec
       [Defn a]
       (Expr a)
  | ECase
       (Expr a)
       [Alter a]
  | ELam [a] (Expr a) deriving (Show,Eq)

type CoreExpr = Expr Name

isAtomicExpr :: Expr a -> Bool
isAtomicExpr (EVar _) = True
isAtomicExpr (ENum _) = True
isAtomicExpr _ = False

type Program a = [ScDefn a]
type CoreProgram = Program Name

type ScDefn a = (Name, [a], Expr a)
type CoreScDefn = ScDefn Name

-- Utilities
-- (# of objects in the heap, unused addresses, [(address, object)])
type Heap a = (Int, [Int], [(Int, a)])
type Addr = Int

hInitial :: Heap a
-- (0 objects in heap, address 1 .. infty, no allocations
hInitial = (0, [1..], [])

-- allocate n to heap, return new heap and address where n is allocated
hAlloc :: Heap a -> a -> (Heap a, Addr)
hAlloc (size, (next:free), cts) n = ((size+1, free, (next,n): cts), next)

hUpdate :: Heap a -> Addr -> a -> Heap a
hUpdate (size, free, cts) a n = (size, free, (a,n) : remove cts a)

hLookup :: Heap a -> Addr -> a
hLookup (size, free, cts) a = aLookup cts a (error $ "can't find node " ++ show a ++ " in heap")

hFree :: Heap a -> Addr -> Heap a
hFree (size, free, cts) a = (size-1, a:free, remove cts a)

remove :: [(Int, a)] -> Int -> [(Int, a)]
remove [] a = error
  (" Attempt to update or free non existent address #" ++ show a)
remove ((a',n):cts) a | a == a' = cts
                      | a /= a' = (a',n) : remove cts a

type Assoc a b = [(a,b)] -- association list, associates keys to values
aLookup [] k' def = def
aLookup ((k,v):bs) k' def | k == k' = v
                          | k /= k' = aLookup bs k' def
aDomain = map fst
aRange = map snd
aEmpty = []

-- this should be a recursion scheme
mkApChain :: [CoreExpr] -> CoreExpr
mkApChain (expr:rest@(_:_)) = EAp expr $ mkApChain rest
mkApChain [x] = x
mkApChain [] = error "empty app chain"

-- Pretty printing

ppDefn (name, value) = pretty name <+> pretty "=" <+> ppExpr value

ppExpr :: CoreExpr -> Doc ann
ppExpr (EVar x) = pretty x
ppExpr (ENum x) = pretty x
ppExpr (EConstr x y) = pretty "Pack" <> braces (
  pretty x <> comma <> pretty y)
ppExpr (EAp x y) = ppExpr x <+> ppExpr y
ppExpr (ELet False definitions result) = pretty "let" <+>
  encloseSep langle rangle (semi <> space) (map ppDefn definitions) <+> ppExpr result
ppExpr (ELet True definitions result) = pretty "letrec" <+>
  encloseSep langle rangle (semi <> space) (map ppDefn definitions) <+> ppExpr result
-- ppExpr (ECase match alts) = encloseSep
--  (pretty "case" <+> ppExpr match <+> pretty "of ") semi
--  (semi) (map ppAlt alts)
ppExpr (ECase match alts) = pretty "case" <+> ppExpr match <+> pretty "of "
  <> vsep (map (\x -> ppAlt x <> semi) alts)

ppAlt (tag,args,expr) = (pretty "<" <> pretty tag <> pretty ">") <+>
  encloseSep mempty mempty space (map pretty args) <+> pretty "->" <+>
  ppExpr expr
