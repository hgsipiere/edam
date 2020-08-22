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

type ScDefn a = (Name, [a], Expr a)
type CoreScDefn = ScDefn Name

type Program a = [ScDefn a]
type CoreProgram = Program Name
-- G Machine types

data Instruction
 = Unwind
 | Pushglobal Name
 | Pushint Int
 | Push Int
 | MkAp
 | Slide Int deriving (Show, Eq)

data Node
 = NNum Int
 | NAp Addr Addr
 | NGlobal Int GmCode

getArg :: Node -> Addr
getArg (NAp a1 a2) = a2

type GmCode = [Instruction]
type GmStack = [Addr]
type GmHeap = Heap Node
type GmGlobals = Assoc Name Addr
type GmStats = Int

type GmState =
  (GmCode,    -- current instruction list
   GmStack,   -- current stack
   GmHeap,    -- heap of nodes
   GmGlobals, -- global addresses in heap
   GmStats)   -- statistics

getCode :: GmState -> GmCode
getCode (i, _, _, _, _) = i

putCode :: GmCode -> GmState -> GmState
putCode i' (i, stack, heap, globals, stats) = (i', stack, heap, globals, stats)

getStack :: GmState -> GmStack
getStack (_, stack, _, _, _) = stack

putStack :: GmStack -> GmState -> GmState
putStack stack' (i, stack, heap, globals, stats) = (i, stack', heap, globals, stats)

getHeap :: GmState -> GmHeap
getHeap (_, _, heap, _, _) = heap

putHeap :: GmHeap -> GmState -> GmState
putHeap heap' (i, stack, heap, globals, stats) = (i, stack, heap', globals, stats)

getGlobals :: GmState -> GmGlobals
getGlobals (_, _, _, globals, _) = globals

getStats :: GmState -> GmStats
getStats (_, _, _, _, stats) = stats

putStats :: GmStats -> GmState -> GmState
putStats stats' (i, stack, heap, globals, stats) = (i, stack, heap, globals, stats')

statInitial :: Int
statInitial = 0
statIncSteps, statGetSteps :: Int -> Int
statIncSteps s = s+1
statGetSteps s = s

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
-- def is practically only used to call error
aLookup [] k' def = def
aLookup ((k,v):bs) k' def | k == k' = v
                          | k /= k' = aLookup bs k' def
aDomain = map fst
aRange = map snd
aEmpty = []

-- this should be a recursion scheme, and work with non empty lists
mkApChain :: [CoreExpr] -> CoreExpr
mkApChain (expr:rest@(_:_)) = EAp expr $ mkApChain rest
mkApChain [x] = x
mkApChain [] = error "empty app chain"

-- Pretty printing, this is in type so that the Show does not
-- have to be either defined via cyclical imports with a pp module
-- or that the show is defined a more 'mixing' module

-- Format core expressions as document
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
ppExpr (ECase match alts) = pretty "case" <+> ppExpr match <+> pretty "of "
  <> vsep (map (\x -> ppAlt x <> semi) alts)
ppAlt (tag,args,expr) = (pretty "<" <> pretty tag <> pretty ">") <+>
  encloseSep mempty mempty space (map pretty args) <+> pretty "->" <+>
  ppExpr expr

-- Format state machine types as document
ppStats :: GmState -> Doc ann
ppStats s = pretty "Steps taken = " <> (pretty.statGetSteps.getStats $ s)

ppNode :: GmState -> Addr -> Node -> Doc ann
ppNode _ _ (NNum n) = pretty n
ppNode s a (NGlobal n g) = pretty "Global " <> pretty v
  where v = head [n | (n,b) <- getGlobals s, a == b]
  -- look through the globals by address to find the correct one
ppNode s a (NAp a1 a2) = pretty "Ap" <+> pretty a1 <+> pretty a2

ppStackItem :: GmState -> Addr -> Doc ann
ppStackItem s a = pretty a <> pretty ": " <> ppNode s a (hLookup (getHeap s) a)

ppStack :: GmState -> Doc ann
-- print the stack items by printing (partially applied to the stack)
-- by the addresses looked up in the heap
ppStack s = pretty " Stack:[" <> nest 2 (vsep (map (ppStackItem s) reversedStack)) <> pretty "]"
  where reversedStack = reverse $ getStack s

ppInstruction :: Instruction -> Doc ann
ppInstruction Unwind = pretty "Unwind"
ppInstruction (Pushglobal f) = pretty "Pushglobal" <+> pretty f
ppInstruction (Push n) = pretty "Push" <+> pretty n
ppInstruction (Pushint n) = pretty "Pushint" <+> pretty n
ppInstruction MkAp = pretty "MkAp"
ppInstruction (Slide n) = pretty "Slide" <+> pretty n

ppInstructions :: GmCode -> Doc ann
ppInstructions is = pretty "  Code:{" <> (nest 2 $ vsep (map ppInstruction is)) <> pretty "}" <> hardline

ppSC :: GmState -> (Name, Addr) -> Doc ann
ppSC s (name, addr) = pretty "Code for " <> pretty name <> hardline <> ppInstructions code <> hardline
  where (NGlobal name code) = hLookup (getHeap s) addr

ppState :: GmState -> Doc ann
ppState s = ppStack s <> hardline <> ppInstructions (getCode s) <> hardline

ppResults :: [GmState] -> Doc ann
ppResults states@(s:ss) =
  pretty "Supercombinator definitions" <> hardline <>
  vsep (map (ppSC s) (getGlobals s)) <> hardline <> hardline <>
 pretty "State transitions" <> hardline <> hardline <>
 vsep (map ppState states) <> hardline <> hardline <>
 ppStats (last states)
