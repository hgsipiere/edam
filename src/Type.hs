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

to_main :: CoreExpr -> CoreProgram
to_main expr = [("main", [], expr)]
-- G Machine types

data Instr
 = Unwind
 | Pushglobal Name
 | Pushint Int
 | Push Int
 | MkAp
 | Update Int
 | Pop Int
 | Slide Int
 | Alloc Int
 | Eval
 | Add | Sub | Mul | Div | Mod | Neg
 | Eq | Neq | Lt | Le | Gt | Ge
 | Cond GmCode GmCode
 deriving (Show, Eq)

data Node
 = NNum Int
 | NAp Addr Addr
 | NGlobal Int GmCode
 | NInd Addr deriving (Eq, Show)

getArg :: Node -> Addr
getArg (NAp a1 a2) = a2

type GmCode = [Instr]
type GmStack = [Addr]
type GmDumpItem = (GmCode, GmStack)
type GmDump = [GmDumpItem]
type GmHeap = Heap Node
type GmGlobal = (Name,Addr)
type GmGlobals = Assoc Name Addr
type GmStats = Int

data GmState = GmState
  { getCode :: GmCode,
    getStack :: GmStack,
    getDump :: GmDump,
    getHeap :: GmHeap,
    getGlobals :: GmGlobals,
    getStats :: GmStats }

-- TODO Refactor with lens/generic-lens, none of this code is necesasry
-- the original code uses a quintuple but record syntax generates get functions
putCode :: GmCode -> GmState -> GmState
putCode i' state = state {getCode = i'}

putStack :: GmStack -> GmState -> GmState
putStack stack' state = state {getStack = stack'}

putDump :: GmDump -> GmState -> GmState
putDump dump' state = state {getDump = dump'}

appendDump :: GmDumpItem -> GmState -> GmState
appendDump dumpItem state = putDump (dumpItem: getDump state) state

putHeap :: GmHeap -> GmState -> GmState
putHeap heap' state = state {getHeap = heap'}

appendGlobal :: GmGlobal -> GmState -> GmState
appendGlobal newGlobal state =  state {getGlobals = newGlobal:getGlobals state}

putStats :: GmStats -> GmState -> GmState
putStats stats' state = state {getStats = stats'}

statInitial :: Int
statInitial = 0
statIncSteps, statGetSteps :: Int -> Int
statIncSteps s = s+1
statGetSteps s = s

-- Utilities

-- Recursion schemes (I should use these)
para :: (a -> [a] -> b -> b) -> b -> [a] -> b
para c k (x : xs) = c x xs (para c k xs)
para c k []       = k

cata :: (a -> b -> b) -> b -> [a] -> b
cata c k (x : xs) = c x (cata c k xs)
cata c k [] = k

limitList 0 (x:xs) = [] -- recursion scheme?
limitList n (x:xs) = x:limitList (n-1) xs
limitList k [] = []

-- (# of objects in the heap, unused addresses, [(address, object)])
type Heap a = (Int, [Int], [(Int, a)])
type Addr = Int

hInitial :: Heap a
-- (0 objects in heap, address 1 .. infty, no allocations)
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
-- def is practically only used to call error, not at all safe
aLookup [] k' def = def
aLookup ((k,v):bs) k' def | k == k' = v
                          | k /= k' = aLookup bs k' def


aReplace [] _ def = def -- cata? but error
aReplace ((k,v):bs) (k',v') def | k == k' = (k',v'): bs
                                | k /= k' = (k,v)  : aReplace bs (k',v') def

aLookupSafe [] k' = Nothing
aLookupSafe ((k,v):bs) k' | k == k'   = Just v
                          | otherwise = aLookupSafe bs k'

aDomain = map fst
aRange = map snd
aEmpty = []

-- this should be a recursion scheme on non-empty and lists and not reverse
mkApChain :: [CoreExpr] -> CoreExpr
mkApChain = mkApChain'.reverse
-- k 2 7 ~ [EVar "k", ENum 2, Enum 7]
-- -> EAp (EAp (EVar "k") (ENum 2)) (ENum 7)
mkApChain' :: [CoreExpr] -> CoreExpr
mkApChain' [] = error "No expressions to chain"
mkApChain' [x] = x
mkApChain' (x:xs@(_:_)) = EAp (mkApChain' xs) x

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
ppStats s = pretty "Steps taken (if terminating) = " <> (pretty.statGetSteps.getStats $ s)

ppNode :: GmState -> Addr -> Node -> Doc ann
ppNode _ _ (NNum n) = pretty n
ppNode s a (NGlobal _ g) = pretty "Global " <> pretty v
  where v = head [n | (n,b) <- getGlobals s, a == b]
  -- print globals by matching address lookup
ppNode _ _ (NAp a1 a2) = pretty "Ap" <+> pretty a1 <+> pretty a2
ppNode _ _ (NInd a) = pretty "NInd" <+> pretty a

ppSC :: GmState -> (Name, Addr) -> Doc ann
ppSC s (name, addr) = pretty "Code for " <> pretty name <> hardline <> ppInstrs code <> hardline
  where (NGlobal name code) = hLookup (getHeap s) addr

ppStackItem :: GmState -> Addr -> Doc ann
ppStackItem s a = pretty a <> pretty ": " <> ppNode s a (hLookup (getHeap s) a)

ppShortStack :: GmStack -> Doc ann
ppShortStack stack = encloseSep lbracket rbracket (pretty ", ") (map pretty stack)

ppStack :: GmState -> Doc ann
ppStack state = pretty " Stack:[" <> nest 2 (vsep (map (ppStackItem state) reversedStack)) <> pretty "]"
  where reversedStack = reverse $ getStack state
  -- reversed so you pop off from the bottom, stable aesthetics


ppInstr :: Instr -> Doc ann
ppInstr Unwind = pretty "Unwind"
ppInstr (Pushglobal f) = pretty "Pushglobal" <+> pretty f
ppInstr (Push n) = pretty "Push" <+> pretty n
ppInstr (Pushint n) = pretty "Pushint" <+> pretty n
ppInstr MkAp = pretty "MkAp"
ppInstr (Update n) = pretty "Update" <+> pretty n
ppInstr (Pop n) = pretty "Pop" <+> pretty n
ppInstr (Slide n) = pretty "Slide" <+> pretty n
ppInstr (Alloc n) = pretty "Alloc" <+> pretty n
ppInstr Eval = pretty "Eval"
ppInstr Add = pretty "Add"
ppInstr Sub = pretty "Sub"
ppInstr Mul = pretty "Mul"
ppInstr Div = pretty "Div"
ppInstr Mod = pretty "Mod"
ppInstr Neg = pretty "Neg"
ppInstr Eq = pretty "Eq"
ppInstr Neq = pretty "Neq"
ppInstr Lt = pretty "Lt"
ppInstr Le = pretty "Le"
ppInstr Gt = pretty "Gt"
ppInstr Ge = pretty "Ge"
ppInstr (Cond a b) = pretty "Cond" <+> ppShortInstrs 7 a <+> ppShortInstrs 7 b

ppShortInstrs :: Int -> GmCode -> Doc ann
ppShortInstrs n code = encloseSep lbrace rbrace (pretty "; ") dotcodes
  where codes = map ppInstr (take n code)
        dotcodes | length code > n = codes ++  [pretty "..."]
                 | otherwise       = codes

ppInstrs :: GmCode -> Doc ann
ppInstrs is = pretty "  Code:{" <> (nest 2 $ vsep (map ppInstr is)) <> pretty "}" <> hardline

ppDumpItem :: GmDumpItem -> Doc ann
ppDumpItem (code, stack) = langle <> ppShortInstrs 3 code <> pretty ", " <> ppShortStack stack <> rangle

ppDump :: GmState -> Doc ann
ppDump s = nest 4 (pretty "Dump:[" <> vsep (map ppDumpItem (reverse.getDump $ s)) <> rangle)

ppState :: GmState -> Doc ann
ppState s = ppStack s <> hardline <> ppDump s <> hardline <> ppInstrs (getCode s) <> hardline

ppResults :: [GmState] -> Doc ann
ppResults states@(state:ss) =
  pretty "Supercombinator definitions" <> hardline <>
  vsep (map (ppSC state) (getGlobals state)) <> hardline <> hardline <>
 pretty "State transitions" <> hardline <> hardline <>
 -- we limit the length because often breaking changes cause infinite loops
 vsep (map ppState limitedStates) <> hardline <> hardline <>
 ppStats (last limitedStates)
   where limitedStates = limitList 1000000 states
