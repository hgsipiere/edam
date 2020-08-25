{-# LANGUAGE BlockArguments #-}

module Lib
    ( mainFunc
    ) where

import Data.List (mapAccumL)
import Type

mainFunc :: IO ()
mainFunc = putStrLn k

-- Mk6 implements output so then write tests for these, for now it is awkward.
--prog = [("main", [],
--  EAp
--  (EAp (EVar "k") (ENum 9))
--  (ENum 9)
--  )]

--prog = [("main", [], 
--  ELet recursive [("x",EAp (EVar "i") (ENum 9))] (EVar "x")
--  )]

--prog = [("main", [],
--  EAp
--  (EAp (EAp (EVar "twice") (EVar "twice")) (EVar "i"))
--  (ENum 3))]

--prog = [
--  ("const3", ["x"], ENum 3),
--  ("y", ["f"],
--  ELet recursive
--  [("x",EAp (EVar "f") (EVar "x"))] (EVar "x")),
--  ("main", [], EAp (EVar "y") (EVar "const3"))
--  ]


{-prog = [("main", [],
  ELet recursive
  [("fix2", ["f"],
  EAp (EVar "f")
  (EAp (EVar "fix") (EVar "f")))]


  (EAp (EAp (EVar "fix") (EVar "i")) (ENum 12)))] -}

prog = [("main", [], EAp (EVar "i") (ENum 12))]


k = show.ppResults.eval.compile $ prog
-- fix f = f (fix f)

preludeDefs = [
  ("i", ["x"], EVar "x"),
  ("fix", ["f"], -- fix f = f (fix f)
  EAp (EVar "f")
  (EAp (EVar "fix") (EVar "f"))),
  ("k", ["x","y"], EVar "x"),
  ("twice", ["f","x"], EAp (EVar "f") (EAp (EVar "f") (EVar "x")))
  ]

doAdmin :: GmState -> GmState
doAdmin s = putStats (statIncSteps $ getStats s) s

-- State transition description
-- [instructions] [stack] [heap] [globals]
-- => [instructions'] [stack'] [heap'] [globals']

-- Pushglobal f:i   s h m[f:a]
-- =>           i a:s h m
pushglobal f state = putStack (a: getStack state) state
  where a = aLookup (getGlobals state) f (error $ "Undeclared global " ++ f)

-- pushint n:i   s h           m[show n:a]
-- =>        i a:s h           m
-- If there is "n" in the heap then just put the address on the stack
--
-- Otherwise put it onto the stack then also put it into the globals
-- pushint n:i   s h           m
-- =>        i a:s h[a:NNum n] m[show n:a]
pushint :: Int -> GmState -> GmState
pushint n state = case aLookupSafe (getGlobals state) (show n) of
      Just a -> putStack (a: getStack state) state
      Nothing -> let (heap', a) = hAlloc (getHeap state) (NNum n) in
        appendGlobal (show n, a) $ putHeap heap' $ putStack (a: getStack state) state

-- MkAp i a_1:a_2:s h                m
-- =>   i       a:s h[a:NAp a_1 a_2] m
-- Draw an application node in the graph with stack pointers
mkap state = putHeap heap' (putStack (a:as') state)
  where (heap', a) = hAlloc (getHeap state) (NAp a1 a2)
        (a1:a2:as') = getStack state
-- Push n:i     a_0: ... :a_n:s h m (3.18)
-- =>     i a_n:a_0: ... :a_n:s h m
-- Push the nth argument to the top of the stack starting from 0
-- as of Mk 3 the stack directly leaves application arguments on the stack
push :: Int -> GmState -> GmState
push n state
  = putStack (a_n:as) state
  where as = getStack state
        a_n  = as !! n

-- Slide n:i a_0: ... :a_n:s h m
-- =>      i           a_0:s h m
-- Take the top of the stack and put it n down
--
-- See figure (3.1) for the use case in the Mk 1
-- It can be used for strict evaluation to
-- draw the graph with [Unwind] global
-- then create pointers to the application arguments
-- with push then reduce with a function given by the code
-- the sliding is to then get rid of the original graph
-- once we already have pointers to the graph's application arguments.
slide n state = putStack (a: drop n as) state
  where (a:as) = getStack state


-- For use case see Figure 3.5
-- The idea is that applying f x_1 ... x_n,
-- we have on the stack f and its n arguments.
-- however our program will draw a new seperate graph
-- e below f, x_1, ..., x_n pointers etc so what we
-- do is that we replace the top application of the supercombinator
-- reduction with an indirection to the result so any references
-- to this reduction all go to this indirection.
-- Then what you do is you get rid of all the inbetween application nodes.

-- Update n:i a:a_0: ... :a_n:s h             m
-- =>       i   a_0: ... :a_n:s h[a_n:NInd a] m
update :: Int -> GmState -> GmState
update n state = putStack as $ putHeap (objectCount, freeAddrs, addrValueMap') state
  where (a:as) = getStack state
        a_n = as !! n
        (objectCount, freeAddrs,addrValueMap) = getHeap state 
        addrValueMap' = aReplace addrValueMap (a_n , NInd a) (error "Stack value not in heap?")

-- Pop n:i a_1: ... :a_n:s h m
-- =>    i               s h m
pop :: Int -> GmState -> GmState
pop n state = putStack (drop n $ getStack state) state

-- Alloc n:i               s h                   m (3.20)
-- =>      i a_1: ... :a_n:s h[a_1: NInd hNull ] m
--                            [       ...      ]
--                            [a_n: NInd hNull ]
alloc :: Int -> GmState -> GmState
alloc n state = putStack (addrs ++ (getStack stateWithHeap)) stateWithHeap
  where (heap,addrs) = allocNodes n (getHeap state)
        stateWithHeap = putHeap heap state

-- as given 3.5.3 (except n+k patterns)
allocNodes :: Int -> GmHeap -> (GmHeap, [Addr])
allocNodes 0     heap = (heap, [])
allocNodes n_plus_1 heap = (heap2, (a:as))
  where hNull = -1 -- Impossible heap allocation address
        (heap1, as) = allocNodes (n_plus_1 - 1) heap
        (heap2, a) = hAlloc heap1 (NInd hNull)

-- [Unwind] a:s h[a:NNum n] m
-- =>    [] a:s h           m
-- Unwinding the stack finished if number result
--
--    [Unwind]     a:s h[a:NAp a_1 a_2] m
-- => [Unwind] a_1:a:s h                m
-- If an application, put the function at the top of the stack
--
-- [Unwind] a_0: ... :a_n:s  h[a_0 : NGlobal n c     ] (3.19)
--                            [a1  : NAp a_0     a_1']
--                            [        ...           ]
--                            [a_n : NAp a_(n-1) a_n'] m
-- =>     c a_0: ... :a_n:s  h                         m
-- If there is a global definition on top of the stack
-- then below there will be a series of node applications
-- however the stack is arranged to have arguments on the stack
-- for reducing so we need to extract the arguments.
-- 
-- See figure 3.7 (Mark 3 onwards) to see an illustration
-- of how this builds a graph to be reduced

-- [Unwind]  a:s h[a: NInd a'] m
-- =>       a':s h             m
-- If there is an indirection to a' at a, replace a with a'
unwind :: GmState -> GmState
unwind state = newState $ hLookup heap a
  where mapn n f xs = map f (take n xs) ++ drop n xs
        (a:as) = getStack state
        heap   = getHeap state
        newState (NNum n) = state
        newState (NAp a1 a2) = putCode [Unwind] (putStack (a1:a:as) state)
        newState (NGlobal n c)
          | length as < n = error "Unwinding with too few arguments"
          | otherwise     = let stack' = rearrange n (getHeap state) (getStack state) in
                            putCode c $ putStack stack' state
        newState (NInd a') = putCode [Unwind] (putStack (a':as) state)

-- As given by SPJ in the book, this takes the stack a_0:...:a_n:s to a_1:...:a_n:s then
-- maps to the argument of the application referred to by each address like the unwind except s
rearrange :: Int -> GmHeap -> GmStack -> GmStack
rearrange n heap as = take n as' ++ drop n as
  where as' = map (getArg. hLookup heap) $ tail as

dispatch :: Instruction -> GmState -> GmState
dispatch (Pushglobal f) = pushglobal f
dispatch (Pushint n) = pushint n
dispatch MkAp = mkap
dispatch (Push n) = push n
dispatch (Slide n) = slide n
dispatch (Update n) = update n
dispatch (Pop n) = pop n
dispatch (Alloc n) = alloc n
dispatch Unwind = unwind

step :: GmState -> GmState
step state = dispatch i (putCode is state)
  where (i:is) = getCode state

gmFinal :: GmState -> Bool
gmFinal = null.getCode

eval :: GmState -> [GmState]
eval state = state : restStates
  where restStates | gmFinal state = []
                   | otherwise     = eval nextState
        nextState = doAdmin (step state)

type GmCompiledSc = (Name, Int, GmCode)
type GmEnvironment = Assoc Name Int
type GmCompiler = CoreExpr -> GmEnvironment -> GmCode

-- SC [[f x_1 ... x_n = e]] = R [[e]] [x_1 -> 0, ..., x_n -> n-1] n
-- For a direct supercombinator application the arguments are typically
-- directly on the stack 
compileSc :: (Name, [Name], CoreExpr) -> GmCompiledSc
compileSc (name,env,body) = (name, length env, compileR body (zip env [0..]))

-- Compile expression body then update top application with redirect, clean up with pop
-- This is the state transition for context.
-- Update d: Pop d:i  a:a_0: ... :a_d:s h             m
-- =>              i                  s h[a_d:NInd a] m
-- R[[e]] rho d = C[[e]] rho ++ [Update d, Pop d, Unwind]
compileR :: GmCompiler
compileR e env = compileC e env ++ [Update d, Pop d, Unwind]
  where d = length env

-- Mk 3 change really don't understand
-- C[[f]] rho = [Pushglobal f]                                  where f is a supercombinator
-- C[[x]] rho = [Push (rho x)]                                  where x is a local variable
-- C[[i]] rho = [Pushint i]
-- C[[e_0 e_1]] rho = C[[e_1]] rho ++ C[[e_0]] rho^+1 ++ [MkAp] where p^+n x = (rho x) + n
-- C[let x_1=e_1; ...; x_n=e_n in e]] rho
--               = C[[e_1]] rho^+0 ++ ... ++
--                 C[[e_n]] rho^+(n-1) ++
--                 C[[e]] rho' ++ [Slide n]                     where p' = p^(+n) [x-1 -> n-1, ... x_n -> 0]
-- C[[letrec x_1=e1; ... ; x_n = e_n in e]] rho
--               = [Alloc n] ++
--                 C[[e_1]] rho' ++ [Update n-1]
--                 C[[e_k]] rho' ++ [Update n-k] ++ ... ++
--                 C[[e_n]] rho' ++ [Update 0] ++
--                 C[[e]] rho' ++ [Slide n]                     where p' = p^(+n)[x_1 -> n-1,..., x_n -> 0]
-- Figure 3.10 (changed with k)
argOffset :: Int -> GmEnvironment -> GmEnvironment
-- argOffset n rho = rho^n
argOffset n env = (\(arg,rel) -> (arg,rel+n)) <$> env

compileC :: GmCompiler
compileC (EVar v) env
  | elem v (aDomain env) = [Push n]
  | otherwise            = [Pushglobal v]
    where n = aLookup env v (error "Can't happen")
    -- the environment maps argument names to how far up
    -- the stack they are, argument pointers are directly on the stack
    -- so we push this stack distance starting from 0
compileC (ENum n) env = [Pushint n]
-- Apply e2 to e1, since e2 is given the original environment, we need to
-- shift the environment for e1 since it has an argument in the stack e2 then the rest (not sure?)
compileC (EAp e1 e2) env = compileC e2 env ++ compileC e1 (argOffset 1 env) ++ [MkAp]
compileC (ELet recursive defs e) args -- 3.5.4
         | recursive = compileLetrec compileC defs e args
         | otherwise = compileLet    compileC defs e args

-- calculates rho'
compileArgs :: [CoreDefn] -> GmEnvironment -> GmEnvironment
compileArgs defs env
  = zip (map fst defs) [(n-1) .. 0] ++ argOffset n env
    where n = length defs

compileLet :: GmCompiler -> [CoreDefn] -> GmCompiler
compileLet comp defs expr env
  = compileLet' defs env ++ comp expr env' ++ [Slide n]
  -- I think that we need rho' because the earliest compiled
  -- argument is the first one so will be deepest in the stack
  -- and x_n will be the last one compiled so closest to the result expression
  -- in the stack thus is mapped to 0
  where env' = compileArgs defs env
        n    = length defs

-- compile new definitions
compileLet' :: [CoreDefn] -> GmEnvironment -> GmCode
compileLet' [] env = []
-- starts with C[[e_1]] rho^+0 then C[[e_2]] rho^+(1),
-- argOffset does the rho exponent adjustment
compileLet' ((name,expr):defs) env
  -- We argOffset because closer to the start of the stack
  -- there has been a new expression defined (earlier definition)
  -- so the environment requires adjusting.
  = compileC expr env ++ compileLet' defs (argOffset 1 env)

-- letrec <x_1 = e_1; x_n = e_n> expr
-- Each x_j is to be defined in an indirection so we allocate dummy indirections (-1 address)
-- Then what we do is compile each expression with a differing environment each time
-- then after expression compilation we point the evaluated value to one of the dummy indirections
-- after all this you just clean up the stack by getting rid of all the x_j originals
-- since they are in indirections
compileLetrec :: GmCompiler -> [CoreDefn] -> GmCompiler -- ex 3.16
compileLetrec comp defs expr env = [Alloc n] ++ compileLetrec' 1 defs env' ++ comp expr env' ++ [Slide n]
  where n = length defs
        env' = compileArgs defs env
compileLetrec' :: Int -> [CoreDefn] -> GmEnvironment -> GmCode
compileLetrec' _ [] _ = []
compileLetrec' k ((name,expr):defs) env = compileC expr env ++ [Update (n-k)] ++ compileLetrec' (k+1) defs env
  where n = length defs + k

compile program = (initialCode, [], heap, globals, statInitial)
  where (heap, globals) = buildInitialHeap program
        initialCode = [Pushglobal "main", Unwind]

-- put all the super combinators in the heap and provide an association map from names to addresses
buildInitialHeap :: CoreProgram -> (GmHeap, GmGlobals)
buildInitialHeap program = mapAccumL allocateSc hInitial compiledWPrelude
  where compiled = map compileSc program
        compiledPrimitives = [] -- Nothing at the moment
        compiledWPrelude = (compileSc <$> preludeDefs) ++ compiled ++ compiledPrimitives

allocateSc :: GmHeap -> GmCompiledSc -> (GmHeap, (Name, Addr))
allocateSc heap (name, nargs, instns) = (heap', (name, addr))
  where (heap', addr) = hAlloc heap (NGlobal nargs instns)
