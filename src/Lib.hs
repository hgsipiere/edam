{-# LANGUAGE BlockArguments #-}

module Lib
    ( mainFunc
    ) where

import Data.List (mapAccumL)
import Type

mainFunc :: IO ()
mainFunc = putStrLn k

-- TODO Introduce runProg :: CoreExpr -> Int,
-- that compiles, evaluates then grabs the last state
-- if the stack is a single number prints that number
-- otherwise error. This is so I can write tests for evaluation.

-- TODO test for laziness by introducing fix combinator
-- fix f x = f (fix f) x
-- fix id 3 seems to loop forever in GHCi
-- A solution may be to introduce a predicate, short n xs
-- which checks if the list xs is n or shorter
-- then for the evaluation check the evaluation states
-- aren't ridiculously long
-- maybe should do this program
-- main = k 3 (fix id 3)

--prog = [("main", [],
--  EAp
--  (EAp (EVar "k") (ENum 9))
--  (ENum 9)
--  )]
prog = [("main", [], EAp (EVar "i") (ENum 9))]

--prog = [("main", [],
--  EAp
--  (EAp (EAp (EVar "twice") (EVar "twice")) (EVar "i"))
--  (ENum 3))]

--prog = [("main", [],
--  EAp (EAp (EVar "fix") (EVar "i")) (ENum 12))]

k = show.ppResults.eval.compile $ prog

-- fix f = f (fix f)

preludeDefs = [
  ("i", ["x"], EVar "x"),
  ("fix", ["f"],
  EAp (EVar "f")
  (EAp (EVar "fix") (EVar "f")))
  --("k", ["x","y"], EVar "x"),
  --("twice", ["f","x"], EAp (EVar "f") (EAp (EVar "f") (EVar "x")))
  ]

doAdmin :: GmState -> GmState
doAdmin s = putStats (statIncSteps $ getStats s) s

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
-- =>        i a:s h[a:NNum n] m[n : a]
pushint :: Int -> GmState -> GmState
pushint n state = case aLookupSafe (getGlobals state) (show n) of
      Just a -> putStack (a: getStack state) state
      Nothing -> let (heap', a) = hAlloc (getHeap state) (NNum n) in
        appendGlobal (show n, a) $ putHeap heap' $ putStack (a: getStack state) state

-- MkAp i a_1:a_2:s h                m
-- =>   i       a:s h[a:NAp a_1 a_2] m
mkap state = putHeap heap' (putStack (a:as') state)
  where (heap', a) = hAlloc (getHeap state) (NAp a1 a2)
        (a1:a2:as') = getStack state
-- Push n:i     a_0: ... :a_n:s h m
-- =>     i a_n:a_0: ... :a_n:s h m
-- Rearrange the stack so that we point to the argument being applied
-- rather than the function doing the applying, this means that
-- push n now takes the nth function argument starting from 0
push :: Int -> GmState -> GmState
push n state
  = putStack (a_n:as) state
  where as = getStack state
        a_n  = as !! n

-- Slide n:i a_0: ... :a_n:s h m
-- =>      i           a_0:s h m
-- Take the top of the stack and put it n down
slide n state = putStack (a: drop n as) state
  where (a:as) = getStack state

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

-- [Unwind] a:s h[a:NNum n] m
-- =>    [] a:s h           m
-- Unwinding the stack finished if number result
--
--    [Unwind]     a:s h[a:NAp a_1 a_2] m
-- => [Unwind] a_1:a:s h                m
-- If an application, put the function at the top of the stack
--
-- [Unwind] a_0: ... :a_n:s  h[a_0 : NGlobal n c     ]
--                            [a1  : NAp a_0     a_1']
--                            [        ...           ]
--                            [a_n : NAp a_(n-1) a_n'] m
-- =>     c a_0: ... :a_n:s  h                         m
-- If there is a global definition on top of the stack
-- then below there will be a series of node applications
-- however the stack is arranged to have arguments on the stack
-- for reducing so we need to extract the arguments.

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
dispatch (Update n) = update n
dispatch (Pop n) = pop n
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

-- This supercombinator (sc) compilation scheme, takes an n arity sc
-- then it generates an environment rho^0, this is a finite map from arguments
-- to what is understood for the moment as a specific relative arity
-- The specific relative arity is kind of the position in the application reduction
-- SC [[f x_1 ... x_n = e]] = R [[e]] [x_1 -> 0, ..., x_n -> n-1] n
-- According to SPJ, this number can be used to determine argument stack position
-- as I understand the book.
-- The implementation actually just works out n, it seems.
compileSc :: (Name, [Name], CoreExpr) -> GmCompiledSc
compileSc (name,env,body) = (name, length env, compileR body (zip env [0..]))

-- Old comment, need to figure out what changed
-- Generate code for the expression, incorporating the current environment
-- so possible variables I think? hence we then need to slide (d+1) down
-- d for the arity, 1 for the compiled expression itself being removed as
-- it has been compiled so we wouldn't want to loop? I think. Unwind just to reduce.
-- R [[e]] rho d = C [[e]] rho ++ [Slide d + 1, Unwind]
--
-- Not sure what this does yet, Mark 2 change
-- This is the state transition but I'm confused.
-- Update d: Pop d:i  a:a_0: ... :a_d:s h             m
-- =>              i                  s h[a_d:NInd a] m
-- R[[e]] rho d = C[[e]] rho ++ [Update d, Pop d, Unwind]
compileR :: GmCompiler
compileR e env = compileC e env ++ [Update d, Pop d, Unwind]
  where d = length env

-- C[[f]] rho = [Pushglobal f]                                  where f is a supercombinator
-- C[[x]] rho = [Push (rho x)]                                  where x is a local variable
-- C[[i]] rho = [Pushint i]
-- C[[e_0 e_1]] rho = C[[e_1]] rho ++ C[[e_0]] rho^+1 ++ [MkAp] where p^+n x = (rho x) + n
-- For the second one, we have to find the specific relative arity by using the environment
-- or finite map rho.
-- For the third one, I think we have to shift the environment by one because this is application
-- so there is something being applied thus the specific relative arity I think has to shift?
-- the compilation order is opposite order to application because we put evaluation code on top
-- then reduce down instructions
compileC :: GmCompiler
compileC (EVar v) env
  | elem v (aDomain env) = [Push n]
  | otherwise            = [Pushglobal v]
  -- this shouldn't evaluate unnecessarily due to lazy evaluation
    where n = aLookup env v (error "Can't happen")

compileC (ENum n) env = [Pushint n]
compileC (EAp e1 e2) env = compileC e2 env ++ compileC e1 (argOffset 1 env) ++ [MkAp]
  where argOffset :: Int -> GmEnvironment -> GmEnvironment
        -- this implements argOffset n rho = rho^n
        argOffset n env = (\(arg,rel) -> (arg,rel+n)) <$> env

compile program = (initialCode, [], heap, globals, statInitial)
  where (heap, globals) = buildInitialHeap program
        initialCode = [Pushglobal "main", Unwind]

-- we iterate over the heap, each time we allocate to the
-- heap the global node and make a map of globals which
-- is just a map from global names to the address in the heap
buildInitialHeap :: CoreProgram -> (GmHeap, GmGlobals)
buildInitialHeap program = mapAccumL allocateSc hInitial compiledWPrelude
  where compiled = map compileSc program
        compiledPrimitives = [] -- Nothing at the moment
        compiledWPrelude = (compileSc <$> preludeDefs) ++ compiled ++ compiledPrimitives

allocateSc :: GmHeap -> GmCompiledSc -> (GmHeap, (Name, Addr))
allocateSc heap (name, nargs, instns) = (heap', (name, addr))
  where (heap', addr) = hAlloc heap (NGlobal nargs instns)
