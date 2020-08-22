{-# LANGUAGE BlockArguments #-}

module Lib
    ( mainFunc
    ) where

import Data.List (mapAccumL)
import Type

mainFunc :: IO ()
mainFunc = putStrLn k

prog = [("main", [],
  EAp
  (EAp (EVar "k") (ENum 9))
  (ENum 12)
  )]
k = show.ppResults.eval.compile $ prog

preludeDefs = [("i", ["x"], EVar "x"), ("k", ["x","y"], EVar "x")]

doAdmin :: GmState -> GmState
doAdmin s = putStats (statIncSteps $ getStats s) s

-- Pushglobal f:i   s h m[f:a]
-- =>           i a:s h m
pushglobal f state = putStack (a: getStack state) state
  where a = aLookup (getGlobals state) f (error $ "Undeclared global " ++ f)

-- pushint n:i   s h           m
-- =>        i a:s h[a:NNum n] m
pushint n state
  = putHeap heap' (putStack (a: getStack state) state)
  where (heap', a) = hAlloc (getHeap state) (NNum n)

-- MkAp i a_1:a_2:s h                m
-- =>   i       a:s h[a:NAp a_1 a_2] m
mkap state = putHeap heap' (putStack (a:as') state)
  where (heap', a) = hAlloc (getHeap state) (NAp a1 a2)
        (a1:a2:as') = getStack state

-- Push n:i      a_0: ... :a_(n+1): s h[a_(n+1) : NAp a_n a'_n] m
-- =>     i a'_n:a_0: ... :a_(n+1): s h                         m
-- For example push 0, would assume that the stack was where f is a function
-- a_0=f, a_1=NAp f arg like so and it would put the argument arg on top of the stack
-- then for push n, you would go n into the stack e.g. push 1,
-- a_0, a_1=f, a_2=NAp f arg and put arg on top of the stack
push :: Int -> GmState -> GmState
push n state
  = putStack (a:as) state
  where as = getStack state
        a  = getArg $ hLookup (getHeap state) (as !! (n+1))

-- slide n:i a_0: ... :a_n:s h m
-- =>      i           a_0:s h m
-- Take the top of the stack and put it n down
slide n state = putStack (a: drop n as) state
  where (a:as) = getStack state

-- [Unwind] a:s h[a:NNum n] m
-- =>    [] a:s h           m
-- Unwinding the stack finished if number result
--
--    [Unwind]     a:s h[a:NAp a_1 a_2] m
-- => [Unwind] a_1:a:s h                m
-- If an application, put the function at the top of the stack
--
-- [Unwind] a_0: ... :a_n:s h[a_0 : NGlobal n c] m
-- =>     c a_0: ... :a_n:s h                    m
-- If there is a global definition, put the defining code as the instruction list
unwind :: GmState -> GmState
unwind state = newState $ hLookup heap a
  where (a:as) = getStack state
        heap   = getHeap state
	newState (NNum n) = state
	newState (NAp a1 a2) = putCode [Unwind] (putStack (a1:a:as) state)
	newState (NGlobal n c)
	  | length as < n = error "Unwinding with too few arguments"
	  | otherwise     = putCode c state

dispatch :: Instruction -> GmState -> GmState
dispatch (Pushglobal f) = pushglobal f
dispatch (Pushint n) = pushint n
dispatch MkAp = mkap
dispatch (Push n) = push n
dispatch (Slide n) = slide n
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

-- Generate code for the expression, incorporating the current environment
-- so possible variables I think? hence we then need to slide (d+1) down
-- d for the arity, 1 for the compiled expression itself being removed as
-- it has been compiled so we wouldn't want to loop? I think. Unwind just to reduce.
-- R [[e]] rho d = C [[e]] rho ++ [Slide d + 1, Unwind]
compileR :: GmCompiler
compileR e env = compileC e env ++ [Slide (length env + 1), Unwind]

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
