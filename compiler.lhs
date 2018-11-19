> import Control.Monad.Trans.Writer.Lazy
> import Control.Monad.Trans.Class

Monadic Compiler

Hangjian Yuan
psyhy4@nottingham.ac.uk

--------------------------------------------------------------------------------

Imperative language:

> data Prog = Assign Name Expr
>           | If Expr Prog Prog
>           | While Expr Prog
>           | Seqn [Prog]
>             deriving Show
>
> data Expr = Val Int | Var Name | App Op Expr Expr
>             deriving Show
>
> type Name = Char
>
> data Op   = Add | Sub | Mul | Div
>             deriving Show

Factorial example:

> fac :: Int -> Prog
> fac n = Seqn [Assign 'A' (Val 1),
>               Assign 'B' (Val n),
>               While (Var 'B') (Seqn
>                  [Assign 'A' (App Mul (Var 'A') (Var 'B')),
>                   Assign 'B' (App Sub (Var 'B') (Val (1)))])]

Virtual machine:

> type Stack = [Int]
>
> type Mem   = [(Name,Int)]
>
> type Code  = [Inst]
> 
> data Inst  = PUSH Int
>            | PUSHV Name
>            | POP Name
>            | DO Op
>            | JUMP Label
>            | JUMPZ Label
>            | LABEL Label
>              deriving Show
> 
> type Label = Int

State monad:

> type State = Label
>
> newtype ST a = S (State -> (a, State))
>
> app :: ST a -> State -> (a,State)
> app (S st) x 	=  st x
>
> instance Functor ST where
>    -- fmap :: (a -> b) -> ST a -> ST b
>    fmap g st = S (\s -> let (x,s') = app st s in (g x, s'))
>
> instance Applicative ST where
>    -- pure :: a -> ST a
>    pure x = S (\s -> (x,s))
>
>    -- (<*>) :: ST (a -> b) -> ST a -> ST b
>    stf <*> stx = S (\s ->
>       let (f,s')  = app stf s
>           (x,s'') = app stx s' in (f x, s''))
>
> instance Monad ST where
>    -- return :: a -> ST a
>    return x = S (\s -> (x,s))
>
>    -- (>>=) :: ST a -> (a -> ST b) -> ST b
>    st >>= f = S (\s -> let (x,s') = app st s in app (f x) s')

--------------------------------------------------------------------------------

This function translates Expr (expression) into Code.
Because this part doesn't contain any effect (monad), there is no need to use WriterT here.

> compExpr :: Expr -> Code
> compExpr (Val n) = [PUSH n]
> compExpr (Var x) = [PUSHV x]
> compExpr (App o l r) = (compExpr l) ++ (compExpr r) ++ [DO o]


This helper function is used to increment the label, which is the "state" in this coursework.

> fresh :: ST Label
> fresh = S (\n -> (n, n + 1))


This function is the core part of the compiler, It translates all the control statements 
(Assign, If, While, Seqn) into machine code level.

The implementation uses WriterT to combine the Writer Monad and the State Monad.
State Monad is used to "store" the value of label (integer).
Writer Monad has two parameters in normal case, the output and the computation result.
However, in this case, we store the code in the output (type: Code),
and the computation result is useless (type: ()).
So, The final return type of this function is WriterT Code ST ().

> mcomp :: Prog -> WriterT Code ST ()
> mcomp (Assign n e) = do tell (compExpr e)
>                         tell [POP n]
> mcomp (If e l r)   = do n1 <- lift fresh
>                         n2 <- lift fresh
>                         tell (compExpr e)
>                         tell [JUMPZ n1]
>                         mcomp l
>                         tell [JUMP n2]
>                         tell [LABEL n1]
>                         mcomp r
>                         tell [LABEL n2]
> mcomp (While e p)  = do n1 <- lift fresh
>                         n2 <- lift fresh
>                         tell [LABEL n1]
>                         tell (compExpr e)
>                         tell [JUMPZ n2]
>                         mcomp p
>                         tell [JUMP n1]
>                         tell [LABEL n2]
> mcomp (Seqn [])      = do tell []
> mcomp (Seqn (p:ps))  = do mcomp p
>                           mcomp (Seqn ps)

This function extracts the Code from the return value of mcomp function.
execWriterT is used to get rid of Writer Monad.
app and fst are used to get rid of State Monad.

> comp :: Prog -> Code
> comp p = fst (app (execWriterT (mcomp p)) 0)

--------------------------------------------------------------------------------

PC: Program Counter

> type PC = Int


This helper function takes a Name and a Mem as the input, and search the corresponding
int value as the output.
It returns Nothing if there is no tuple in the memory has the same name.

> find :: Name -> Mem -> Maybe Int
> find x [] = Nothing
> find x (m:ms) | x == fst m = Just (snd m)
>               | otherwise  = find x ms


This helper function takes a value from memory to the stack.
It uses find function to get the value, and put it at the top of the stack.

> fetch :: (Mem, Stack) -> Name -> Stack
> fetch (m, s) n = x:s where Just x = find n m


This function is used to update the data in memory.
If the variable already exists, replace the old value by the new one.
Otherwise, append the new tuple at the end of the memory.

> update :: (Name, Int) -> Mem -> Mem
> update (n, i) m | find n m == Nothing = m ++ [(n, i)]
>                 | otherwise = takeWhile (\a -> fst a /= n) m ++ 
>                               [(n, i)] ++ 
>                               tail (dropWhile (\a -> fst a /= n) m)


This function gives the implementations of Add, Sub, Mul, Div.

> arithm :: Op -> Int -> Int -> Int
> arithm Add x y = x + y
> arithm Sub x y = x - y
> arithm Mul x y = x * y
> arithm Div x y = x `div` y


This function takes a code snippet and a label, then it search the label's location
in the code, and return the location.

> jump :: Code -> Label -> PC
> jump ((LABEL x):xs) l | x == l = 0
> jump (x:xs) l = 1 + (jump xs l)


This function is the core part of the executor.
It takes a machine's state (Code, PC, Mem, Stack) and one instruction, 
then executes the instruction, return the new machine state.

> step :: (Code, PC, Mem, Stack) -> Inst -> (Code, PC, Mem, Stack)
> step (c, p, m, s) (PUSH i)     = (c, p+1, m, i:s)
> step (c, p, m, s) (PUSHV n)    = (c, p+1, m, fetch (m, s) n)
> step (c, p, m, x:xs) (POP n)   = (c, p+1, update (n, x) m, xs)
> step (c, p, m, x:y:zs) (DO o)  = (c, p+1, m, (arithm o y x) : zs)
> step (c, p, m, s) (JUMP l)     = (c, jump c l, m, s)
> step (c, p, m, x:xs) (JUMPZ l) | x == 0 = (c, jump c l, m, xs) 
>                                | otherwise = (c, p+1, m, xs)
> step (c, p, m, s) (LABEL l)    = (c, p+1, m, s)


This function used step function to execute the code, the only thing it does
is to check whether the PC already reached the end of the code.

> exec' :: (Code, PC, Mem, Stack) -> (Code, PC, Mem, Stack)
> exec' (c, p, m, s) | p < (length c) = exec' (step (c, p, m, s) (c !! p))
>                    | otherwise      = (c, p, m, s)


This function is the interface for the executor.
It takes a code snippet, and return the final content in memory.

> exec :: Code -> Mem
> exec c = m where (c', p, m, s) = exec' (c, 0, [], [])
