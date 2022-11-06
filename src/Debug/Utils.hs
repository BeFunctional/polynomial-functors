module Debug.Utils (trace, traceV, traceIf)where

import Debug.Trace

traceV :: (Show s) => s -> s
traceV x = trace (show x) x

traceIf :: Bool -> String -> a -> a
traceIf True = trace
traceIf False = const id
