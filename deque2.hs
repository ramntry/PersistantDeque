module Main where

-- See http://www.lektorium.tv/lecture/?id=14322
--     http://www.aladdin.cs.cmu.edu/papers/pdfs/y2000/catenable.pdf (part 3, "Noncatenable Deques")

import Data.Tuple
import Test.QuickCheck
import Criterion.Main

class Deque d where
    emptyDeque :: d a
    putFront :: a -> d a -> d a
    putBack :: a -> d a -> d a
    popFront :: d a -> Maybe (a, d a)
    popBack :: d a -> Maybe (a, d a)


-- O(log(n)) theoretical asymptotic for all operations listed above
data Deque1 a = EmptyDeque1
             | Deque1 (Maybe a) (Deque1 (a, a)) (Maybe a)
    deriving (Show)

instance Deque Deque1 where
    emptyDeque = EmptyDeque1

    putFront x EmptyDeque1 = Deque1 (Just x) EmptyDeque1 Nothing
    putFront x (Deque1 Nothing ch t) = Deque1 (Just x) ch t
    putFront x (Deque1 (Just z) ch t) = Deque1 Nothing (putFront (x, z) ch) t

    putBack y EmptyDeque1 = Deque1 Nothing EmptyDeque1 (Just y)
    putBack y (Deque1 h ch Nothing) = Deque1 h ch (Just y)
    putBack y (Deque1 h ch (Just z)) = Deque1 h (putBack (z, y) ch) Nothing


    popFront EmptyDeque1 = Nothing
    popFront (Deque1 (Just x) ch t) = case (ch, t) of
        (EmptyDeque1, Nothing) -> Just (x, EmptyDeque1)
        _                      -> Just (x, Deque1 Nothing ch t)
    popFront (Deque1 Nothing ch t) = case (popFront ch, t) of
        (Nothing, Nothing)            -> Nothing
        (Nothing, Just r)             -> Just (r, EmptyDeque1)
        (Just ((h, succ), newCh), _)  -> Just (h, Deque1 (Just succ) newCh t)


    popBack EmptyDeque1 = Nothing
    popBack (Deque1 h ch (Just x)) = case (h, ch) of
        (Nothing, EmptyDeque1) -> Just (x, EmptyDeque1)
        _                      -> Just (x, Deque1 h ch Nothing)
    popBack (Deque1 h ch Nothing) = case (h, popBack ch) of
        (Nothing, Nothing)           -> Nothing
        (Just r, Nothing)            -> Just (r, EmptyDeque1)
        (_, Just ((pred, t), newCh)) -> Just (t, Deque1 h newCh (Just pred))


newtype DequeBuffer a = DequeBuffer [a] deriving (Show)

-- amortized O(1) theoretical asymptotic for all operations
data Deque2 a = EmptyDeque2
              | Deque2 (DequeBuffer a) (Deque2 (a, a)) (DequeBuffer a)
    deriving (Show)

data DequeAction = PutFrontAction | PutBackAction

putBufferWith :: DequeAction -> a -> DequeBuffer a -> Deque2 (a, a) -> (DequeBuffer a, Deque2 (a, a))
putBufferWith act x buf deqp = case buf of
    DequeBuffer (f:s:t:[]) -> (DequeBuffer [x, f], enq (s, t) deqp)
    DequeBuffer xs         -> (DequeBuffer (x:xs), deqp)
    where enq = case act of
                PutFrontAction -> putFront
                PutBackAction  -> putBack . swap

instance Deque Deque2 where
    emptyDeque = EmptyDeque2

    putFront x EmptyDeque2 = Deque2 (DequeBuffer [x]) EmptyDeque2 (DequeBuffer [])
    putFront x (Deque2 hbuf ch tbuf) = Deque2 hbuf' ch' tbuf
        where (hbuf', ch') = putBufferWith PutFrontAction x hbuf ch

    putBack x EmptyDeque2 = Deque2 (DequeBuffer []) EmptyDeque2 (DequeBuffer [x])
    putBack x (Deque2 hbuf ch tbuf) = Deque2 hbuf ch' tbuf'
        where (tbuf', ch') = putBufferWith PutBackAction x tbuf ch

    popFront EmptyDeque2 = Nothing
    popFront (Deque2 (DequeBuffer (x:[])) EmptyDeque2 (DequeBuffer [])) = Just (x, EmptyDeque2)
    popFront (Deque2 (DequeBuffer (x:xs)) ch tbuf) = Just (x, Deque2 (DequeBuffer xs) ch tbuf)
    popFront (Deque2 (DequeBuffer []) ch tbuf) = case (popFront ch, tbuf) of
        (Nothing, DequeBuffer [])    -> Nothing
        (Nothing, DequeBuffer xs)    -> Just (last xs, Deque2 (DequeBuffer []) EmptyDeque2 (DequeBuffer (init xs)))
        (Just ((h, succ), newCh), _) -> Just (h, Deque2 (DequeBuffer [succ]) newCh tbuf) 

    popBack EmptyDeque2 = Nothing
    popBack (Deque2 (DequeBuffer []) EmptyDeque2 (DequeBuffer (x:[]))) = Just (x, EmptyDeque2)
    popBack (Deque2 hbuf ch (DequeBuffer (x:xs))) = Just (x, Deque2 hbuf ch (DequeBuffer xs))
    popBack (Deque2 hbuf ch (DequeBuffer [])) = case (popBack ch, hbuf) of
        (Nothing, DequeBuffer [])    -> Nothing
        (Nothing, DequeBuffer xs)    -> Just (last xs, Deque2 (DequeBuffer (init xs)) EmptyDeque2 (DequeBuffer []))
        (Just ((pred, t), newCh), _) -> Just (t, Deque2 hbuf newCh (DequeBuffer [pred])) 


putAllWith :: (Deque d) => (a -> d a -> d a) -> [a] -> d a -> d a
putAllWith enq = flip $ foldl (flip enq)

putFrontAll :: (Deque d) => [a] -> d a -> d a
putFrontAll = putAllWith putFront

putBackAll :: (Deque d) => [a] -> d a -> d a
putBackAll = putAllWith putBack

dequeFromList :: (Deque d) => [a] -> d a
dequeFromList = foldr putFront emptyDeque

deque1FromList :: [a] -> Deque1 a
deque1FromList = dequeFromList

deque2FromList :: [a] -> Deque2 a
deque2FromList = dequeFromList

takeWith :: (Deque d) => (d a -> Maybe (a, d a)) -> Int -> d a -> [a]
takeWith _ 0 _ = []
takeWith ex n d = case ex d of
    Nothing        -> []
    Just (x, rest) -> x : takeWith ex (n - 1) rest

takeFront :: (Deque d) => Int -> d a -> [a]
takeFront = takeWith popFront

takeBack :: (Deque d) => Int -> d a -> [a]
takeBack = takeWith popBack



prop_order :: (Deque d) => ([Int] -> d Int) -> [Int] -> Bool
prop_order makeDeq xs = takeFront len deq == reverse (takeBack len deq)
    where len = length xs
          deq = makeDeq xs

test :: IO ()
test = do
    quickCheckWith stdArgs { maxSize = 5000 } (prop_order deque1FromList)
    quickCheckWith stdArgs { maxSize = 5000 } (prop_order (foldl (flip putBack) EmptyDeque1))

    quickCheckWith stdArgs { maxSize = 5000 } (prop_order deque2FromList)
    quickCheckWith stdArgs { maxSize = 5000 } (prop_order (foldl (flip putBack) EmptyDeque2))

bench_chunkThrow :: (Deque d) => d Int -> [Int]
bench_chunkThrow = takeBack 10000 . putFrontAll [1..5000]

bench_with benchmark makeDeq = map makeBench [5*1000, 25*1000, 125*1000, 625*1000, 5*625*1000]
    where makeBench size = bench (show size) $ nf benchmark (makeDeq [1..size])

bench_performance1 deq size = takeFront size $ putBackAll [1..size] deq

bench_performance makeDeq = map (makeBench . (* 1000)) [ 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 768]
    where makeBench size = bench (show size) $ nf (bench_performance1 (makeDeq [])) size

bench_popOnly makeDeq = map (makeBench . (* 1000)) [ 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 768]
    where makeBench size = bench (show size) $ nf (takeFront size) (makeDeq [1..size])

bench_popOnlyImpl1 :: [Int] -> [Int]
bench_popOnlyImpl1 chunk = takeFront 100 $ putFrontAll chunk EmptyDeque1
bench_putOnly1 = map (makeBench . (* 1000)) [ 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 768]
    where makeBench size = bench (show size) $ nf (\s -> bench_popOnlyImpl1 [1..s]) size

main = test >>
    defaultMain [ bgroup "asymptotics/deque1" $ bench_with bench_chunkThrow deque1FromList
                , bgroup "asymptotics/deque2" $ bench_with bench_chunkThrow deque2FromList

                , bgroup "performance/deque1" $ bench_performance deque1FromList
                , bgroup "performance/deque2" $ bench_performance deque2FromList

                , bgroup "poponly/deque1" $ bench_popOnly deque1FromList
                , bgroup "putonly/deque1" $ bench_putOnly1
                ]

-- in real: O(1) for both implementations for popFront and popBack, but strange behavior
-- for put* operations (worse then O(log(n))). Presumably the reason is poor memory management
-- by Haskell runtime
--
-- See also https://drive.google.com/folderview?id=0B_1xZaGBxQOmSmF1QnZrX2VTajQ&usp=sharing
