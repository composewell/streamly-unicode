{-# LANGUAGE BangPatterns #-}

-- |
-- Module      : Data.Unicode.Internal.NormalizeStream
-- Copyright   : (c) 2020 Composewell Technologies
--
-- License     : BSD-style
-- Maintainer  : streamly@composewell.com
-- Stability   : experimental
--
-- Stream based normalization.

module Data.Unicode.Internal.NormalizeStream
    ( decomposeD
    , partialComposeD
    , onlyComposeRegD
    , normalizeD
    , onlyDecomposeD
    , onlyReorderD
    )
    where

import qualified Data.Unicode.Properties.CombiningClass  as CC
import qualified Data.Unicode.Properties.Compositions    as C
import qualified Data.Unicode.Properties.Decompose       as D
import qualified Data.Unicode.Properties.DecomposeHangul as H

import qualified Streamly.Internal.Data.Stream.StreamD as SD

import Data.Char (chr, ord)
import Fusion.Plugin.Types (Fuse(..))
import Streamly.Internal.Data.Stream.StreamD (Step(..), Stream(..))

data ReBuf = Empty | One !Char | Many !Char !Char ![Char]

{-# INLINE toListR #-}
toListR :: ReBuf -> [Char]
toListR Empty = []
toListR (One x) = [x]
toListR (Many x y z) = x:y:z

{-# INLINE insertIntoReBuf #-}
insertIntoReBuf :: Char -> ReBuf -> ReBuf
insertIntoReBuf c Empty = One c
insertIntoReBuf c (One c0)
    | CC.getCombiningClass c < CC.getCombiningClass c0
    = Many c c0 []
    | otherwise
    = Many c0 c []
insertIntoReBuf c (Many c0 c1 cs)
    | cc < CC.getCombiningClass c0
    = Many c c0 (c1 : cs)
    | cc < CC.getCombiningClass c1
    = Many c0 c (c1 : cs)
    | otherwise
    = Many c0 c1 (cs' ++ (c : cs''))
    where
        cc = CC.getCombiningClass c
        (cs', cs'') = span ((<= cc) . CC.getCombiningClass) cs

{-# ANN type DecomposeState Fuse #-}
data DecomposeState st
    = DecomposedAndNC ![Char] ![Char] st
    | Decomposable ![Char] !ReBuf st
    | EmptyReBufWithYield !Char ![Char] ![Char] st
    | EmptyReBuf ![Char]

{-# ANN type ODState Fuse #-}
data ODState st
    = ODDecomposedAndNC ![Char] st
    | ODDecomposable ![Char] st

{-# ANN type ORState Fuse #-}
data ORState st
    = OREmptyReBuf ![Char]
    | OREmptyReBufWithYield !Char ![Char] st
    | ORHoldReBuf !ReBuf st

{-# INLINE [2] onlyReorderD #-}
onlyReorderD :: Monad m => Stream m Char -> Stream m Char
onlyReorderD (Stream step state) = Stream step' (ORHoldReBuf Empty state)
  where

    {-# INLINE [1] step' #-}
    step' gst (ORHoldReBuf reBuf st) = do
        r <- step gst st
        case r of
            Yield x st1 -> return $ reorder x reBuf st1
            Skip st1 -> return $ Skip $ ORHoldReBuf reBuf st1
            Stop -> return $ Skip $ OREmptyReBuf (toListR reBuf)

    step' gst (OREmptyReBuf (x:xs)) = return $ Yield x $ OREmptyReBuf xs
    step' gst (OREmptyReBuf []) = return Stop

    step' gst (OREmptyReBufWithYield y (x:xs) st) =
        return $ Yield x $ OREmptyReBufWithYield y xs st
    step' gst (OREmptyReBufWithYield y [] st) =
        return $ Yield y $ ORHoldReBuf Empty st

    reorder x Empty st =
        if CC.isCombining x
            then Skip $ ORHoldReBuf (insertIntoReBuf x Empty) st
            else Yield x $ ORHoldReBuf Empty st
    reorder x reBuf st =
        if CC.isCombining x
            then Skip $ ORHoldReBuf (insertIntoReBuf x reBuf) st
            else Skip $ OREmptyReBufWithYield x (toListR reBuf) st

{-# INLINE [2] onlyDecomposeD #-}
onlyDecomposeD :: Monad m => D.DecomposeMode -> Stream m Char -> Stream m Char
onlyDecomposeD mode (Stream step state) = Stream step' (ODDecomposedAndNC [] state)
  where

    {-# INLINE [1] step' #-}
    step' gst (ODDecomposable [] st) = next gst st
    step' gst (ODDecomposable (x:xs) st)
        | D.isDecomposable mode x =
            return $ Skip $ ODDecomposable (D.decomposeChar mode x ++ xs) st
        | otherwise = return $ Yield x $ ODDecomposable xs st

    step' gst (ODDecomposedAndNC (x:xs) st) = return $ Yield x (ODDecomposedAndNC xs st)
    step' gst (ODDecomposedAndNC [] st) = next gst st

    {-# INLINE next #-}
    next gst st = do
        r <- step gst st
        case r of
            Yield x st1 -> return $ check x st1
            Skip st1 -> return $ Skip $ ODDecomposedAndNC [] st1
            Stop -> return Stop

    {-# INLINE check #-}
    check ch st
        | D.isHangul ch =
            let (l, v, t) = D.decomposeCharHangul ch
             in if t == chr H.jamoTFirst
                    then Yield l $ ODDecomposedAndNC [v] st
                    else Yield l $ ODDecomposedAndNC [v, t] st
        | D.isDecomposable mode ch =
            Skip $ ODDecomposable (D.decomposeChar mode ch) st
        | otherwise = Yield ch $ ODDecomposedAndNC [] st

{-# INLINE [2] decomposeD #-}
decomposeD :: Monad m => D.DecomposeMode -> Stream m Char -> Stream m Char
decomposeD mode (Stream step state) = Stream step' (DecomposedAndNC [] [] state)
  where

    {-# INLINE [1] step' #-}
    step' gst (EmptyReBuf (x:xs)) = return $ Yield x $ EmptyReBuf xs
    step' gst (EmptyReBuf []) = return $ Stop

    step' gst (EmptyReBufWithYield x xs [] st) =
        return $ Yield x $ Decomposable xs Empty st
    step' gst (EmptyReBufWithYield x xs (y:ys) st) =
        return $ Yield y (EmptyReBufWithYield x xs ys st)

    step' gst (Decomposable [] rebuf st) = next gst rebuf st
    step' gst (Decomposable (x:xs) rebuf st)
        | D.isDecomposable mode x =
            return $ Skip $ Decomposable (D.decomposeChar mode x ++ xs) rebuf st
        | otherwise = return $ reorder x xs rebuf st

    step' gst (DecomposedAndNC xxs (y:ys) st) = return $ Yield y (DecomposedAndNC xxs ys st)
    step' gst (DecomposedAndNC (x:xs) _ st) = return $ Yield x (DecomposedAndNC xs [] st)
    step' gst (DecomposedAndNC [] _ st) = next gst Empty st

    {-# INLINE next #-}
    next gst rebuf st = do
        r <- step gst st
        case r of
            Yield x st1 -> return $ check x rebuf st1
            Skip st1 -> return $ Skip $ DecomposedAndNC [] (toListR rebuf) st1
            Stop -> return $ Skip $ EmptyReBuf (toListR rebuf)

    {-# INLINE check #-}
    check ch rebuf st
        | D.isHangul ch =
            let (l, v, t) = D.decomposeCharHangul ch
             in if t == chr H.jamoTFirst
                    then Yield l (DecomposedAndNC [v] (toListR rebuf) st)
                    else Yield l (DecomposedAndNC [v, t] (toListR rebuf) st)
        | D.isDecomposable mode ch =
            Skip $ Decomposable (D.decomposeChar mode ch) rebuf st
        | otherwise = reorder ch [] rebuf st

    {-# INLINE reorder #-}
    reorder x xs Empty st = Yield x $ Decomposable xs Empty st
    reorder x xs rebuf st =
        if CC.isCombining x
            then Skip $ Decomposable xs (insertIntoReBuf x rebuf) st
            else Skip $ EmptyReBufWithYield x xs (toListR rebuf) st

data JamoBuf
    = JamoLIndex !Int
    | JamoLV !Char

{-# INLINE fromJamoLIndex #-}
fromJamoLIndex :: Int -> Char
fromJamoLIndex li = chr (D.jamoLFirst + li)

{-# INLINE fromJamoBuf #-}
fromJamoBuf :: JamoBuf -> Char
fromJamoBuf jbuf = case jbuf of
    JamoLIndex li -> fromJamoLIndex li
    JamoLV lv -> lv

{-# ANN type ComposeState Fuse #-}
data ComposeState st
    = ComposeNone st
    | ComposeReg !Char st
    | ComposeJamo !JamoBuf st
    | InitJamoLIndex !Char st -- This is only for efficiency
    | NotJamo !Char st -- This is only for efficiency
    | InitHangulLV !Char st -- This is only for efficiency

-- Assumes every character except hangul characters are fully
-- decomposed and the combining characters are reordered.
{-# INLINE [2] partialComposeD #-}
partialComposeD :: Monad m => Stream m Char -> Stream m Char
partialComposeD (Stream step state) = Stream step' (ComposeNone state)
  where

    {-# INLINE [1] step' #-}
    step' gst (ComposeNone st) = do
        r <- step gst st
        case r of
            Yield x st1 -> return $ composeNone x st1
            Skip st1 -> return $ Skip $ ComposeNone st1
            Stop -> return Stop
    step' gst (ComposeJamo jbuf st) = do
        r <- step gst st
        case r of
            Yield x st1 -> return $ composeJamo jbuf x st
            Skip st1 -> return $ Skip $ ComposeJamo jbuf st1
            Stop -> return Stop
    step' gst (ComposeReg rbuf st) = do
        r <- step gst st
        case r of
            Yield x st1 -> return $ composeReg rbuf x st
            Skip st1 -> return $ Skip $ ComposeReg rbuf st1
            Stop -> return Stop
    step' gst (NotJamo ch st) = return $ notJamo ch st
    step' gst (InitJamoLIndex ch st) = return $ initJamoLIndex ch st
    step' gst (InitHangulLV ch st) = return $ initHangulLV ch st

    {-# INLINE initJamoLIndex #-}
    initJamoLIndex c st =
        case H.jamoLIndex c of
            Just li -> Skip $ ComposeJamo (JamoLIndex li) st
            Nothing -> Yield c $ ComposeNone st

    {-# INLINE initHangulLV #-}
    initHangulLV c st
        | H.isHangulLV c = Skip $ ComposeJamo (JamoLV c) st
        | otherwise = Yield c $ ComposeNone st

    {-# INLINE initReg #-}
    initReg !c st = Skip $ ComposeReg c st

    {-# INLINE composeNone #-}
    composeNone ch st
        | H.isHangul ch = initHangulLV ch st
        | H.isJamo ch = initJamoLIndex ch st
        | otherwise = initReg ch st

    {-# INLINE composeCharJamo #-}
    composeCharJamo (JamoLIndex li) c st =
      case H.jamoVIndex c of
            Just vi ->
                let lvi = li * H.jamoNCount + vi * H.jamoTCount
                    lvch = chr (H.hangulFirst + lvi)
                in Skip $ ComposeJamo (JamoLV lvch) st
            Nothing -> Yield (fromJamoLIndex li) (InitJamoLIndex c st)
    composeCharJamo (JamoLV lv) c st =
        case H.jamoTIndex c of
            Just ti -> Yield (chr ((ord lv) + ti)) (ComposeNone st)
            Nothing -> Yield lv (InitJamoLIndex c st)

    {-# INLINE composeJamo #-}
    composeJamo jbuf ch st
        | H.isJamo ch = composeCharJamo jbuf ch st
        | otherwise = Yield (fromJamoBuf jbuf) (NotJamo ch st)

    -- ~ composeNone
    {-# INLINE notJamo #-}
    notJamo ch st
        | H.isHangul ch = initHangulLV ch st
        | otherwise = initReg ch st

    {-# INLINE composeReg #-}
    composeReg rbuf !ch !st
        | H.isHangul ch = Yield rbuf $ InitHangulLV ch st
        | H.isJamo ch = Yield rbuf $ InitJamoLIndex ch st
        | CC.isCombining ch =
            case C.composePair rbuf ch of
                Just x -> Skip $ ComposeReg x st
                Nothing -> Yield rbuf $ ComposeReg ch st
        -- The first char in RegBuf may or may not be a starter. In
        -- case it is not we rely on composeStarterPair failing.
        | C.isSecondStarter ch
        , Just x <- C.composeStarterPair rbuf ch = Skip $ ComposeReg x st
        | otherwise = Yield rbuf (ComposeReg ch st)


{-# ANN type OCRegState Fuse #-}
data OCRegState st
    = OCRegComposeNone st
    | OCRegComposeReg !Char st
    | OCRegSkip !Char st
    | ELRJPT !Char st -- Only exists to manually add a loop breaker

{-# INLINE [2] onlyComposeRegD #-}
onlyComposeRegD :: Monad m => Stream m Char -> Stream m Char
onlyComposeRegD (Stream step state) = Stream step' (OCRegComposeNone state)
  where

    {-# INLINE [1] step' #-}
    step' gst (OCRegComposeNone st) = do
        r <- step gst st
        case r of
            Yield x st1 -> return $ composeNone x st1
            Skip st1 -> return $ Skip $ OCRegComposeNone st1
            Stop -> return Stop
    step' gst (OCRegComposeReg rbuf st) = do
        r <- step gst st
        case r of
            Yield x st1 -> return $ composeReg rbuf x st
            Skip st1 -> return $ Skip $ OCRegComposeReg rbuf st1
            Stop -> return Stop
    step' gst (OCRegSkip ch st) = return $ Yield ch (OCRegComposeNone st)

    {-# INLINE composeNone #-}
    composeNone ch st
        | H.isHangul ch = Yield ch (OCRegComposeNone st)
        | H.isJamo ch = Yield ch (OCRegComposeNone st)
        | otherwise = Skip $ OCRegComposeReg ch st

    {-# INLINE composeReg #-}
    composeReg rbuf !ch !st
        | H.isHangul ch = Yield rbuf $ OCRegSkip ch st
        | H.isJamo ch = Yield rbuf $ OCRegSkip ch st
        | CC.isCombining ch =
            case C.composePair rbuf ch of
                Just x -> Skip $ OCRegComposeReg x st
                Nothing -> Yield rbuf $ OCRegComposeReg ch st
        -- The first char in RegBuf may or may not be a starter. In
        -- case it is not we rely on composeStarterPair failing.
        | C.isSecondStarter ch
        , Just x <- C.composeStarterPair rbuf ch = Skip $ OCRegComposeReg x st
        | otherwise = Yield rbuf (OCRegComposeReg ch st)


{-

{-# INLINE [2] onlyComposeRegD #-}
onlyComposeRegD :: Monad m => Stream m Char -> Stream m Char
onlyComposeRegD (Stream step state) = Stream step' (OCRegComposeNone state)
  where

    {-# INLINE [1] step' #-}
    step' gst (OCRegComposeNone st) = do
        r <- step gst st
        case r of
            Yield x st1 -> return $ composeNone x st1
            Skip st1 -> return $ Skip $ OCRegComposeNone st1
            Stop -> return Stop
    step' gst (ELRJPT rbuf st) = return $ Skip $ OCRegComposeReg rbuf st
    step' gst (OCRegComposeReg rbuf st) = do
        r <- step gst st
        case r of
            Yield x st1 -> return $ composeReg rbuf x st
            Skip st1 -> return $ Skip $ OCRegComposeReg rbuf st1
            Stop -> return Stop
    step' gst (OCRegSkip ch st) = return $ Yield ch (OCRegComposeNone st)

    {-# INLINE composeNone #-}
    composeNone ch st
        | ich > 0 && ich <= 20 = Yield ch (OCRegComposeNone st)
        | ich > 20 && ich <= 30 = Yield ch (OCRegComposeNone st)
        | otherwise = Skip $ OCRegComposeReg ch st
        where ich = ord ch

    {-# INLINE composeReg #-}
    composeReg !rbuf !ch !st
        | ich > 0 && ich <= 20 = Yield rbuf $ OCRegSkip ch st
        | ich > 20 && ich <= 30 = Yield rbuf $ OCRegSkip ch st
{-
        | ich > 30 && ich <= 40 =
            case ord11 ich of
                Just x -> Skip $ OCRegComposeReg x st
                Nothing -> Yield rbuf $ OCRegComposeReg ch st
        -- The first char in RegBuf may or may not be a starter. In
        -- case it is not we rely on composeStarterPair failing.
        | ord ch > 40
        , Just x <- ord11 ich = Skip $ OCRegComposeReg x st
-}
        | otherwise = Yield rbuf (ELRJPT ch st)
        where ich = ord ch

    ord11 ich | ich < 35 = Nothing
              | otherwise = Just $ chr ich

    ord12 ich | ich > 55 = Nothing
              | otherwise = Just $ chr ich




{-# INLINE [2] onlyComposeRegD #-}
onlyComposeRegD :: Monad m => Stream m Char -> Stream m Char
onlyComposeRegD (Stream step state) = Stream step' (OCRegComposeNone state)
  where

    {-# INLINE [1] step' #-}
    step' gst (OCRegComposeNone st) = do
        r <- step gst st
        case r of
            Yield x st1 -> return $ composeNone x st1
            Skip st1 -> return $ Skip $ OCRegComposeNone st1
            Stop -> return Stop
    step' gst (ELRJPT ch st) = return $ Skip $ OCRegComposeReg ch st
    step' gst (OCRegComposeReg rbuf st) = do
        r <- step gst st
        case r of
            Yield x st1 -> return $ composeReg rbuf x st
            Skip st1 -> return $ Skip $ OCRegComposeReg rbuf st1
            Stop -> return Stop
    step' gst (OCRegSkip ch st) = return $ Yield ch (OCRegComposeNone st)

    {-# INLINE composeNone #-}
    composeNone ch st
        | ich > 0 && ich <= 20 = Yield ch (OCRegComposeNone st)
        | ich > 20 && ich <= 30 = Yield ch (OCRegComposeNone st)

        | otherwise = Skip $ OCRegComposeReg ch st
        where ich = ord ch

    {-# INLINE composeReg #-}
    composeReg !rbuf !ch !st
        | ich > 0 && ich <= 20 = Yield rbuf $ OCRegSkip ch st
        | ich > 20 && ich <= 30 = Yield rbuf $ OCRegSkip ch st
        | ich > 30 && ich <= 40 =
            case ord11 ich of
                Just x -> Skip $ ELRJPT x st
                Nothing -> Yield rbuf $ ELRJPT ch st
        -- The first char in RegBuf may or may not be a starter. In
        -- case it is not we rely on composeStarterPair failing.
        | ich > 40 && ich <= 60
        , Just x <- ord12 ich  = Skip $ ELRJPT x st
        | otherwise = Yield rbuf $ ELRJPT ch st
        where ich = ord ch

    ord11 ich | ich < 35 = Nothing
              | otherwise = Just $ chr ich

    ord12 ich | ich > 55 = Nothing
              | otherwise = Just $ chr ich
-}


normalizeD :: D.DecomposeMode -> Stream m Char -> Stream m Char
normalizeD = undefined
