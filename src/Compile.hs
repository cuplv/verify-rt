{-# LANGUAGE GADTs #-}

module Compile where

import ALang
import Symbol

data Ref a where
  EmptyRef :: Ref a
  IsLb :: Ref Int
  IsUb :: Ref Int
  IsLit :: a -> Ref a
  RefAdd :: Ref Int -> Ref Int -> Ref Int
  RefSub :: Ref Int -> Ref Int -> Ref Int
  IsRight :: Ref b -> Ref (Either a b)

data Request
  = Request { lowReq :: Maybe Int
            , highReq :: Maybe Int
            , addCap :: (Int, Int) -> Maybe Int
            , subCap :: (Int, Int) -> Maybe Int
            }

emptyRequest = Request { lowReq = Nothing
                       , highReq = Nothing
                       , addCap = const (Just 0)
                       , subCap = const (Just 0)
                       }

data Transact a
  = Transact [(Request, Ref a, (Maybe Int, Maybe Int) -> (Int, a))]

-- compile :: (Avs a, Avs b) => ALang a b -> Ref a -> Transact b
-- compile m = case m of
--   CheckAtLeast lr ->
--     let a1q = emptyRequest { lowReq = Just lr }
--         a1r = IsRight IsLb
--         a1f = \(Just lb,_) -> (0, Right lb)
--     in const $ Transact [(a1q,a1r,a1f)
--                         ,(emptyRequest, EmptyRef, const (0, Left ()))
--                         ]
