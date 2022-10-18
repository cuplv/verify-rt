{-# LANGUAGE OverloadedStrings #-}

module Symbol.Axioms where

import Data.Text (pack)
import Dhall

loadAxioms' :: String -> IO String
loadAxioms' i = input string ("./dhall/inst/" <> pack i <> ".dhall")

loadAxioms :: String -> IO [String]
loadAxioms i = lines <$> loadAxioms' i
