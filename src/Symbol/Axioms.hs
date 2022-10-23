{-# LANGUAGE OverloadedStrings #-}

module Symbol.Axioms where

import Data.Text (pack)
import Dhall

loadAxiomsStr :: String -> IO String
loadAxiomsStr i = input string ("./dhall/inst/" <> pack i <> ".dhall")

loadAxiomsDhall :: String -> IO [String]
loadAxiomsDhall i = lines <$> loadAxiomsStr i
