-- Some interesting examples using the instances of datatypes, rdatatypes and mdatatypes

requires qprelude
requires datatypes
requires rdatatypes
requires mdatatypes

headb :: List Bool -> Maybe Bool
headb as = head (fmap as not)
