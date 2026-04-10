{ pkgs, lib }: final: prev: {
  HTTP = pkgs.haskell.lib.dontCheck prev.HTTP_4000_5_0;
  Cabal = prev.Cabal_3_16_1_0;
  Cabal-syntax = prev.Cabal-syntax_3_16_1_0;
}
