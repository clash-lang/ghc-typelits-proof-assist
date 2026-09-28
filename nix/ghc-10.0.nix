{ pkgs }:
pkgs.callPackage
  (import (pkgs.path + "/pkgs/development/compilers/ghc/common-hadrian.nix") {
    version = "10.0.0.20260917";
    url = "https://downloads.haskell.org/ghc/10.0.1-alpha1/ghc-10.0.0.20260917-src.tar.xz";
    sha256 = "sha256-pd862LmjqCeZRR9/Yt88Hqg/05L4lPoriF9tUCFgQEk=";
  })
  {
    bootPkgs = pkgs.haskell.packages.ghc9124;
    inherit (pkgs.python3Packages) sphinx;
    inherit (pkgs.darwin) xattr autoSignDarwinBinariesHook;
    llvmPackages = pkgs.llvmPackages_20;
    buildTargetLlvmPackages = pkgs.llvmPackages_20;
  }
