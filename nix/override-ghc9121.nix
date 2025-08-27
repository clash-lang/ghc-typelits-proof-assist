{ pkgs }:
let
  inherit (pkgs.haskell.lib) dontCheck dontBenchmark;

  cabalSrc = pkgs.fetchFromGitHub {
    owner  = "haskell";
    repo   = "cabal";
    rev    = "15d9d9765cdd0e8870ea8b0f1c63835f55fdd03f";
    sha256 = "sha256-foWu3wvt940VmhgHf7Iz1ZlUQ42bPcn7qO1//rFV9Lk=";
  };
  pluginExtraSrc = pkgs.fetchFromGitHub {
    owner  = "clash-lang";
    repo   = "ghc-tcplugins-extra";
    rev    = "64a64b3f5ac61b141b61264f95de40cdfcbe6d20";
    sha256 = "sha256-VPV2a1ozRP10Xft1Gxly5K1QwO3WCRYVXAXCrNcwRjw=";
  };
  pluginTLNatNormaliseSrc = pkgs.fetchFromGitHub {
    owner  = "clash-lang";
    repo   = "ghc-typelits-natnormalise";
    rev    = "99cc658c9547baca1baf1de2a66448abf455e253";
    sha256 = "sha256-H+KoZQmvMju1/8sLzxKqxEy991PwRplvIaAJgwia304=";
  };
  pluginTLKnownNatSrc = pkgs.fetchFromGitHub {
    owner  = "clash-lang";
    repo   = "ghc-typelits-knownnat";
    rev    = "16393073f52866f8172ddbd8bbd76bbfdc4600d9";
    sha256 = "sha256-0lIIRQryeqNHYhMdwxSPPLKJ/skwOOWNISqfi5WKX+E=";
  };
  pluginTLExtraSrc = pkgs.fetchFromGitHub {
    owner  = "clash-lang";
    repo   = "ghc-typelits-extra";
    rev    = "5b257704f21110fb5f1faa32a679025966144635";
    sha256 = "sha256-puyzSyfhXA5ICdoC3NeiPpQqCKdw+Nb4I+IFRcUoPnM=";
  };

  callHackageRevision = oldpkgs: args:
    let orev = drv: {
          revision = args.revision;
          editedCabalFile = args.editedCabalFile;
        };
        meta = oldpkgs.callHackageDirect {
          pkg = args.pkg;
          ver = args.ver;
          sha256 = args.sha256;
        } {};
     in dontCheck (dontBenchmark (
          pkgs.haskell.lib.compose.overrideCabal orev meta
        ));

  fromCabalSources = oldpkgs: pkg: dontCheck ( dontBenchmark (
    oldpkgs.callCabal2nix pkg (cabalSrc + "/" + pkg) {}
  ));
in final: prev: {
  cabal-install    = fromCabalSources prev "cabal-install";
  Cabal-described  = fromCabalSources prev "Cabal-described";
  Cabal-QuickCheck = fromCabalSources prev "Cabal-QuickCheck";
  Cabal-tests      = fromCabalSources prev "Cabal-tests";
  Cabal-tree-diff  = fromCabalSources prev "Cabal-tree-diff";

  hashable  = dontCheck (prev.callHackage "hashable" "1.5.0.0" {});
  th-compat = dontCheck (prev.callHackage "th-compat" "0.1.6" {});

  ghc-tcplugins-extra = dontCheck (dontBenchmark (
    prev.callCabal2nix "ghc-tcplugins-extra" pluginExtraSrc {}
  ));
  ghc-typelits-natnormalise = dontCheck (dontBenchmark (
    prev.callCabal2nix "ghc-typelits-natnormalise" pluginTLNatNormaliseSrc {}
  ));
  ghc-typelits-knownnat = dontCheck (dontBenchmark (
    prev.callCabal2nix "ghc-typelits-knownnat" pluginTLKnownNatSrc {}
  ));
  ghc-typelits-extra = dontCheck (dontBenchmark (
    prev.callCabal2nix "ghc-typelits-extra" pluginTLExtraSrc {}
  ));

  ed25519 = callHackageRevision prev {
    pkg             = "ed25519";
    ver             = "0.0.5.0";
    revision        = "9";
    sha256          = "sha256-x/8O0KFlj2SDVDKp3IPIvqklmZHfBYKGwygbG48q5Ig=";
    editedCabalFile = "sha256-8VUN2+O1PxCHoDVmc2QBFGCJbMKx/zKLUhwF7Vlzu3g=";
  };
  lukko = callHackageRevision prev {
    pkg             = "lukko";
    ver             = "0.1.2";
    revision        = "1";
    sha256          = "sha256-7B7SocaLDVqQZ3lcUZQgVZJ5S3vSbAEwulbji2yJP6M=";
    editedCabalFile = "sha256-gzSo2BDjheHcFCPcApRdqqHxqboFjlIn8aMhHkiCyig=";
  };
  cryptohash-sha256 = callHackageRevision prev {
    pkg             = "cryptohash-sha256";
    ver             = "0.11.102.1";
    revision        = "6";
    sha256          = "sha256-DRfERrluYyO0vyovBSZ5gsIIZZwwarNIPdw0r70oQmY=";
    editedCabalFile = "sha256-Dp3izM4mHnpbAn6EL29H9Q6w5gWaDemKVHn3WqgWQQc=";
  };
  HTTP = callHackageRevision prev {
    pkg             = "HTTP";
    ver             = "4000.4.1";
    revision        = "5";
    sha256          = "sha256-FquFoyK9pdsIOfICtrZ6G1uCQlDgod9CKhhTWCkF1d0=";
    editedCabalFile = "sha256-da2gO9LSt0cxnjiHelW/i+Up20UgoH1OX/vSTF6FDcs=";
  };
  hackage-security = callHackageRevision prev {
    pkg             = "hackage-security";
    ver             = "0.6.2.6";
    revision        = "5";
    sha256          = "sha256-B61sYNOJXszHBA4JWFP5UZBp3UcJk9ufnGE3Li5rQNI=";
    editedCabalFile = "sha256-+F9vHvVdH5F5Xyx8R22zb9eu21XId9R/KkQR8BUQQKk=";
  };

  zlib = prev.zlib_0_7_1_0;
}
