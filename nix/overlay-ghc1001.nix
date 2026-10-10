{ pkgs }:
final: prev:
let
  inherit (pkgs.haskell.lib) dontCheck doJailbreak overrideCabal;
  ghc914 = import ./overlay-ghc9141.nix { inherit pkgs; } final prev;
  forkSource = repo: { rev, hash, subdir ? "" }:
    pkgs.fetchFromGitHub
      {
        owner = "haskell";
        inherit repo rev hash;
      } + pkgs.lib.optionalString (subdir != "") "/${subdir}";
  fromFork = name: source:
    overrideCabal prev.${name} (_: {
      src = forkSource name source;
      # Use the fork's Cabal file, including its updated dependency bounds.
      editedCabalFile = null;
      revision = null;
    });
in
ghc914 // {
  # These build tools do not load target code. Bootstrap them with the stable
  # package set, avoiding a cycle through the alpha's global jailbreak below.
  inherit (pkgs.haskellPackages) jailbreak-cabal hscolour;

  # Hackage bounds generally do not include unreleased GHC boot libraries.
  mkDerivation = args: prev.mkDerivation (args // { jailbreak = true; });

  # Adapt ghc-paths' custom Setup to the alpha's Cabal verbosity API.
  ghc-paths = overrideCabal prev.ghc-paths (old: {
    postPatch = (old.postPatch or "") + ''
      sed -i '/^import Distribution.Simple.Setup$/a import Distribution.Verbosity (mkVerbosity, defaultVerbosityHandles)' Setup.hs
      substituteInPlace Setup.hs \
        --replace-fail '(fromFlag (configVerbosity flags))' \
          '(mkVerbosity defaultVerbosityHandles (fromFlag (configVerbosity flags)))'
    '';
  });

  # jailbreak-cabal leaves this conditional dependency bound unchanged.
  tagged = overrideCabal prev.tagged (old: {
    postPatch = (old.postPatch or "") + ''
      substituteInPlace tagged.cabal --replace-fail "template-haskell >=2.11 && <2.25" "template-haskell >=2.11 && <2.26"
    '';
  });

  unordered-containers = overrideCabal prev.unordered-containers (old: {
    postPatch = (old.postPatch or "") + ''
      substituteInPlace unordered-containers.cabal --replace-fail "template-haskell >=2.16 && <2.25" "template-haskell >=2.16 && <2.26"
    '';
  });


  # time 1.16.0.1 fixes gregorianPaschalMoon; update the old golden result.
  time-compat = overrideCabal prev.time-compat (old: {
    postPatch = (old.postPatch or "") + ''
      substituteInPlace test/main/Test/Calendar/EasterRef.hs \
        --replace-fail "2011, Gregorian: moon, 2011-04-18" "2011, Gregorian: moon, 2011-04-17"
    '';
  });

  # Cabal v3.18.1.0
  Cabal = prev.callCabal2nix "Cabal"
    (pkgs.fetchFromGitHub {
      owner = "haskell";
      repo = "cabal";
      rev = "0de1ddfe447c415eea1ee66bf8036ef3e9787502";
      hash = "sha256-Nt9Qk8GfPauEO+wDNaW64FmRErvS8EocrKfVe3ddOxc=";
    } + "/Cabal")
    { };


  # cabal-syntax v3.18.1.0
  Cabal-syntax = prev.callCabal2nix "Cabal-syntax"
    (pkgs.fetchFromGitHub {
      owner = "haskell";
      repo = "cabal";
      rev = "0de1ddfe447c415eea1ee66bf8036ef3e9787502";
      hash = "sha256-Nt9Qk8GfPauEO+wDNaW64FmRErvS8EocrKfVe3ddOxc=";
    } + "/Cabal-syntax")
    { };

  # cabal-install-solver v3.18.1.0
  cabal-install-solver = prev.callCabal2nix "cabal-install-solver"
    (pkgs.fetchFromGitHub {
      owner = "haskell";
      repo = "cabal";
      rev = "0de1ddfe447c415eea1ee66bf8036ef3e9787502";
      hash = "sha256-Nt9Qk8GfPauEO+wDNaW64FmRErvS8EocrKfVe3ddOxc=";
    } + "/cabal-install-solver")
    { };

  # cabal-install-solver v3.18.1.0
  hooks-exe = prev.callCabal2nix "hooks-exe"
    (pkgs.fetchFromGitHub {
      owner = "haskell";
      repo = "cabal";
      rev = "0de1ddfe447c415eea1ee66bf8036ef3e9787502";
      hash = "sha256-Nt9Qk8GfPauEO+wDNaW64FmRErvS8EocrKfVe3ddOxc=";
    } + "/hooks-exe")
    { };

  # cabal-install v3.18.1.0
  cabal-install = dontCheck (prev.callCabal2nix "cabal-install"
    (pkgs.fetchFromGitHub {
      owner = "haskell";
      repo = "cabal";
      rev = "0de1ddfe447c415eea1ee66bf8036ef3e9787502";
      hash = "sha256-Nt9Qk8GfPauEO+wDNaW64FmRErvS8EocrKfVe3ddOxc=";
    } + "/cabal-install")
    { Cabal-described = null;
      Cabal-QuickCheck = null;
      Cabal-tests = null;
      Cabal-tree-diff = null;
    });

  # hackage-security v0.6.4.0
  hackage-security = prev.callCabal2nix "hackage-security"
    (pkgs.fetchFromGitHub {
      owner = "haskell";
      repo = "hackage-security";
      rev = "c7c6fdab06f152a54005843e2e91968d1f34962c";
      hash = "sha256-RH6RkJsGKFvp9EcB+Lw0qT0Mv+iIa6LoxWUksoaNQcg=";
    } + "/hackage-security")
    { };

  # Waiting for upstream: https://github.com/sol/doctest/pull/493
  doctest = dontCheck
    (prev.callCabal2nix "doctest"
      (pkgs.fetchFromGitHub {
        owner = "sol";
        repo = "doctest";
        rev = "c38f60af631735927a6deca95bf1241991be9605";
        hash = "sha256-Gbl5aMy4oLrZ40N+4aKo8O33DwhV4+FixGJjPCzBEgI=";
      })
      { }
    );

  # GHC 10.0 support pending upstream: https://github.com/martijnbastiaan/doctest-parallel
  doctest-parallel = prev.callCabal2nix "doctest-parallel"
    (forkSource "doctest-parallel" {
      rev = "ec2efedfe93b4ad072450abf0fd594b01a803fb6";
      hash = "sha256-cJz85vz2pATDDLxu/IRkBay224sfXs0v8cTqJrQllNk=";
    })
    { };

  # Waiting for upstream: https://github.com/Lysxia/first-class-families/pull/70
  first-class-families = fromFork "first-class-families" {
    rev = "423173d74b5bb7a1fa706f25a1da386ecaeb5acb";
    hash = "sha256-pFKhRfsU8Mcp/834Cid2iH3reqk+W0HNA25uQqNIE/c=";
  };

  # GHC 10.0 support pending upstream: https://github.com/alanz/ghc-exactprint
  ghc-exactprint = prev.callCabal2nix "ghc-exactprint"
    (forkSource "ghc-exactprint" {
      rev = "6bf758597ee25cd27953528e400747e653013297";
      hash = "sha256-mosyU52dfBntgKRMZ8fwbaS0oZOFvARBZ/YU4tAjHqA=";
    })
    { };

  # Upstream ghc-10.0 branch.
  hashable = prev.callCabal2nix "hashable"
    (pkgs.fetchFromGitHub {
      owner = "haskell-unordered-containers";
      repo = "hashable";
      rev = "c7202c5a061a46753f2cd0b6bd82a40ee22ee401";
      hash = "sha256-h3HWovVuEVJ9bZ1eRSZs3vH2oRkkReLzjQKQ04ZuSLE=";
    })
    { };

  # Waiting for upstream: https://github.com/haskell-hint/hint/pull/187
  hint = fromFork "hint" {
    rev = "cfcf1a5fd1663399f77f73a5866ead21536fc406";
    hash = "sha256-nYo72iEEdaUJw+rRQl463m5ixyVUHdfXiIHvgvvV1H4=";
  };

  # Waiting for upstream: https://github.com/nomeata/inspection-testing/pull/102
  inspection-testing = prev.callCabal2nix "inspection-testing"
    (pkgs.fetchFromGitHub {
      owner = "nomeata";
      repo = "inspection-testing";
      rev = "b38452dda0cb13991bbe6749810fb18f0dbfbbda";
      hash = "sha256-ZJkO9Oljw2W24xztPFkBIJOt9ZJJQekuKU4PZm5XaAM=";
    })
    { };

  # Waiting for upstream: https://github.com/snoyberg/mono-traversable/pull/262
  mono-traversable = fromFork "mono-traversable" {
    rev = "1b7777a104cd326840e945480bcc954b69ad03c8";
    hash = "sha256-3LAIghFufdku8l2GS8TXd+WkC7Y888At13d5DcidHIA=";
    subdir = "mono-traversable";
  };

  # Waiting for upstream: https://github.com/recursion-schemes/recursion-schemes/pull/176
  recursion-schemes = fromFork "recursion-schemes" {
    rev = "9f1384f718f07178d65f71786d47ebae4ec66f80";
    hash = "sha256-2EyhWQVYWYwnUiUSESM8J+3mwcVmwkSpY+NSTALHzMo=";
  };

  # Waiting for upstream: https://github.com/Bodigrim/tasty-inspection-testing/pull/12
  tasty-inspection-testing = prev.callCabal2nix "tasty-inspection-testing"
    (pkgs.fetchFromGitHub {
      owner = "Bodigrim";
      repo = "tasty-inspection-testing";
      rev = "d618bc2bd368ed6e07c2077c20ec2001e2a984d7";
      hash = "sha256-EVfmYJCFK1gOgz8fc1gpPmbzwkbNLuLfnWI2M+3POaM=";
    })
    { };

  # Waiting for upstream: https://github.com/haskell-compat/th-compat/pull/25
  th-compat = prev.callCabal2nix "th-compat"
    (pkgs.fetchFromGitHub {
      owner = "haskell-compat";
      repo = "th-compat";
      rev = "85c922ef33ccba51e25945b3fad0f608857e8a74";
      hash = "sha256-0GEhp1F/J0LXj4+YmR6gUkzxoK6egckSN1StPNe4W9c=";
    })
    { };

  # Waiting for upstream: https://github.com/mgsloan/th-orphans/pull/43
  th-orphans = fromFork "th-orphans" {
    rev = "e2e088696de8b13e758a70c173dc5ff0beff2aeb";
    hash = "sha256-/IuI4PN5Rb8rZ39oHHUFcIbWkzmY8c2mGsY2Th95R8A=";
  };
}
