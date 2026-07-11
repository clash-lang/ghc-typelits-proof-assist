{
  description = "";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    ghc-tcplugin-api = {
      url = "github:sheaf/ghc-tcplugin-api";
      flake = false;
    };
    ghc-typelits-natnormalise = {
      url = "github:clash-lang/ghc-typelits-natnormalise";
      flake = false;
    };
    ghc-typelits-knownnat = {
      url = "github:clash-lang/ghc-typelits-knownnat";
      flake = false;
    };
    ghc-typelits-extra = {
      url = "github:clash-lang/ghc-typelits-extra";
      flake = false;
    };
  };

  outputs =
  { self
  , nixpkgs
  , flake-utils
  , ghc-tcplugin-api
  , ghc-typelits-natnormalise
  , ghc-typelits-knownnat
  , ghc-typelits-extra
  }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        lib = import ./nix/lib.nix { inherit pkgs; };

        ghcVersions = [ "ghc9103" "ghc9124" "ghc9141"];
        defaultGhcVersion = "ghc9103";

        inherit (pkgs.haskell.lib) dontCheck;

        makeOverlay = compilerVersion:
          let
            hsPkgs = pkgs.haskell.packages.${compilerVersion};
            ghcOverrideFile = ./. + "/nix/override-${compilerVersion}.nix";

            ghcOverrides =
              if builtins.pathExists ghcOverrideFile then
                import ghcOverrideFile { inherit pkgs lib; }
              else
                f: p: {};

            pkgSrcOverrides = final: prev: {
              ghc-tcplugin-api = dontCheck (
                prev.callCabal2nix "ghc-tcplugin-api"
                  ghc-tcplugin-api {}
              );
              ghc-typelits-natnormalise = dontCheck (
                prev.callCabal2nix "ghc-typelits-natnormalise"
                  ghc-typelits-natnormalise {}
              );
              ghc-typelits-knownnat = dontCheck (
                prev.callCabal2nix "ghc-typelits-knownnat"
                  ghc-typelits-knownnat {}
              );
              ghc-typelits-extra = dontCheck (
                prev.callCabal2nix "ghc-typelits-extra"
                  ghc-typelits-extra {}
              );

              ghc-typelits-proof-assist =
                prev.callCabal2nix "ghc-typelits-proof-assist"
                  ./. {};
            };
          in
            (hsPkgs.extend ghcOverrides).extend pkgSrcOverrides;

        overlays = nixpkgs.lib.attrsets.genAttrs ghcVersions makeOverlay;

        makeDevShell = compilerVersion:
          with overlays.${compilerVersion};
          shellFor {
            name = {
              "ghc9103" = "GHC 9.10.3";
              "ghc9124" = "GHC 9.12.4";
              "ghc9141" = "GHC 9.14.1";
            }."${compilerVersion}";
            packages = p: [
              # project packages
              p.ghc-typelits-proof-assist
            ];
            nativeBuildInputs = [
              # Haskell dependencies
              cabal-install

              # other dependencies
              pkgs.coq
              pkgs.rocqPackages.stdlib
            ];
          };

        shells = pkgs.lib.attrsets.genAttrs ghcVersions makeDevShell;
      in {
        devShells = shells // { default = shells.${defaultGhcVersion}; };
      });
}
