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
        pkgs0 = nixpkgs.legacyPackages.${system};

        ghcVersions = [ "ghc9103" "ghc9124" "ghc9141" "ghc1001"];
        defaultGhcVersion = "ghc9103";

        inherit (pkgs0.haskell.lib) dontCheck doJailbreak;

        makeOverlay = compilerVersion: final: prev:
          let
            ghcOverlayFile = ./. + "/nix/overlay-${compilerVersion}.nix";
            ghcOverlay =
              if builtins.pathExists ghcOverlayFile then
                import ghcOverlayFile { pkgs = prev; }
              else
                f: p: {};

            pkgSrcOverlay = final: prev: {
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
              ghc-typelits-extra = doJailbreak ( dontCheck (
                prev.callCabal2nix "ghc-typelits-extra"
                  ghc-typelits-extra {}
              ));

              ghc-typelits-proof-assist =
                prev.callCabal2nix "ghc-typelits-proof-assist"
                  ./. {};
            };

            haskellOverlays =
              prev.lib.composeManyExtensions [
                pkgSrcOverlay
                ghcOverlay
              ];
          in
            {
              "hsPkgs-${compilerVersion}" =
                if compilerVersion == "ghc1001" then
                  let
                    ghc100Packages = (prev.haskell.packages.ghc9141.override {
                      ghc = import ./nix/ghc-10.0.nix { pkgs = prev; };
                      buildHaskellPackages = ghc100Packages;
                    }).extend haskellOverlays;
                  in
                    ghc100Packages
                else
                  prev.haskell.packages.${compilerVersion}.extend haskellOverlays;
            };

        overlays = nixpkgs.lib.attrsets.genAttrs ghcVersions makeOverlay;

        pkgs =
          nixpkgs.legacyPackages.${system}.extend (
            nixpkgs.lib.composeManyExtensions (
              nixpkgs.lib.attrsets.attrValues overlays));

        makeDevShell = compilerVersion:
          with pkgs."hsPkgs-${compilerVersion}";
          shellFor {
            name = {
              "ghc9103" = "GHC 9.10.3";
              "ghc9124" = "GHC 9.12.4";
              "ghc9141" = "GHC 9.14.1";
              "ghc1001" = "GHC 10.0.1 alpha1";
            }."${compilerVersion}";
            packages = p: [
              # project packages
              p.ghc-typelits-proof-assist
            ];
            nativeBuildInputs = [
              # Haskell dependencies
              cabal-install
            ];
          };

        shells = pkgs0.lib.attrsets.genAttrs ghcVersions makeDevShell;
      in {
        devShells = shells // { default = shells.${defaultGhcVersion}; };
      });
}
