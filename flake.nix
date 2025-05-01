{
  description = "";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  };

  outputs = { self, nixpkgs, flake-utils } :
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        ghcVersions = [ "ghc910" "ghc9121" ];
        defaultGhcVersion = "ghc910";

        makeOverlay = compilerVersion:
          let
            overrideFile = ./. + "/nix/override-${compilerVersion}.nix";

            overrides =
              if builtins.pathExists overrideFile then
                import overrideFile { inherit pkgs; }
              else
                f: p: { };

            hsOverlay =
              pkgs.haskell.packages.${compilerVersion}.override {
                inherit overrides;
              };

            pkgSrcOverrides = pkgs.haskell.lib.compose.packageSourceOverrides {
              ghc-typelits-proof-assist = ./.;
            };
          in
            hsOverlay.extend pkgSrcOverrides;

        overlays = nixpkgs.lib.attrsets.genAttrs ghcVersions makeOverlay;

        makeDevShell = compilerVersion:
          with overlays.${compilerVersion};
          shellFor {
            name = compilerVersion;
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
