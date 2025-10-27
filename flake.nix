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
        lib = import ./nix/lib.nix { inherit pkgs; };

        ghcVersions = [ "ghc910" "ghc9121" ];
        defaultGhcVersion = "ghc910";

        makeOverlay = compilerVersion:
          let
            hsPkgs = pkgs.haskell.packages.${compilerVersion};

            ghc-tcplugin-api =
              lib.callHackageRevision hsPkgs {
                pkg = "ghc-tcplugin-api";
                ver = "0.18.1.0";
                revision = "0";
                sha256 = "sha256-VE1IDANndcIswnmdgkEwYIqdnFIhwqe12hDPxpLpSQo=";
                editedCabalFile = "sha256-KJ2NO27XM6kzqlGNSD3V+76WQg452ppYhidXpvqkdso=";
              };

            overrides = _: _: {
              inherit ghc-tcplugin-api;
            };

            ghcOverrideFile = ./. + "/nix/override-${compilerVersion}.nix";

            ghcOverrides =
              if builtins.pathExists ghcOverrideFile then
                import ghcOverrideFile { inherit pkgs lib; }
              else
                f: p: { };

            pkgSrcOverrides = pkgs.haskell.lib.compose.packageSourceOverrides {
              ghc-typelits-proof-assist = ./.;
            };
          in
            ((hsPkgs.extend overrides).extend ghcOverrides).extend pkgSrcOverrides;

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
        x = overlays;
        devShells = shells // { default = shells.${defaultGhcVersion}; };
      });
}
