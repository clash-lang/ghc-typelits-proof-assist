{
  description = "";
  
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  };
  outputs = { self, nixpkgs, flake-utils } : 
    flake-utils.lib.eachDefaultSystem (system: 
      let pkgs = nixpkgs.legacyPackages.${system}; 
          myHsPkgs = pkgs.haskell.packages.ghc98.extend
            (pkgs.haskell.lib.compose.packageSourceOverrides {
              ghc-typelits-proof-assist = ./.;
            });
      in 
      {
        devShells.default = myHsPkgs.shellFor {
          packages = p: [ p.ghc-typelits-proof-assist ];
          nativeBuildInputs = with myHsPkgs; [ cabal-install ];
        };
      });
}
