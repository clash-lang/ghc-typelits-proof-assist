{ inputs, ... }:
{
  imports = [
    inputs.haskell-flake.flakeModule
  ];
  perSystem = { self', lib, config, pkgs, ... }: {
    # Our only Haskell project. You can have multiple projects, but this template
    # has only one.
    # See https://github.com/srid/haskell-flake/blob/master/example/flake.nix
    haskellProjects.default = {
      # To avoid unnecessary rebuilds, we filter projectRoot:
      # https://community.flake.parts/haskell-flake/local#rebuild
      projectRoot = builtins.toString (lib.fileset.toSource {
        root = ../..;
        fileset = lib.fileset.unions [
          ../../src
          ../../tests
          ../../prototype-ghc-prover.cabal
          ../../LICENSE
          ../../README.md
        ];
      });

      # The base package set (this value is the default)
      basePackages = pkgs.haskell.packages.ghc98;

      # Packages to add on top of `basePackages`
      packages = {
        # Add source or Hackage overrides here
        # (Local packages are added automatically)
        /*
        aeson.source = "1.5.0.0" # Hackage version
        shower.source = inputs.shower; # Flake input
        */
        # primitive.source = "0.9.0.0";
      };

      # Add your package overrides here
      settings = {
        # ghc = { super, ... }: { custom = _: super.ghc_9_10_1; };
        # ghc-lib-parser = { super, ... }: { custom = _: super.ghc-lib-parser_9_10_1_20240511; };
        # tar = { super, ... }: { custom = _: super.tar_0_6_3_0; };
        # commutative-semigroups = { super, ... }: { custom = _: super.commutative-semigroups_0_2_0_1; };
        # primitive = { super, ... }: { custom = _: super.primitive_0_9_0_0; };
        /*
        haskell-template = {
          haddock = false;
        };
        aeson = {
          check = false;
        };
        */
      };

      # Development shell configuration
      devShell = {
        hlsCheck.enable = false;
      };

      # What should haskell-flake add to flake outputs?
      autoWire = [ "packages" "apps" "checks" ]; # Wire all but the devShell
    };

    # Default package & app.
    packages.default = self'.packages.haskell-template;
    apps.default = self'.apps.haskell-template;
  };
}
