{ pkgs }:
let
  inherit (pkgs.haskell.lib) dontCheck dontBenchmark;

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
in {
  inherit callHackageRevision;
}
