with (import <nixpkgs> {}).pkgs;

let hp = haskell.packages.ghc784.override {
           overrides = config.haskellPackageOverrides or (self: super: {});
         };
in

(hp.callPackage ./. {}).env
