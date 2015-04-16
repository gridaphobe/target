with (import <nixpkgs> {}).pkgs;

let hp = haskell-ng.packages.ghc7101.override {
           overrides = config.haskellPackageOverrides or (self: super: {});
         };
in

(hp.callPackage ./. {}).env
