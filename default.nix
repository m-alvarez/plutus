########################################################################
# default.nix -- The top-level nix build file for plutus.
#
# This file defines an attribute set of packages.
#
# It contains:
#
#   - pkgs -- the nixpkgs set that the build is based on.
#   - haskellPackages.* -- the package set based on stackage
#   - haskellPackages.ghc -- the compiler
#   - localPackages -- just local packages
#
#   - tests -- integration tests and linters suitable for running in a
#              sandboxed build environment
#
# Other files:
#   - shell.nix   - dev environment, used by nix-shell / nix run.
#   - release.nix - the Hydra jobset.
#   - lib.nix     - the localLib common functions.
#   - nix/*       - other nix code modules used by this file.
#
# See also:
#   - TODO: documentation links
#
########################################################################

let
  localLib = import ./lib.nix;
in
{ system ? builtins.currentSystem
, config ? {}  # The nixpkgs configuration file

# Use a pinned version nixpkgs.
, pkgs ? localLib.importPkgs { inherit system config; }

# Disable running of tests for all local packages.
, forceDontCheck ? false

# Enable profiling for all haskell packages.
# Profiling slows down performance by 50% so we don't enable it by default.
, enableProfiling ? false

# Enable separation of build/check derivations.
, enableSplitCheck ? true

# Keeps the debug information for all haskell packages.
, enableDebugging ? false

# Build (but don't run) benchmarks for all local packages.
, enableBenchmarks ? true

# Overrides all nix derivations to add build timing information in
# their build output.
, enablePhaseMetrics ? true

# Overrides all nix derivations to add haddock hydra output.
, enableHaddockHydra ? true

# Disables optimization in the build for all local packages.
, fasterBuild ? false

}:

with pkgs.lib;

let
  src = localLib.cleanSourceHaskell ./.;
  # This is the stackage LTS plus overrides, plus the plutus
  # packages.
  haskellPackages = pkgs.callPackage localLib.iohkNix.haskellPackages {
    inherit forceDontCheck enableProfiling enablePhaseMetrics enableHaddockHydra
      enableBenchmarks fasterBuild enableDebugging enableSplitCheck;
      pkgsGenerated = ./pkgs;
      filter = localLib.isPlutus;
      requiredOverlay = ./nix/overlays/required.nix;
      ghc = pkgs.haskell.compiler.ghc843;
  };
  playgroundGhc = pkgs.haskell.packages.ghc843.ghcWithPackages (ps: [
    haskellPackages.plutus-playground-server
    haskellPackages.plutus-use-cases
  ]);
  #purescriptNixpkgs = import (localLib.iohkNix.fetchNixpkgs ./plutus-playground/plutus-playground-client/nixpkgs-src.json) {};
  packages = self: ( rec {
    inherit pkgs;
    inherit haskellPackages;

    localPackages = localLib.getPackages {
      inherit (self) haskellPackages; filter = localLib.isPlutus;
    };
    tests = {
      shellcheck = pkgs.callPackage localLib.iohkNix.tests.shellcheck { inherit src; };
      hlint = pkgs.callPackage localLib.iohkNix.tests.hlint {
        inherit src;
        # TODO: when plutus-ir passes hlint, remove this.
        projects = localLib.remove "plutus-ir" localLib.plutusPkgList;
      };
      stylishHaskell = pkgs.callPackage localLib.iohkNix.tests.stylishHaskell {
        inherit (self.haskellPackages) stylish-haskell;
          inherit src;
      };
    };
    plutus-server-invoker = pkgs.stdenv.mkDerivation {
                          name = "plutus-server-invoker";
                          unpackPhase = "true";
                          buildInputs = [ playgroundGhc haskellPackages.plutus-playground-server pkgs.makeWrapper ];
                          buildPhase = ''
                                     # We need to provide the ghc interpreter (hint) with the location of the ghc lib dir and the package db
                                     mkdir $out
                                     ln -s ${haskellPackages.plutus-playground-server}/bin/plutus-playground-server $out/plutus-playground-server
                                     wrapProgram $out/plutus-playground-server --set GHC_LIB_DIR "${playgroundGhc}/lib/ghc-8.4.3" --set GHC_PACKAGE_PATH "${playgroundGhc}/lib/ghc-8.4.3/package.conf.d"
                          '';
                          installPhase = "echo nothing to install";
        };
    plutus-playground-purescript = pkgs.stdenv.mkDerivation {
        name = "plutus-playground-purescript";
        unpackPhase = "true";
        buildInputs = [ haskellPackages.plutus-playground-server ];
        buildPhase = ''
        mkdir $out
        ${haskellPackages.plutus-playground-server}/bin/plutus-playground-server psgenerator $out
        '';
        installPhase = "echo nothing to install";
    };
    plutus-core-spec = pkgs.callPackage ./plutus-core-spec {};
    plutus-playground-client = pkgs.callPackage ./plutus-playground/plutus-playground-client { pkgs = purescriptNixpkgs; psSrc = plutus-playground-purescript; };
    inherit (pkgs) stack2nix;
    purescriptNixpkgs = import (builtins.fetchTarball 
      { url = "https://github.com/NixOS/nixpkgs/archive/889d618f16ef2fc3110e1a8a6b2014109ae49e41.tar.gz"; 
        sha256 = "14jqmpp3nkn8rk310mws1a3fhq72b0wnn5dnc1qcykva4pkc5fda"; 
        name = "purescriptNixpkgs";
      }) {};
  });

in
  # The top-level package set
  pkgs.lib.makeScope pkgs.newScope packages
