workspace(name = "plutus")

load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

git_repository(
    name = "io_tweag_rules_haskell",
    remote = "https://github.com/tweag/rules_haskell.git",
    commit = "e134749dbdd926515be1d30495dafd8c72c26a61",
)

load("@io_tweag_rules_haskell//haskell:repositories.bzl", "haskell_repositories")

haskell_repositories()

http_archive(
    name = "io_tweag_rules_nixpkgs",
    strip_prefix = "rules_nixpkgs-0.4.1",
    urls = ["https://github.com/tweag/rules_nixpkgs/archive/v0.4.1.tar.gz"],
)

load(
    "@io_tweag_rules_nixpkgs//nixpkgs:nixpkgs.bzl",
    "nixpkgs_package",
)

nixpkgs_package(
    name = "ghc",
    attribute_path = "ghc",
    nix_file_content = """
      let
        forceDontCheck = false;
        enableProfiling = false;
        enableSplitCheck = true;
        enableDebugging = false;
        enableBenchmarks = true;
        enablePhaseMetrics = true;
        enableHaddockHydra = true;
        fasterBuild = false;
        forceError = true;
        localLib = import ./lib.nix {};
        # This is the stackage LTS plus overrides, plus the plutus
        # packages.
        haskellPackages = let
          errorOverlay = import <errorOverlay> {
            pkgs = localLib.pkgs;
            filter = localLib.isPlutus;
          };
        customOverlays = with localLib.pkgs.lib; optional forceError errorOverlay;
        in localLib.pkgs.callPackage localLib.iohkNix.haskellPackages {
          inherit forceDontCheck enableProfiling enablePhaseMetrics
          enableHaddockHydra enableBenchmarks fasterBuild enableDebugging
          enableSplitCheck customOverlays;
          pkgsGenerated = <pkgsGenerated>;
          filter = localLib.isPlutus;
          filterOverrides = {
            splitCheck = let
              dontSplit = [
                # Broken for things with test tool dependencies
                "wallet-api"
                "plutus-tx"
                # Broken for things which pick up other files at test runtime
                "plutus-playground-server"
              ];
              # Split only local packages not in the don't split list
              doSplit = builtins.filter (name: !(builtins.elem name dontSplit)) localLib.plutusPkgList;
              in name: builtins.elem name doSplit;
          };
          requiredOverlay = <requiredOverlay>;
        };
      in
        {ghc = haskellPackages.ghcWithPackages (ps: [
          haskellPackages.plutus-playground-server
          haskellPackages.plutus-playground-lib
          haskellPackages.plutus-use-cases
        ]);}
      """,
    nix_file_deps = [
        "@//:lib.nix",
        "@//:default.nix",
    ],
    repositories = {
      "pkgsGenerated" : "//:pkgs/default.nix",
      "requiredOverlay" : "//:nix/overlays/required.nix",
      "errorOverlay" : "//:nix/overlays/force-error.nix",
    }
)

nixpkgs_package(
    name = "happy",
    attribute_path = "haskellPackages.happy",
    # For vector example. Just use `attribute_path = haskell.compiler.ghc822`
    # when no extra packages needed.
    nix_file_content = """
      let
        localLib = import ./lib.nix {};
        localPackages = import ./default.nix { pkgs = localLib.pkgs; };
        pkgs = localPackages.pkgs;
      in
        pkgs
      """,
    nix_file_deps = [
        "@//:lib.nix",
        "@//:default.nix",
    ],
    repositories = {
      "pkgsGenerated" : "//:pkgs/default.nix",
      "requiredOverlay" : "//:nix/overlays/required.nix",
      "errorOverlay" : "//:nix/overlays/force-error.nix",
    }
)

nixpkgs_package(
    name = "alex",
    attribute_path = "haskellPackages.alex",
    # For vector example. Just use `attribute_path = haskell.compiler.ghc822`
    # when no extra packages needed.
    nix_file_content = """
      let
        localLib = import ./lib.nix {};
        localPackages = import ./default.nix { pkgs = localLib.pkgs; };
        pkgs = localPackages.pkgs;
      in
        pkgs
      """,
    nix_file_deps = [
        "@//:lib.nix",
        "@//:default.nix",
    ],
    repositories = {
      "pkgsGenerated" : "//:pkgs/default.nix",
      "requiredOverlay" : "//:nix/overlays/required.nix",
      "errorOverlay" : "//:nix/overlays/force-error.nix",
    }
)

nixpkgs_package(
    name = "hlint",
    nix_file_content = """
      let
        localLib = import ./lib.nix {};
        localPackages = import ./default.nix { pkgs = localLib.pkgs; };
        pkgs = localPackages.pkgs;
        script = (import localLib.iohkNix.tests.hlintScript {inherit pkgs;});
      in
        pkgs.stdenv.mkDerivation {
          name = "hlintScript";
          unpackPhase = "true";
          buildInputs = [];
          buildPhase = "";
          installPhase = ''
            mkdir -p $out/bin
            cp ${script} $out/bin/run.sh
          '';
        }
      """,
    nix_file_deps = [
        "@//:lib.nix",
        "@//:default.nix",
    ],
    repositories = {
        "pkgsGenerated" : "//:pkgs/default.nix",
    }
)

nixpkgs_package(
    name = "stylish-haskell",
    nix_file_content = """
      let
        localLib = import ./lib.nix {};
        localPackages = import ./default.nix { pkgs = localLib.pkgs; };
        pkgs = localPackages.pkgs;
        script = (import localLib.iohkNix.tests.stylishHaskellScript {inherit pkgs;});
      in
        pkgs.stdenv.mkDerivation {
          name = "stylishHaskellScript";
          unpackPhase = "true";
          buildInputs = [];
          buildPhase = "";
          installPhase = ''
            mkdir -p $out/bin
            cp ${script} $out/bin/run.sh
          '';
        }
      """,
    nix_file_deps = [
        "@//:lib.nix",
        "@//:default.nix",
    ],
    repositories = {
        "pkgsGenerated" : "//:pkgs/default.nix",
    }
)

nixpkgs_package(
    name = "shellcheck",
    nix_file_content = """
      let
        localLib = import ./lib.nix {};
        localPackages = import ./default.nix { pkgs = localLib.pkgs; };
        pkgs = localPackages.pkgs;
        script = (import localLib.iohkNix.tests.shellcheckScript {inherit pkgs;});
      in
        pkgs.stdenv.mkDerivation {
          name = "shellcheckScript";
          unpackPhase = "true";
          buildInputs = [];
          buildPhase = "";
          installPhase = ''
            mkdir -p $out/bin
            cp ${script} $out/bin/run.sh
          '';
        }
      """,
    nix_file_deps = [
        "@//:lib.nix",
        "@//:default.nix",
    ],
    repositories = {
        "pkgsGenerated" : "//:pkgs/default.nix",
    }
)

register_toolchains("//:ghc")
