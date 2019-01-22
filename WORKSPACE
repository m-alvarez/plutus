workspace(name = "plutus")

load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

git_repository(
    name = "io_tweag_rules_haskell",
    remote = "https://github.com/tweag/rules_haskell.git",
    commit = "316f858fc6aebf9140cfebf6befe97b3bd55e7c0",
)

load("@io_tweag_rules_haskell//haskell:repositories.bzl", "haskell_repositories")

haskell_repositories()

http_archive(
    name = "io_tweag_rules_nixpkgs",
    strip_prefix = "rules_nixpkgs-0.5.1",
    urls = ["https://github.com/tweag/rules_nixpkgs/archive/v0.5.1.tar.gz"],
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

############################################################ Font End Stuff ######################################################3

# download the archive:
local_repository(
    name = "bazel_rules_purescript",
    path = "plutus-playground/plutus-playground-client/rules_purescript-master"
)

load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

git_repository(
    name = "bazel_skylib",
    remote = "https://github.com/bazelbuild/bazel-skylib.git",
    tag = "0.6.0"
)

# load the purescript rules and functions:
load("@bazel_rules_purescript//purescript:purescript.bzl", "purescript_toolchain", "purescript_dep")

http_archive(
    name = "io_bazel_rules_sass",
    # Make sure to check for the latest version when you install
    url = "https://github.com/bazelbuild/rules_sass/archive/1.15.2.zip",
    strip_prefix = "rules_sass-1.15.2",
    sha256 = "96cedd370d8b87759c8b4a94e6e1c3bef7c17762770215c65864d9fba40f07cf",
)

# Fetch required transitive dependencies. This is an optional step because you
# can always fetch the required NodeJS transitive dependency on your own.
load("@io_bazel_rules_sass//:package.bzl", "rules_sass_dependencies")
rules_sass_dependencies()

# Setup repositories which are needed for the Sass rules.
load("@io_bazel_rules_sass//:defs.bzl", "sass_repositories")
sass_repositories()

git_repository(
    name = "build_bazel_rules_nodejs",
    remote = "https://github.com/bazelbuild/rules_nodejs.git",
    tag = "0.16.5", # check for the latest tag when you install
)

load("@build_bazel_rules_nodejs//:package.bzl", "rules_nodejs_dependencies")
rules_nodejs_dependencies()

load("@build_bazel_rules_nodejs//:defs.bzl", "node_repositories", "yarn_install")

node_repositories(package_json = ["//plutus-playground/plutus-playground-client:package.json"])

yarn_install(
    name = "npm",
    package_json = "//plutus-playground/plutus-playground-client:package.json",
    yarn_lock = "//plutus-playground/plutus-playground-client:yarn.lock",
)

# TODO: I can't work out how to create a sass_library out of the npm repo so this
# will reference bootstrap source directly, this is bad as it can get out of sync
# with the npm version
BOOTSTRAP_SCSS_BUILD_FILE = """
load("@io_bazel_rules_sass//sass:sass.bzl",
     "sass_binary",
     "sass_library",
)

sass_library(
    name = "bootstrap_sass",
    srcs = glob(["**/_*.scss"]),
    visibility = ["//visibility:public"],
)
"""

http_archive(
    name = "com_github_bootstrap",
    url = "https://registry.yarnpkg.com/bootstrap/-/bootstrap-4.1.3.tgz#0eb371af2c8448e8c210411d0cb824a6409a12be",
    strip_prefix = "package/scss",
    build_file_content = BOOTSTRAP_SCSS_BUILD_FILE,
)

# downloads the `purs` command:
purescript_toolchain()

# hand-added
purescript_dep(name = "purescript-ace-halogen"
              ,url = "https://github.com/slamdata/purescript-ace-halogen/archive/v7.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-ace-halogen-7.0.0"
              ,deps = ["@purescript-halogen//:pkg",
                       "@purescript-random//:pkg",
                       "@purescript-ace//:pkg"])

purescript_dep(name = "purescript-halogen-echarts"
              ,url = "https://github.com/slamdata/purescript-halogen-echarts/archive/v14.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-halogen-echarts-14.0.0"
              ,deps = ["@purescript-halogen//:pkg",
                       "@purescript-halogen-css//:pkg",
                       "@purescript-echarts//:pkg"])

purescript_dep(name = "purescript-ace"
              ,url = "https://github.com/slamdata/purescript-ace/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-ace-4.0.0"
              ,deps = ["@purescript-nullable//:pkg",
                       "@purescript-dom//:pkg",
                       "@purescript-eff//:pkg"])

purescript_dep(name = "purescript-undefinable"
              ,url = "https://github.com/ethul/purescript-undefinable/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-undefinable-3.0.0"
              ,deps = ["@purescript-maybe//:pkg",
                       "@purescript-functions//:pkg"])
purescript_dep(name = "purescript-strings"
              ,url = "https://github.com/purescript/purescript-strings/archive/v3.5.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-strings-3.5.0"
              ,deps = ["@purescript-either//:pkg"
                      ,"@purescript-gen//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-partial//:pkg"
                      ,"@purescript-unfoldable//:pkg"
                      ,"@purescript-arrays//:pkg"]
               ,patches = ["//plutus-playground/plutus-playground-client:purescript-strings.patch"])
purescript_dep(name = "purescript-dom"
              ,url = "https://github.com/purescript-contrib/purescript-dom/archive/v4.12.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-dom-4.12.0"
              ,deps = ["@purescript-arraybuffer-types//:pkg"
                      ,"@purescript-datetime//:pkg"
                      ,"@purescript-enums//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-foreign//:pkg"
                      ,"@purescript-js-date//:pkg"
                      ,"@purescript-media-types//:pkg"
                      ,"@purescript-nullable//:pkg"
                      ,"@purescript-prelude//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"]
               ,patches = ["//plutus-playground/plutus-playground-client:purescript-dom.patch"])

# Auto Generated
purescript_dep(name = "purescript-data-default"
              ,url = "https://github.com/nkly/purescript-data-default/archive/0.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-data-default-0.1.0"
              ,deps = [])
purescript_dep(name = "purescript-affjax"
              ,url = "https://github.com/slamdata/purescript-affjax/archive/v5.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-affjax-5.0.0"
              ,deps = ["@purescript-aff//:pkg"
                      ,"@purescript-argonaut-core//:pkg"
                      ,"@purescript-arraybuffer-types//:pkg"
                      ,"@purescript-dom//:pkg"
                      ,"@purescript-foreign//:pkg"
                      ,"@purescript-form-urlencoded//:pkg"
                      ,"@purescript-http-methods//:pkg"
                      ,"@purescript-integers//:pkg"
                      ,"@purescript-math//:pkg"
                      ,"@purescript-media-types//:pkg"
                      ,"@purescript-nullable//:pkg"
                      ,"@purescript-refs//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"])
purescript_dep(name = "purescript-eff"
              ,url = "https://github.com/purescript/purescript-eff/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-eff-3.1.0"
              ,deps = ["@purescript-prelude//:pkg"])
purescript_dep(name = "purescript-argonaut-codecs"
              ,url = "https://github.com/purescript-contrib/purescript-argonaut-codecs/archive/v3.2.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-argonaut-codecs-3.2.0"
              ,deps = ["@purescript-argonaut-core//:pkg"
                      ,"@purescript-generics//:pkg"
                      ,"@purescript-integers//:pkg"])
purescript_dep(name = "purescript-arrays"
              ,url = "https://github.com/purescript/purescript-arrays/archive/v4.2.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-arrays-4.2.1"
              ,deps = ["@purescript-foldable-traversable//:pkg"
                      ,"@purescript-nonempty//:pkg"
                      ,"@purescript-partial//:pkg"
                      ,"@purescript-st//:pkg"
                      ,"@purescript-tailrec//:pkg"
                      ,"@purescript-tuples//:pkg"
                      ,"@purescript-unfoldable//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"])
purescript_dep(name = "purescript-mathbox"
              ,url = "https://github.com/rintcius/purescript-mathbox/archive/v0.4.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-mathbox-0.4.0"
              ,deps = ["@purescript-console//:pkg"
                      ,"@purescript-foreign//:pkg"
                      ,"@purescript-free//:pkg"
                      ,"@purescript-globals//:pkg"
                      ,"@purescript-nullable//:pkg"
                      ,"@purescript-maps//:pkg"
                      ,"@purescript-lens//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-signal//:pkg"])
purescript_dep(name = "purescript-generics-rep"
              ,url = "https://github.com/purescript/purescript-generics-rep/archive/v5.3.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-generics-rep-5.3.0"
              ,deps = ["@purescript-enums//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-monoid//:pkg"
                      ,"@purescript-prelude//:pkg"
                      ,"@purescript-symbols//:pkg"])
purescript_dep(name = "purescript-remotedata"
              ,url = "https://github.com/krisajenkins/purescript-remotedata/archive/v2.2.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-remotedata-2.2.0"
              ,deps = ["@purescript-bifunctors//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-generics//:pkg"
                      ,"@purescript-profunctor-lenses//:pkg"])
purescript_dep(name = "purescript-node-process"
              ,url = "https://github.com/purescript-node/purescript-node-process/archive/v5.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-node-process-5.0.0"
              ,deps = ["@purescript-console//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-maps//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-node-fs//:pkg"
                      ,"@purescript-node-streams//:pkg"
                      ,"@purescript-posix-types//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"
                      ,"@purescript-partial//:pkg"])
purescript_dep(name = "purescript-lists"
              ,url = "https://github.com/purescript/purescript-lists/archive/v4.11.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-lists-4.11.0"
              ,deps = ["@purescript-lazy//:pkg"
                      ,"@purescript-nonempty//:pkg"
                      ,"@purescript-tailrec//:pkg"
                      ,"@purescript-unfoldable//:pkg"
                      ,"@purescript-partial//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"])
purescript_dep(name = "purescript-argonaut-generic-codecs"
              ,url = "https://github.com/eskimor/purescript-argonaut-generic-codecs/archive/v6.0.4.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-argonaut-generic-codecs-6.0.4"
              ,deps = ["@purescript-argonaut-core//:pkg"
                      ,"@purescript-arrays//:pkg"
                      ,"@purescript-generics//:pkg"
                      ,"@purescript-integers//:pkg"
                      ,"@purescript-partial//:pkg"])
purescript_dep(name = "purescript-node-url"
              ,url = "https://github.com/purescript-node/purescript-node-url/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-node-url-3.0.0"
              ,deps = ["@purescript-nullable//:pkg"])
purescript_dep(name = "purescript-exceptions"
              ,url = "https://github.com/purescript/purescript-exceptions/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-exceptions-3.1.0"
              ,deps = ["@purescript-eff//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-maybe//:pkg"])
purescript_dep(name = "purescript-smolder"
              ,url = "https://github.com/bodil/purescript-smolder/archive/v10.2.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-smolder-10.2.0"
              ,deps = ["@purescript-monoid//:pkg"
                      ,"@purescript-maps//:pkg"
                      ,"@purescript-strings//:pkg"
                      ,"@purescript-catenable-lists//:pkg"
                      ,"@purescript-tuples//:pkg"
                      ,"@purescript-free//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-bifunctors//:pkg"])
purescript_dep(name = "purescript-sets"
              ,url = "https://github.com/purescript/purescript-sets/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-sets-3.1.0"
              ,deps = ["@purescript-maps//:pkg"
                      ,"@purescript-tailrec//:pkg"])
purescript_dep(name = "purescript-formatters"
              ,url = "https://github.com/slamdata/purescript-formatters/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-formatters-3.0.0"
              ,deps = ["@purescript-prelude//:pkg"
                      ,"@purescript-parsing//:pkg"
                      ,"@purescript-fixed-points//:pkg"
                      ,"@purescript-datetime//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-generics-rep//:pkg"])
purescript_dep(name = "purescript-js-timers"
              ,url = "https://github.com/purescript-contrib/purescript-js-timers/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-js-timers-3.0.0"
              ,deps = ["@purescript-eff//:pkg"])
purescript_dep(name = "purescript-node-path"
              ,url = "https://github.com/purescript-node/purescript-node-path/archive/v2.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-node-path-2.0.0"
              ,deps = [])
purescript_dep(name = "purescript-mmorph"
              ,url = "https://github.com/Thimoteus/purescript-mmorph/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-mmorph-3.0.0"
              ,deps = ["@purescript-transformers//:pkg"
                      ,"@purescript-functors//:pkg"])
purescript_dep(name = "purescript-nullable"
              ,url = "https://github.com/purescript-contrib/purescript-nullable/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-nullable-3.0.0"
              ,deps = ["@purescript-maybe//:pkg"
                      ,"@purescript-functions//:pkg"])
purescript_dep(name = "purescript-console"
              ,url = "https://github.com/purescript/purescript-console/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-console-3.0.0"
              ,deps = ["@purescript-eff//:pkg"])
purescript_dep(name = "purescript-lazy"
              ,url = "https://github.com/purescript/purescript-lazy/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-lazy-3.0.0"
              ,deps = ["@purescript-monoid//:pkg"])
purescript_dep(name = "purescript-spec-mocha"
              ,url = "https://github.com/owickstrom/purescript-spec-mocha/archive/v2.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-spec-mocha-2.0.0"
              ,deps = ["@purescript-console//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-spec//:pkg"])
purescript_dep(name = "purescript-dom-classy"
              ,url = "https://github.com/garyb/purescript-dom-classy/archive/v2.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-dom-classy-2.1.0"
              ,deps = ["@purescript-dom//:pkg"])
purescript_dep(name = "purescript-lenient-html-parser"
              ,url = "https://github.com/justinwoo/purescript-lenient-html-parser/archive/v1.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-lenient-html-parser-1.0.0"
              ,deps = ["@purescript-prelude//:pkg"
                      ,"@purescript-console//:pkg"
                      ,"@purescript-string-parsers//:pkg"
                      ,"@purescript-generics-rep//:pkg"])
purescript_dep(name = "purescript-halogen-bootstrap"
              ,url = "https://github.com/slamdata/purescript-halogen-bootstrap/archive/v7.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-halogen-bootstrap-7.0.0"
              ,deps = ["@purescript-halogen//:pkg"])
purescript_dep(name = "purescript-hoist"
              ,url = "https://github.com/paf31/purescript-hoist/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-hoist-4.0.0"
              ,deps = ["@purescript-functors//:pkg"])
purescript_dep(name = "purescript-pux"
              ,url = "https://github.com/alexmingoia/purescript-pux/archive/v12.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-pux-12.0.0"
              ,deps = ["@purescript-aff//:pkg"
                      ,"@purescript-eff//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-signal//:pkg"
                      ,"@purescript-maps//:pkg"
                      ,"@purescript-functions//:pkg"
                      ,"@purescript-profunctor//:pkg"
                      ,"@purescript-react//:pkg"
                      ,"@purescript-globals//:pkg"
                      ,"@purescript-dom//:pkg"
                      ,"@purescript-smolder//:pkg"
                      ,"@purescript-css//:pkg"])
purescript_dep(name = "purescript-refs"
              ,url = "https://github.com/purescript/purescript-refs/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-refs-3.0.0"
              ,deps = ["@purescript-eff//:pkg"])
purescript_dep(name = "purescript-list-zipper"
              ,url = "https://github.com/soupi/purescript-list-zipper/archive/v1.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-list-zipper-1.0.0"
              ,deps = ["@purescript-prelude//:pkg"
                      ,"@purescript-control//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-tuples//:pkg"
                      ,"@purescript-unfoldable//:pkg"])
purescript_dep(name = "purescript-distributive"
              ,url = "https://github.com/purescript/purescript-distributive/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-distributive-3.0.0"
              ,deps = ["@purescript-identity//:pkg"])
purescript_dep(name = "purescript-io"
              ,url = "https://github.com/slamdata/purescript-io/archive/v5.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-io-5.0.0"
              ,deps = ["@purescript-aff//:pkg"
                      ,"@purescript-control//:pkg"
                      ,"@purescript-eff//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-monoid//:pkg"
                      ,"@purescript-newtype//:pkg"
                      ,"@purescript-prelude//:pkg"
                      ,"@purescript-tailrec//:pkg"
                      ,"@purescript-transformers//:pkg"])
purescript_dep(name = "purescript-string-parsers"
              ,url = "https://github.com/purescript-contrib/purescript-string-parsers/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-string-parsers-3.1.0"
              ,deps = ["@purescript-control//:pkg"
                      ,"@purescript-arrays//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-strings//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-tailrec//:pkg"])
purescript_dep(name = "purescript-parallel"
              ,url = "https://github.com/purescript/purescript-parallel/archive/v3.3.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-parallel-3.3.1"
              ,deps = ["@purescript-transformers//:pkg"
                      ,"@purescript-refs//:pkg"
                      ,"@purescript-functors//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"])
purescript_dep(name = "purescript-foreign"
              ,url = "https://github.com/purescript/purescript-foreign/archive/v4.0.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-foreign-4.0.1"
              ,deps = ["@purescript-arrays//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-functions//:pkg"
                      ,"@purescript-integers//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-strings//:pkg"
                      ,"@purescript-transformers//:pkg"])
purescript_dep(name = "purescript-pathy"
              ,url = "https://github.com/slamdata/purescript-pathy/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-pathy-4.0.0"
              ,deps = ["@purescript-console//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-partial//:pkg"
                      ,"@purescript-profunctor//:pkg"
                      ,"@purescript-strings//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"])
purescript_dep(name = "purescript-orders"
              ,url = "https://github.com/purescript/purescript-orders/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-orders-3.0.0"
              ,deps = ["@purescript-monoid//:pkg"])
purescript_dep(name = "purescript-spec-quickcheck"
              ,url = "https://github.com/owickstrom/purescript-spec-quickcheck/archive/v2.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-spec-quickcheck-2.0.0"
              ,deps = ["@purescript-aff//:pkg"
                      ,"@purescript-random//:pkg"
                      ,"@purescript-quickcheck//:pkg"
                      ,"@purescript-spec//:pkg"])
purescript_dep(name = "purescript-servant-support"
              ,url = "https://github.com/eskimor/purescript-servant-support/archive/v9.0.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-servant-support-9.0.1"
              ,deps = ["@purescript-console//:pkg"
                      ,"@purescript-prelude//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-argonaut-core//:pkg"
                      ,"@purescript-globals//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-nullable//:pkg"
                      ,"@purescript-dom//:pkg"
                      ,"@purescript-affjax//:pkg"
                      ,"@purescript-argonaut-generic-codecs//:pkg"])
purescript_dep(name = "purescript-lens"
              ,url = "https://github.com/purescript-contrib/purescript-lens/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-lens-3.0.0"
              ,deps = ["@purescript-const//:pkg"
                      ,"@purescript-distributive//:pkg"
                      ,"@purescript-profunctor//:pkg"])
purescript_dep(name = "purescript-functors"
              ,url = "https://github.com/purescript/purescript-functors/archive/v2.2.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-functors-2.2.0"
              ,deps = ["@purescript-const//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"])
purescript_dep(name = "purescript-server-sent-events"
              ,url = "https://github.com/MichaelXavier/purescript-server-sent-events/archive/v0.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-server-sent-events-0.1.0"
              ,deps = ["@purescript-dom//:pkg"
                      ,"@purescript-functions//:pkg"
                      ,"@purescript-maybe//:pkg"])
purescript_dep(name = "purescript-posix-types"
              ,url = "https://github.com/purescript-node/purescript-posix-types/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-posix-types-3.0.0"
              ,deps = ["@purescript-prelude//:pkg"
                      ,"@purescript-maybe//:pkg"])
purescript_dep(name = "purescript-node-sqlite3"
              ,url = "https://github.com/justinwoo/purescript-node-sqlite3/archive/v1.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-node-sqlite3-1.0.0"
              ,deps = ["@purescript-aff//:pkg"
                      ,"@purescript-foreign//:pkg"])
purescript_dep(name = "purescript-argonaut-traversals"
              ,url = "https://github.com/purescript-contrib/purescript-argonaut-traversals/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-argonaut-traversals-3.1.0"
              ,deps = ["@purescript-argonaut-core//:pkg"
                      ,"@purescript-argonaut-codecs//:pkg"
                      ,"@purescript-profunctor-lenses//:pkg"])
purescript_dep(name = "purescript-sammy"
              ,url = "https://github.com/purescript-contrib/purescript-sammy/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-sammy-3.0.0"
              ,deps = ["@purescript-eff//:pkg"])
purescript_dep(name = "purescript-node-readline"
              ,url = "https://github.com/purescript-node/purescript-node-readline/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-node-readline-3.1.0"
              ,deps = ["@purescript-console//:pkg"
                      ,"@purescript-node-streams//:pkg"
                      ,"@purescript-node-process//:pkg"
                      ,"@purescript-options//:pkg"
                      ,"@purescript-foreign//:pkg"])
purescript_dep(name = "purescript-safely"
              ,url = "https://github.com/paf31/purescript-safely/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-safely-3.0.0"
              ,deps = ["@purescript-freet//:pkg"
                      ,"@purescript-lists//:pkg"])
purescript_dep(name = "purescript-nonempty"
              ,url = "https://github.com/purescript/purescript-nonempty/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-nonempty-4.0.0"
              ,deps = ["@purescript-foldable-traversable//:pkg"
                      ,"@purescript-prelude//:pkg"])
purescript_dep(name = "purescript-test-unit"
              ,url = "https://github.com/bodil/purescript-test-unit/archive/v13.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-test-unit-13.0.0"
              ,deps = ["@purescript-aff//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-prelude//:pkg"
                      ,"@purescript-eff//:pkg"
                      ,"@purescript-quickcheck//:pkg"
                      ,"@purescript-free//:pkg"
                      ,"@purescript-strings//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-js-timers//:pkg"])
purescript_dep(name = "purescript-unsafe-coerce"
              ,url = "https://github.com/purescript/purescript-unsafe-coerce/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-unsafe-coerce-3.0.0"
              ,deps = [])
purescript_dep(name = "purescript-validation"
              ,url = "https://github.com/purescript/purescript-validation/archive/v3.2.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-validation-3.2.0"
              ,deps = ["@purescript-bifunctors//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-monoid//:pkg"])
purescript_dep(name = "purescript-flare"
              ,url = "https://github.com/sharkdp/purescript-flare/archive/v4.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-flare-4.1.0"
              ,deps = ["@purescript-foldable-traversable//:pkg"
                      ,"@purescript-dom//:pkg"
                      ,"@purescript-signal//:pkg"
                      ,"@purescript-canvas//:pkg"
                      ,"@purescript-drawing//:pkg"
                      ,"@purescript-smolder//:pkg"
                      ,"@purescript-nonempty//:pkg"
                      ,"@purescript-datetime//:pkg"
                      ,"@purescript-tuples//:pkg"])
purescript_dep(name = "purescript-routing"
              ,url = "https://github.com/slamdata/purescript-routing/archive/v6.1.2.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-routing-6.1.2"
              ,deps = ["@purescript-dom//:pkg"
                      ,"@purescript-eff//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-globals//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-maps//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-prelude//:pkg"
                      ,"@purescript-semirings//:pkg"
                      ,"@purescript-tuples//:pkg"
                      ,"@purescript-validation//:pkg"
                      ,"@purescript-aff//:pkg"
                      ,"@purescript-control//:pkg"
                      ,"@purescript-console//:pkg"
                      ,"@purescript-integers//:pkg"])
purescript_dep(name = "purescript-echarts"
              ,url = "https://github.com/slamdata/purescript-echarts/archive/v9.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-echarts-9.1.0"
              ,deps = ["@purescript-eff//:pkg"
                      ,"@purescript-control//:pkg"
                      ,"@purescript-foreign//:pkg"
                      ,"@purescript-dom//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-colors//:pkg"
                      ,"@purescript-variant//:pkg"
                      ,"@purescript-aff//:pkg"])
purescript_dep(name = "purescript-day"
              ,url = "https://github.com/paf31/purescript-day/archive/v9.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-day-9.0.0"
              ,deps = ["@purescript-control//:pkg"
                      ,"@purescript-exists//:pkg"
                      ,"@purescript-free//:pkg"
                      ,"@purescript-functors//:pkg"
                      ,"@purescript-pairing//:pkg"
                      ,"@purescript-transformers//:pkg"])
purescript_dep(name = "purescript-taylor"
              ,url = "https://github.com/paf31/purescript-taylor/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-taylor-3.0.0"
              ,deps = ["@purescript-lists//:pkg"])
purescript_dep(name = "purescript-foldable-traversable"
              ,url = "https://github.com/purescript/purescript-foldable-traversable/archive/v3.6.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-foldable-traversable-3.6.1"
              ,deps = ["@purescript-bifunctors//:pkg"
                      ,"@purescript-maybe//:pkg"])
purescript_dep(name = "purescript-uri"
              ,url = "https://github.com/slamdata/purescript-uri/archive/v4.2.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-uri-4.2.1"
              ,deps = ["@purescript-globals//:pkg"
                      ,"@purescript-integers//:pkg"
                      ,"@purescript-maps//:pkg"
                      ,"@purescript-pathy//:pkg"
                      ,"@purescript-string-parsers//:pkg"
                      ,"@purescript-unfoldable//:pkg"
                      ,"@purescript-generics//:pkg"
                      ,"@purescript-generics-rep//:pkg"
                      ,"@purescript-profunctor-lenses//:pkg"])
purescript_dep(name = "purescript-drawing"
              ,url = "https://github.com/purescript-contrib/purescript-drawing/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-drawing-3.0.0"
              ,deps = ["@purescript-canvas//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-math//:pkg"
                      ,"@purescript-integers//:pkg"
                      ,"@purescript-colors//:pkg"])
purescript_dep(name = "purescript-pprint"
              ,url = "https://github.com/paf31/purescript-pprint/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-pprint-4.0.0"
              ,deps = ["@purescript-arrays//:pkg"
                      ,"@purescript-strings//:pkg"
                      ,"@purescript-unfoldable//:pkg"])
purescript_dep(name = "purescript-random"
              ,url = "https://github.com/purescript/purescript-random/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-random-3.0.0"
              ,deps = ["@purescript-eff//:pkg"
                      ,"@purescript-integers//:pkg"
                      ,"@purescript-math//:pkg"])
purescript_dep(name = "purescript-options"
              ,url = "https://github.com/purescript-contrib/purescript-options/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-options-3.0.0"
              ,deps = ["@purescript-foreign//:pkg"
                      ,"@purescript-maps//:pkg"
                      ,"@purescript-tuples//:pkg"
                      ,"@purescript-monoid//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-contravariant//:pkg"])
purescript_dep(name = "purescript-gen"
              ,url = "https://github.com/purescript/purescript-gen/archive/v1.1.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-gen-1.1.1"
              ,deps = ["@purescript-nonempty//:pkg"
                      ,"@purescript-tailrec//:pkg"
                      ,"@purescript-tuples//:pkg"
                      ,"@purescript-unfoldable//:pkg"
                      ,"@purescript-integers//:pkg"])
purescript_dep(name = "purescript-arraybuffer-types"
              ,url = "https://github.com/purescript-contrib/purescript-arraybuffer-types/archive/v2.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-arraybuffer-types-2.0.0"
              ,deps = [])
purescript_dep(name = "purescript-symbols"
              ,url = "https://github.com/purescript/purescript-symbols/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-symbols-3.0.0"
              ,deps = ["@purescript-unsafe-coerce//:pkg"
                      ,"@purescript-prelude//:pkg"])
purescript_dep(name = "purescript-rationals"
              ,url = "https://github.com/anttih/purescript-rationals/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-rationals-4.0.0"
              ,deps = ["@purescript-integers//:pkg"
                      ,"@purescript-prelude//:pkg"])
purescript_dep(name = "purescript-control"
              ,url = "https://github.com/purescript/purescript-control/archive/v3.3.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-control-3.3.1"
              ,deps = ["@purescript-prelude//:pkg"])
purescript_dep(name = "purescript-quickcheck-laws"
              ,url = "https://github.com/garyb/purescript-quickcheck-laws/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-quickcheck-laws-3.0.0"
              ,deps = ["@purescript-proxy//:pkg"
                      ,"@purescript-enums//:pkg"
                      ,"@purescript-quickcheck//:pkg"])
purescript_dep(name = "purescript-colors"
              ,url = "https://github.com/sharkdp/purescript-colors/archive/v4.3.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-colors-4.3.0"
              ,deps = ["@purescript-arrays//:pkg"
                      ,"@purescript-integers//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-partial//:pkg"
                      ,"@purescript-strings//:pkg"])
purescript_dep(name = "purescript-these"
              ,url = "https://github.com/purescript-contrib/purescript-these/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-these-3.0.0"
              ,deps = ["@purescript-tuples//:pkg"])
purescript_dep(name = "purescript-react"
              ,url = "https://github.com/purescript-contrib/purescript-react/archive/v4.4.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-react-4.4.0"
              ,deps = ["@purescript-eff//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-prelude//:pkg"
                      ,"@purescript-nullable//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"])
purescript_dep(name = "purescript-fixed-points"
              ,url = "https://github.com/slamdata/purescript-fixed-points/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-fixed-points-4.0.0"
              ,deps = ["@purescript-exists//:pkg"
                      ,"@purescript-prelude//:pkg"
                      ,"@purescript-newtype//:pkg"
                      ,"@purescript-transformers//:pkg"])
purescript_dep(name = "purescript-free"
              ,url = "https://github.com/purescript/purescript-free/archive/v4.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-free-4.1.0"
              ,deps = ["@purescript-catenable-lists//:pkg"
                      ,"@purescript-exists//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"])
purescript_dep(name = "purescript-node-http"
              ,url = "https://github.com/purescript-node/purescript-node-http/archive/v4.2.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-node-http-4.2.0"
              ,deps = ["@purescript-maps//:pkg"
                      ,"@purescript-node-streams//:pkg"
                      ,"@purescript-node-url//:pkg"
                      ,"@purescript-options//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"
                      ,"@purescript-node-buffer//:pkg"
                      ,"@purescript-arraybuffer-types//:pkg"])
purescript_dep(name = "purescript-ansi"
              ,url = "https://github.com/hdgarrood/purescript-ansi/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-ansi-4.0.0"
              ,deps = ["@purescript-strings//:pkg"])
purescript_dep(name = "purescript-psci-support"
              ,url = "https://github.com/purescript/purescript-psci-support/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-psci-support-3.0.0"
              ,deps = ["@purescript-console//:pkg"])
purescript_dep(name = "purescript-foreign-lens"
              ,url = "https://github.com/purescript-contrib/purescript-foreign-lens/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-foreign-lens-3.0.0"
              ,deps = ["@purescript-foreign//:pkg"
                      ,"@purescript-profunctor-lenses//:pkg"])
purescript_dep(name = "purescript-tailrec"
              ,url = "https://github.com/purescript/purescript-tailrec/archive/v3.3.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-tailrec-3.3.0"
              ,deps = ["@purescript-identity//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-st//:pkg"
                      ,"@purescript-partial//:pkg"])
purescript_dep(name = "purescript-contravariant"
              ,url = "https://github.com/purescript/purescript-contravariant/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-contravariant-3.1.0"
              ,deps = ["@purescript-either//:pkg"
                      ,"@purescript-monoid//:pkg"
                      ,"@purescript-tuples//:pkg"])
purescript_dep(name = "purescript-now"
              ,url = "https://github.com/purescript-contrib/purescript-now/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-now-3.0.0"
              ,deps = ["@purescript-eff//:pkg"
                      ,"@purescript-datetime//:pkg"])
purescript_dep(name = "purescript-freet"
              ,url = "https://github.com/purescript-contrib/purescript-freet/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-freet-3.0.0"
              ,deps = ["@purescript-console//:pkg"
                      ,"@purescript-control//:pkg"
                      ,"@purescript-tailrec//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-exists//:pkg"
                      ,"@purescript-eff//:pkg"])
purescript_dep(name = "purescript-aff-coroutines"
              ,url = "https://github.com/purescript-contrib/purescript-aff-coroutines/archive/v6.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-aff-coroutines-6.0.0"
              ,deps = ["@purescript-aff//:pkg"
                      ,"@purescript-coroutines//:pkg"])
purescript_dep(name = "purescript-globals"
              ,url = "https://github.com/purescript/purescript-globals/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-globals-3.0.0"
              ,deps = [])
purescript_dep(name = "purescript-form-urlencoded"
              ,url = "https://github.com/purescript-contrib/purescript-form-urlencoded/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-form-urlencoded-3.0.0"
              ,deps = ["@purescript-prelude//:pkg"
                      ,"@purescript-globals//:pkg"
                      ,"@purescript-generics//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-strings//:pkg"
                      ,"@purescript-tuples//:pkg"])
purescript_dep(name = "purescript-integers"
              ,url = "https://github.com/purescript/purescript-integers/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-integers-3.1.0"
              ,deps = ["@purescript-globals//:pkg"
                      ,"@purescript-math//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-partial//:pkg"])
purescript_dep(name = "purescript-maps"
              ,url = "https://github.com/purescript/purescript-maps/archive/v3.5.2.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-maps-3.5.2"
              ,deps = ["@purescript-arrays//:pkg"
                      ,"@purescript-functions//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-st//:pkg"
                      ,"@purescript-gen//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"])
purescript_dep(name = "purescript-node-he"
              ,url = "https://github.com/justinwoo/purescript-node-he/archive/v0.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-node-he-0.1.0"
              ,deps = [])
purescript_dep(name = "purescript-dom-indexed"
              ,url = "https://github.com/slamdata/purescript-dom-indexed/archive/v5.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-dom-indexed-5.0.0"
              ,deps = ["@purescript-prelude//:pkg"
                      ,"@purescript-media-types//:pkg"
                      ,"@purescript-dom//:pkg"])
purescript_dep(name = "purescript-memoize"
              ,url = "https://github.com/paf31/purescript-memoize/archive/v4.0.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-memoize-4.0.1"
              ,deps = ["@purescript-lazy//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-tuples//:pkg"
                      ,"@purescript-integers//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-generics-rep//:pkg"
                      ,"@purescript-strings//:pkg"])
purescript_dep(name = "purescript-profunctor-lenses"
              ,url = "https://github.com/purescript-contrib/purescript-profunctor-lenses/archive/v3.8.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-profunctor-lenses-3.8.0"
              ,deps = ["@purescript-const//:pkg"
                      ,"@purescript-functors//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-identity//:pkg"
                      ,"@purescript-profunctor//:pkg"
                      ,"@purescript-sets//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-record//:pkg"])
purescript_dep(name = "purescript-unicode"
              ,url = "https://github.com/purescript-contrib/purescript-unicode/archive/v3.0.2.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-unicode-3.0.2"
              ,deps = ["@purescript-maybe//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-strings//:pkg"])
purescript_dep(name = "purescript-phoenix"
              ,url = "https://github.com/brandonhamilton/purescript-phoenix/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-phoenix-3.0.0"
              ,deps = ["@purescript-options//:pkg"])
purescript_dep(name = "purescript-css"
              ,url = "https://github.com/slamdata/purescript-css/archive/v3.3.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-css-3.3.0"
              ,deps = ["@purescript-generics//:pkg"
                      ,"@purescript-nonempty//:pkg"
                      ,"@purescript-profunctor//:pkg"
                      ,"@purescript-strings//:pkg"
                      ,"@purescript-these//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-colors//:pkg"
                      ,"@purescript-console//:pkg"])
purescript_dep(name = "purescript-profunctor"
              ,url = "https://github.com/purescript/purescript-profunctor/archive/v3.2.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-profunctor-3.2.0"
              ,deps = ["@purescript-contravariant//:pkg"
                      ,"@purescript-distributive//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-exists//:pkg"
                      ,"@purescript-tuples//:pkg"])
purescript_dep(name = "purescript-transformers"
              ,url = "https://github.com/purescript/purescript-transformers/archive/v3.4.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-transformers-3.4.0"
              ,deps = ["@purescript-arrays//:pkg"
                      ,"@purescript-lazy//:pkg"
                      ,"@purescript-distributive//:pkg"
                      ,"@purescript-tuples//:pkg"])
purescript_dep(name = "purescript-avar"
              ,url = "https://github.com/slamdata/purescript-avar/archive/v2.0.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-avar-2.0.1"
              ,deps = ["@purescript-eff//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-functions//:pkg"
                      ,"@purescript-exceptions//:pkg"])
purescript_dep(name = "purescript-semirings"
              ,url = "https://github.com/purescript/purescript-semirings/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-semirings-4.0.0"
              ,deps = ["@purescript-lists//:pkg"])
purescript_dep(name = "purescript-assert"
              ,url = "https://github.com/purescript/purescript-assert/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-assert-3.0.0"
              ,deps = ["@purescript-eff//:pkg"])
purescript_dep(name = "purescript-node-streams"
              ,url = "https://github.com/purescript-node/purescript-node-streams/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-node-streams-3.1.0"
              ,deps = ["@purescript-eff//:pkg"
                      ,"@purescript-node-buffer//:pkg"
                      ,"@purescript-prelude//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-exceptions//:pkg"])
purescript_dep(name = "purescript-quickserve"
              ,url = "https://github.com/paf31/purescript-quickserve/archive/v2.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-quickserve-2.0.0"
              ,deps = ["@purescript-aff//:pkg"
                      ,"@purescript-node-http//:pkg"
                      ,"@purescript-foreign-generic//:pkg"
                      ,"@purescript-typelevel-prelude//:pkg"
                      ,"@purescript-record//:pkg"])
purescript_dep(name = "purescript-monoid"
              ,url = "https://github.com/purescript/purescript-monoid/archive/v3.3.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-monoid-3.3.0"
              ,deps = ["@purescript-control//:pkg"
                      ,"@purescript-invariant//:pkg"
                      ,"@purescript-newtype//:pkg"])
purescript_dep(name = "purescript-websocket-simple"
              ,url = "https://github.com/zudov/purescript-websocket-simple/archive/v2.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-websocket-simple-2.0.0"
              ,deps = ["@purescript-dom//:pkg"
                      ,"@purescript-eff//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-generics//:pkg"
                      ,"@purescript-var//:pkg"])
purescript_dep(name = "purescript-filterable"
              ,url = "https://github.com/LiamGoodacre/purescript-filterable/archive/v2.4.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-filterable-2.4.1"
              ,deps = ["@purescript-foldable-traversable//:pkg"
                      ,"@purescript-identity//:pkg"
                      ,"@purescript-arrays//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-maps//:pkg"])
purescript_dep(name = "purescript-jquery"
              ,url = "https://github.com/purescript-contrib/purescript-jquery/archive/v4.3.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-jquery-4.3.0"
              ,deps = ["@purescript-dom//:pkg"
                      ,"@purescript-eff//:pkg"
                      ,"@purescript-foreign//:pkg"])
purescript_dep(name = "purescript-format"
              ,url = "https://github.com/sharkdp/purescript-format/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-format-3.0.0"
              ,deps = ["@purescript-strings//:pkg"
                      ,"@purescript-arrays//:pkg"
                      ,"@purescript-math//:pkg"
                      ,"@purescript-unfoldable//:pkg"
                      ,"@purescript-integers//:pkg"])
purescript_dep(name = "purescript-halogen-css"
              ,url = "https://github.com/slamdata/purescript-halogen-css/archive/v7.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-halogen-css-7.0.0"
              ,deps = ["@purescript-css//:pkg"
                      ,"@purescript-halogen//:pkg"])
purescript_dep(name = "purescript-node-postgres"
              ,url = "https://github.com/epost/purescript-node-postgres/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-node-postgres-4.0.0"
              ,deps = ["@purescript-arrays//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-foreign//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-aff//:pkg"
                      ,"@purescript-integers//:pkg"
                      ,"@purescript-datetime//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"
                      ,"@purescript-nullable//:pkg"
                      ,"@purescript-prelude//:pkg"
                      ,"@purescript-foreign-generic//:pkg"])
purescript_dep(name = "purescript-datetime"
              ,url = "https://github.com/purescript/purescript-datetime/archive/v3.4.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-datetime-3.4.1"
              ,deps = ["@purescript-enums//:pkg"
                      ,"@purescript-functions//:pkg"
                      ,"@purescript-generics//:pkg"
                      ,"@purescript-integers//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-maps//:pkg"
                      ,"@purescript-math//:pkg"])
purescript_dep(name = "purescript-argonaut-generic"
              ,url = "https://github.com/purescript-contrib/purescript-argonaut-generic/archive/v1.2.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-argonaut-generic-1.2.0"
              ,deps = ["@purescript-generics//:pkg"
                      ,"@purescript-argonaut-core//:pkg"
                      ,"@purescript-argonaut-codecs//:pkg"
                      ,"@purescript-generics-rep//:pkg"])
purescript_dep(name = "purescript-js-date"
              ,url = "https://github.com/purescript-contrib/purescript-js-date/archive/v5.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-js-date-5.1.0"
              ,deps = ["@purescript-datetime//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-foreign//:pkg"
                      ,"@purescript-integers//:pkg"
                      ,"@purescript-now//:pkg"])
purescript_dep(name = "purescript-node-child-process"
              ,url = "https://github.com/purescript-node/purescript-node-child-process/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-node-child-process-4.0.0"
              ,deps = ["@purescript-exceptions//:pkg"
                      ,"@purescript-foreign//:pkg"
                      ,"@purescript-functions//:pkg"
                      ,"@purescript-maps//:pkg"
                      ,"@purescript-node-fs//:pkg"
                      ,"@purescript-node-streams//:pkg"
                      ,"@purescript-nullable//:pkg"
                      ,"@purescript-posix-types//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"])
purescript_dep(name = "purescript-st"
              ,url = "https://github.com/purescript/purescript-st/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-st-3.0.0"
              ,deps = ["@purescript-eff//:pkg"])
purescript_dep(name = "purescript-proxy"
              ,url = "https://github.com/purescript/purescript-proxy/archive/v2.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-proxy-2.1.0"
              ,deps = ["@purescript-prelude//:pkg"])
purescript_dep(name = "purescript-argonaut"
              ,url = "https://github.com/purescript-contrib/purescript-argonaut/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-argonaut-3.1.0"
              ,deps = ["@purescript-argonaut-codecs//:pkg"
                      ,"@purescript-argonaut-core//:pkg"
                      ,"@purescript-argonaut-traversals//:pkg"])
purescript_dep(name = "purescript-run"
              ,url = "https://github.com/natefaubion/purescript-run/archive/v1.0.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-run-1.0.1"
              ,deps = ["@purescript-aff//:pkg"
                      ,"@purescript-console//:pkg"
                      ,"@purescript-eff//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-free//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-newtype//:pkg"
                      ,"@purescript-prelude//:pkg"
                      ,"@purescript-symbols//:pkg"
                      ,"@purescript-tailrec//:pkg"
                      ,"@purescript-tuples//:pkg"
                      ,"@purescript-type-equality//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"
                      ,"@purescript-variant//:pkg"
                      ,"@purescript-profunctor//:pkg"])
purescript_dep(name = "purescript-distributions"
              ,url = "https://github.com/paf31/purescript-distributions/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-distributions-3.0.0"
              ,deps = ["@purescript-lists//:pkg"])
purescript_dep(name = "purescript-const"
              ,url = "https://github.com/purescript/purescript-const/archive/v3.2.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-const-3.2.0"
              ,deps = ["@purescript-contravariant//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"])
purescript_dep(name = "purescript-partial"
              ,url = "https://github.com/purescript/purescript-partial/archive/v1.2.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-partial-1.2.1"
              ,deps = [])
purescript_dep(name = "purescript-exists"
              ,url = "https://github.com/purescript/purescript-exists/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-exists-3.0.0"
              ,deps = ["@purescript-unsafe-coerce//:pkg"])
purescript_dep(name = "purescript-type-equality"
              ,url = "https://github.com/purescript/purescript-type-equality/archive/v2.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-type-equality-2.1.0"
              ,deps = ["@purescript-eff//:pkg"])
purescript_dep(name = "purescript-unsafe-reference"
              ,url = "https://github.com/purescript-contrib/purescript-unsafe-reference/archive/v2.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-unsafe-reference-2.0.0"
              ,deps = ["@purescript-exceptions//:pkg"])
purescript_dep(name = "purescript-int-53"
              ,url = "https://github.com/rgrempel/purescript-int-53/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-int-53-3.0.0"
              ,deps = ["@purescript-generics//:pkg"
                      ,"@purescript-integers//:pkg"
                      ,"@purescript-math//:pkg"])
purescript_dep(name = "purescript-thermite"
              ,url = "https://github.com/paf31/purescript-thermite/archive/v5.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-thermite-5.0.0"
              ,deps = ["@purescript-aff//:pkg"
                      ,"@purescript-coroutines//:pkg"
                      ,"@purescript-dom//:pkg"
                      ,"@purescript-freet//:pkg"
                      ,"@purescript-profunctor-lenses//:pkg"
                      ,"@purescript-react-dom//:pkg"
                      ,"@purescript-react//:pkg"])
purescript_dep(name = "purescript-handlebars"
              ,url = "https://github.com/purescript-contrib/purescript-handlebars/archive/v2.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-handlebars-2.0.0"
              ,deps = [])
purescript_dep(name = "purescript-variant"
              ,url = "https://github.com/natefaubion/purescript-variant/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-variant-4.0.0"
              ,deps = ["@purescript-prelude//:pkg"
                      ,"@purescript-tuples//:pkg"
                      ,"@purescript-symbols//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"
                      ,"@purescript-partial//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-typelevel-prelude//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-record//:pkg"])
purescript_dep(name = "purescript-prelude"
              ,url = "https://github.com/purescript/purescript-prelude/archive/v3.1.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-prelude-3.1.1"
              ,deps = [])
purescript_dep(name = "purescript-enums"
              ,url = "https://github.com/purescript/purescript-enums/archive/v3.2.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-enums-3.2.1"
              ,deps = ["@purescript-either//:pkg"
                      ,"@purescript-strings//:pkg"
                      ,"@purescript-unfoldable//:pkg"])
purescript_dep(name = "purescript-either"
              ,url = "https://github.com/purescript/purescript-either/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-either-3.1.0"
              ,deps = ["@purescript-foldable-traversable//:pkg"
                      ,"@purescript-prelude//:pkg"])
purescript_dep(name = "purescript-email-validate"
              ,url = "https://github.com/cdepillabout/purescript-email-validate/archive/v2.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-email-validate-2.0.0"
              ,deps = ["@purescript-generics//:pkg"
                      ,"@purescript-parsing//:pkg"
                      ,"@purescript-string-parsers//:pkg"
                      ,"@purescript-aff//:pkg"
                      ,"@purescript-transformers//:pkg"])
purescript_dep(name = "purescript-crypto"
              ,url = "https://github.com/oreshinya/purescript-crypto/archive/v0.2.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-crypto-0.2.0"
              ,deps = ["@purescript-node-buffer//:pkg"
                      ,"@purescript-eff//:pkg"
                      ,"@purescript-prelude//:pkg"])
purescript_dep(name = "purescript-codec"
              ,url = "https://github.com/garyb/purescript-codec/archive/v2.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-codec-2.1.0"
              ,deps = ["@purescript-transformers//:pkg"
                      ,"@purescript-profunctor//:pkg"])
purescript_dep(name = "purescript-parsing"
              ,url = "https://github.com/purescript-contrib/purescript-parsing/archive/v4.3.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-parsing-4.3.1"
              ,deps = ["@purescript-arrays//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-identity//:pkg"
                      ,"@purescript-integers//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-strings//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-unicode//:pkg"])
purescript_dep(name = "purescript-spec"
              ,url = "https://github.com/owickstrom/purescript-spec/archive/v2.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-spec-2.0.0"
              ,deps = ["@purescript-console//:pkg"
                      ,"@purescript-aff//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-strings//:pkg"
                      ,"@purescript-prelude//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-monoid//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-pipes//:pkg"
                      ,"@purescript-ansi//:pkg"])
purescript_dep(name = "purescript-jack"
              ,url = "https://github.com/jystic/purescript-jack/archive/v2.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-jack-2.0.0"
              ,deps = ["@purescript-prelude//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-int-53//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-arrays//:pkg"
                      ,"@purescript-maps//:pkg"
                      ,"@purescript-console//:pkg"
                      ,"@purescript-random//:pkg"])
purescript_dep(name = "purescript-prettier"
              ,url = "https://github.com/gcanti/purescript-prettier/archive/v0.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-prettier-0.1.0"
              ,deps = ["@purescript-prelude//:pkg"
                      ,"@purescript-maybe//:pkg"])
purescript_dep(name = "purescript-reflection"
              ,url = "https://github.com/paf31/purescript-reflection/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-reflection-3.0.0"
              ,deps = ["@purescript-unsafe-coerce//:pkg"
                      ,"@purescript-monoid//:pkg"
                      ,"@purescript-proxy//:pkg"])
purescript_dep(name = "purescript-foreign-generic"
              ,url = "https://github.com/paf31/purescript-foreign-generic/archive/v5.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-foreign-generic-5.0.0"
              ,deps = ["@purescript-console//:pkg"
                      ,"@purescript-eff//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-foreign//:pkg"
                      ,"@purescript-generics-rep//:pkg"
                      ,"@purescript-globals//:pkg"
                      ,"@purescript-maps//:pkg"
                      ,"@purescript-nullable//:pkg"
                      ,"@purescript-proxy//:pkg"
                      ,"@purescript-symbols//:pkg"])
purescript_dep(name = "purescript-inject"
              ,url = "https://github.com/purescript/purescript-inject/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-inject-4.0.0"
              ,deps = ["@purescript-functors//:pkg"])
purescript_dep(name = "purescript-catenable-lists"
              ,url = "https://github.com/purescript/purescript-catenable-lists/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-catenable-lists-4.0.0"
              ,deps = ["@purescript-lists//:pkg"
                      ,"@purescript-tuples//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-unfoldable//:pkg"
                      ,"@purescript-control//:pkg"])
purescript_dep(name = "purescript-aff-promise"
              ,url = "https://github.com/nwolverson/purescript-aff-promise/archive/v1.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-aff-promise-1.0.0"
              ,deps = ["@purescript-aff//:pkg"
                      ,"@purescript-foreign//:pkg"])
purescript_dep(name = "purescript-functions"
              ,url = "https://github.com/purescript/purescript-functions/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-functions-3.0.0"
              ,deps = ["@purescript-prelude//:pkg"])
purescript_dep(name = "purescript-simple-json"
              ,url = "https://github.com/justinwoo/purescript-simple-json/archive/v1.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-simple-json-1.0.0"
              ,deps = ["@purescript-prelude//:pkg"
                      ,"@purescript-foreign-generic//:pkg"
                      ,"@purescript-typelevel-prelude//:pkg"
                      ,"@purescript-record//:pkg"
                      ,"@purescript-nullable//:pkg"])
purescript_dep(name = "purescript-aff"
              ,url = "https://github.com/slamdata/purescript-aff/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-aff-4.0.0"
              ,deps = ["@purescript-console//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-functions//:pkg"
                      ,"@purescript-parallel//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"
                      ,"@purescript-datetime//:pkg"
                      ,"@purescript-free//:pkg"
                      ,"@purescript-st//:pkg"
                      ,"@purescript-type-equality//:pkg"
                      ,"@purescript-avar//:pkg"])
purescript_dep(name = "purescript-fork"
              ,url = "https://github.com/slamdata/purescript-fork/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-fork-3.0.0"
              ,deps = ["@purescript-aff//:pkg"])
purescript_dep(name = "purescript-pipes"
              ,url = "https://github.com/felixSchl/purescript-pipes/archive/v5.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-pipes-5.0.0"
              ,deps = ["@purescript-monoid//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-tuples//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-tailrec//:pkg"
                      ,"@purescript-mmorph//:pkg"
                      ,"@purescript-prelude//:pkg"
                      ,"@purescript-aff//:pkg"
                      ,"@purescript-io//:pkg"])
purescript_dep(name = "purescript-newtype"
              ,url = "https://github.com/purescript/purescript-newtype/archive/v2.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-newtype-2.0.0"
              ,deps = ["@purescript-prelude//:pkg"])
purescript_dep(name = "purescript-tuples"
              ,url = "https://github.com/purescript/purescript-tuples/archive/v4.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-tuples-4.1.0"
              ,deps = ["@purescript-foldable-traversable//:pkg"
                      ,"@purescript-prelude//:pkg"
                      ,"@purescript-distributive//:pkg"
                      ,"@purescript-type-equality//:pkg"])
purescript_dep(name = "purescript-milkis"
              ,url = "https://github.com/justinwoo/purescript-milkis/archive/v1.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-milkis-1.0.0"
              ,deps = ["@purescript-prelude//:pkg"
                      ,"@purescript-node-http//:pkg"
                      ,"@purescript-http-methods//:pkg"
                      ,"@purescript-aff-promise//:pkg"])
purescript_dep(name = "purescript-node-fs-aff"
              ,url = "https://github.com/purescript-node/purescript-node-fs-aff/archive/v5.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-node-fs-aff-5.0.0"
              ,deps = ["@purescript-aff//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-node-fs//:pkg"
                      ,"@purescript-node-path//:pkg"])
purescript_dep(name = "purescript-halogen-vdom"
              ,url = "https://github.com/slamdata/purescript-halogen-vdom/archive/v2.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-halogen-vdom-2.0.0"
              ,deps = ["@purescript-prelude//:pkg"
                      ,"@purescript-eff//:pkg"
                      ,"@purescript-tuples//:pkg"
                      ,"@purescript-dom//:pkg"
                      ,"@purescript-maps//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"
                      ,"@purescript-bifunctors//:pkg"
                      ,"@purescript-refs//:pkg"
                      ,"@purescript-foreign//:pkg"])
purescript_dep(name = "purescript-invariant"
              ,url = "https://github.com/purescript/purescript-invariant/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-invariant-3.0.0"
              ,deps = ["@purescript-prelude//:pkg"])
purescript_dep(name = "purescript-freeap"
              ,url = "https://github.com/ethul/purescript-freeap/archive/v3.0.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-freeap-3.0.1"
              ,deps = ["@purescript-exists//:pkg"
                      ,"@purescript-const//:pkg"])
purescript_dep(name = "purescript-numbers"
              ,url = "https://github.com/sharkdp/purescript-numbers/archive/v5.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-numbers-5.0.0"
              ,deps = ["@purescript-math//:pkg"
                      ,"@purescript-globals//:pkg"
                      ,"@purescript-maybe//:pkg"])
purescript_dep(name = "purescript-maybe"
              ,url = "https://github.com/purescript/purescript-maybe/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-maybe-3.0.0"
              ,deps = ["@purescript-monoid//:pkg"
                      ,"@purescript-prelude//:pkg"])
purescript_dep(name = "purescript-coroutines"
              ,url = "https://github.com/purescript-contrib/purescript-coroutines/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-coroutines-4.0.0"
              ,deps = ["@purescript-freet//:pkg"
                      ,"@purescript-profunctor//:pkg"
                      ,"@purescript-parallel//:pkg"])
purescript_dep(name = "purescript-errors"
              ,url = "https://github.com/passy/purescript-errors/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-errors-3.0.0"
              ,deps = ["@purescript-either//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-control//:pkg"
                      ,"@purescript-eff//:pkg"
                      ,"@purescript-monoid//:pkg"])
purescript_dep(name = "purescript-folds"
              ,url = "https://github.com/paf31/purescript-folds/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-folds-3.1.0"
              ,deps = ["@purescript-control//:pkg"
                      ,"@purescript-profunctor//:pkg"])
purescript_dep(name = "purescript-math"
              ,url = "https://github.com/purescript/purescript-math/archive/v2.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-math-2.1.0"
              ,deps = [])
purescript_dep(name = "purescript-argonaut-core"
              ,url = "https://github.com/purescript-contrib/purescript-argonaut-core/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-argonaut-core-3.1.0"
              ,deps = ["@purescript-enums//:pkg"
                      ,"@purescript-functions//:pkg"
                      ,"@purescript-gen//:pkg"
                      ,"@purescript-maps//:pkg"])
purescript_dep(name = "purescript-debug"
              ,url = "https://github.com/garyb/purescript-debug/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-debug-3.0.0"
              ,deps = ["@purescript-prelude//:pkg"])
purescript_dep(name = "purescript-identity"
              ,url = "https://github.com/purescript/purescript-identity/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-identity-3.1.0"
              ,deps = ["@purescript-foldable-traversable//:pkg"])
purescript_dep(name = "purescript-leibniz"
              ,url = "https://github.com/paf31/purescript-leibniz/archive/v4.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-leibniz-4.1.0"
              ,deps = ["@purescript-prelude//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"])
purescript_dep(name = "purescript-node-buffer"
              ,url = "https://github.com/purescript-node/purescript-node-buffer/archive/v3.0.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-node-buffer-3.0.1"
              ,deps = ["@purescript-eff//:pkg"
                      ,"@purescript-maybe//:pkg"])
purescript_dep(name = "purescript-signal"
              ,url = "https://github.com/bodil/purescript-signal/archive/v9.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-signal-9.0.0"
              ,deps = ["@purescript-dom//:pkg"
                      ,"@purescript-prelude//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-js-timers//:pkg"
                      ,"@purescript-monoid//:pkg"])
purescript_dep(name = "purescript-unfoldable"
              ,url = "https://github.com/purescript/purescript-unfoldable/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-unfoldable-3.0.0"
              ,deps = ["@purescript-partial//:pkg"
                      ,"@purescript-tuples//:pkg"])
purescript_dep(name = "purescript-canvas"
              ,url = "https://github.com/purescript-contrib/purescript-canvas/archive/v3.2.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-canvas-3.2.0"
              ,deps = ["@purescript-eff//:pkg"
                      ,"@purescript-functions//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-arraybuffer-types//:pkg"])
purescript_dep(name = "purescript-behaviors"
              ,url = "https://github.com/paf31/purescript-behaviors/archive/v6.0.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-behaviors-6.0.1"
              ,deps = ["@purescript-prelude//:pkg"
                      ,"@purescript-eff//:pkg"
                      ,"@purescript-sets//:pkg"
                      ,"@purescript-filterable//:pkg"
                      ,"@purescript-nullable//:pkg"])
purescript_dep(name = "purescript-var"
              ,url = "https://github.com/zudov/purescript-var/archive/v2.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-var-2.0.0"
              ,deps = ["@purescript-invariant//:pkg"
                      ,"@purescript-contravariant//:pkg"
                      ,"@purescript-eff//:pkg"])
purescript_dep(name = "purescript-generics"
              ,url = "https://github.com/purescript/purescript-generics/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-generics-4.0.0"
              ,deps = ["@purescript-arrays//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-identity//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-proxy//:pkg"
                      ,"@purescript-strings//:pkg"])
purescript_dep(name = "purescript-machines"
              ,url = "https://github.com/purescript-contrib/purescript-machines/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-machines-4.0.0"
              ,deps = ["@purescript-arrays//:pkg"
                      ,"@purescript-eff//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-monoid//:pkg"
                      ,"@purescript-profunctor//:pkg"
                      ,"@purescript-tuples//:pkg"])
purescript_dep(name = "purescript-strongcheck"
              ,url = "https://github.com/purescript-contrib/purescript-strongcheck/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-strongcheck-3.1.0"
              ,deps = ["@purescript-console//:pkg"
                      ,"@purescript-enums//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-free//:pkg"
                      ,"@purescript-machines//:pkg"
                      ,"@purescript-random//:pkg"
                      ,"@purescript-arrays//:pkg"
                      ,"@purescript-datetime//:pkg"
                      ,"@purescript-gen//:pkg"])
purescript_dep(name = "purescript-halogen"
              ,url = "https://github.com/slamdata/purescript-halogen/archive/v3.0.1.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-halogen-3.0.1"
              ,deps = ["@purescript-aff//:pkg"
                      ,"@purescript-const//:pkg"
                      ,"@purescript-coroutines//:pkg"
                      ,"@purescript-dom//:pkg"
                      ,"@purescript-dom-indexed//:pkg"
                      ,"@purescript-foreign//:pkg"
                      ,"@purescript-fork//:pkg"
                      ,"@purescript-free//:pkg"
                      ,"@purescript-freeap//:pkg"
                      ,"@purescript-halogen-vdom//:pkg"
                      ,"@purescript-maps//:pkg"
                      ,"@purescript-media-types//:pkg"
                      ,"@purescript-nullable//:pkg"
                      ,"@purescript-parallel//:pkg"
                      ,"@purescript-profunctor//:pkg"
                      ,"@purescript-profunctor-lenses//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"
                      ,"@purescript-unsafe-reference//:pkg"])
purescript_dep(name = "purescript-pairing"
              ,url = "https://github.com/paf31/purescript-pairing/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-pairing-4.0.0"
              ,deps = ["@purescript-functors//:pkg"
                      ,"@purescript-identity//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-free//:pkg"])
purescript_dep(name = "purescript-react-dom"
              ,url = "https://github.com/purescript-contrib/purescript-react-dom/archive/v4.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-react-dom-4.1.0"
              ,deps = ["@purescript-dom//:pkg"
                      ,"@purescript-eff//:pkg"
                      ,"@purescript-react//:pkg"])
purescript_dep(name = "purescript-bifunctors"
              ,url = "https://github.com/purescript/purescript-bifunctors/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-bifunctors-3.0.0"
              ,deps = ["@purescript-control//:pkg"
                      ,"@purescript-newtype//:pkg"])
purescript_dep(name = "purescript-express"
              ,url = "https://github.com/nkly/purescript-express/archive/v0.6.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-express-0.6.0"
              ,deps = ["@purescript-aff//:pkg"
                      ,"@purescript-arrays//:pkg"
                      ,"@purescript-control//:pkg"
                      ,"@purescript-data-default//:pkg"
                      ,"@purescript-eff//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-foldable-traversable//:pkg"
                      ,"@purescript-foreign//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-maybe//:pkg"
                      ,"@purescript-node-http//:pkg"
                      ,"@purescript-parsing//:pkg"
                      ,"@purescript-strings//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-unfoldable//:pkg"
                      ,"@purescript-foreign-generic//:pkg"
                      ,"@purescript-test-unit//:pkg"])
purescript_dep(name = "purescript-record"
              ,url = "https://github.com/purescript/purescript-record/archive/v0.2.5.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-record-0.2.5"
              ,deps = ["@purescript-symbols//:pkg"
                      ,"@purescript-functions//:pkg"
                      ,"@purescript-st//:pkg"
                      ,"@purescript-typelevel-prelude//:pkg"])
purescript_dep(name = "purescript-media-types"
              ,url = "https://github.com/purescript-contrib/purescript-media-types/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-media-types-3.0.0"
              ,deps = ["@purescript-generics//:pkg"])
purescript_dep(name = "purescript-yargs"
              ,url = "https://github.com/paf31/purescript-yargs/archive/v3.1.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-yargs-3.1.0"
              ,deps = ["@purescript-unsafe-coerce//:pkg"
                      ,"@purescript-foreign//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-console//:pkg"
                      ,"@purescript-exceptions//:pkg"])
purescript_dep(name = "purescript-graphs"
              ,url = "https://github.com/purescript/purescript-graphs/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-graphs-3.0.0"
              ,deps = ["@purescript-sets//:pkg"
                      ,"@purescript-catenable-lists//:pkg"])
purescript_dep(name = "purescript-typelevel-prelude"
              ,url = "https://github.com/purescript/purescript-typelevel-prelude/archive/v2.5.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-typelevel-prelude-2.5.0"
              ,deps = ["@purescript-proxy//:pkg"
                      ,"@purescript-symbols//:pkg"
                      ,"@purescript-type-equality//:pkg"])
purescript_dep(name = "purescript-quickcheck"
              ,url = "https://github.com/purescript/purescript-quickcheck/archive/v4.6.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-quickcheck-4.6.0"
              ,deps = ["@purescript-arrays//:pkg"
                      ,"@purescript-console//:pkg"
                      ,"@purescript-either//:pkg"
                      ,"@purescript-enums//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-gen//:pkg"
                      ,"@purescript-lists//:pkg"
                      ,"@purescript-nonempty//:pkg"
                      ,"@purescript-partial//:pkg"
                      ,"@purescript-random//:pkg"
                      ,"@purescript-strings//:pkg"
                      ,"@purescript-transformers//:pkg"
                      ,"@purescript-generics-rep//:pkg"
                      ,"@purescript-typelevel-prelude//:pkg"
                      ,"@purescript-record//:pkg"])
purescript_dep(name = "purescript-node-fs"
              ,url = "https://github.com/purescript-node/purescript-node-fs/archive/v4.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-node-fs-4.0.0"
              ,deps = ["@purescript-datetime//:pkg"
                      ,"@purescript-foreign//:pkg"
                      ,"@purescript-node-buffer//:pkg"
                      ,"@purescript-node-path//:pkg"
                      ,"@purescript-unsafe-coerce//:pkg"
                      ,"@purescript-nullable//:pkg"
                      ,"@purescript-node-streams//:pkg"
                      ,"@purescript-exceptions//:pkg"
                      ,"@purescript-js-date//:pkg"
                      ,"@purescript-globals//:pkg"])
purescript_dep(name = "purescript-http-methods"
              ,url = "https://github.com/purescript-contrib/purescript-http-methods/archive/v3.0.0.tar.gz"
              ,sha256 = None
              ,strip_prefix = "purescript-http-methods-3.0.0"
              ,deps = ["@purescript-generics//:pkg"])
