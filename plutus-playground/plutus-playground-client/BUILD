load("@bazel_rules_purescript//purescript:purescript.bzl", "purescript_library", "purescript_bundle")
load("@build_bazel_rules_nodejs//:defs.bzl", "nodejs_binary")

purescript_library(
    name = "playground_purs",
    srcs = glob(["src/**/*.purs"]) + glob(["src/**/*.js"]) + glob(["generated/**/*.purs"]),
    deps = [
        "@purescript-ace-halogen//:pkg",
        "@purescript-ace//:pkg",
        "@purescript-aff//:pkg",
        "@purescript-argonaut-codecs//:pkg",
        "@purescript-console//:pkg",
        "@purescript-debug//:pkg",
        "@purescript-halogen-echarts//:pkg",
        "@purescript-halogen//:pkg",
        "@purescript-js-date//:pkg",
        "@purescript-maybe//:pkg",
        "@purescript-prelude//:pkg",
        "@purescript-remotedata//:pkg",
        "@purescript-servant-support//:pkg",
        "@purescript-transformers//:pkg",
        "@purescript-undefinable//:pkg",
    ]
)

purescript_bundle(
  name = "playground_bundle",
  srcs = ["//static:static_files"],
  entry = "entry-bazel.js",
  config = "webpack-bazel.config.js",
  deps = [":playground_purs"],
  node_modules = "@npm//:node_modules",
  webpack = "@npm//webpack-cli/bin:webpack-cli",
)

# nodejs_binary(
#     name = "webpack",
#     args = [
#         "--config webpack.config.js",
#         "--entry ./entry.js",
#         # "--watch",
#         # "--mode development",
#     ],
#     data = [
#       "webpack.config.js",
#       "//static:static_files",
#       "entry.js",
#     ],
#     entry_point = "webpack/bin/webpack.js",
#     node_modules = "@npm//:node_modules",
#     templated_args = ["--node_options=--preserve-symlinks"],
#     visibility = ["//visibility:public"],
# )

# rollup_bundle(
#   name = "rollup",
#   srcs = ["main.js"],
#   deps = ["//static:sass_main", ":playground_purs"],
#   entry_point = "main.js",
# )

# # Defines an application with default entrypoint (Main.main):
# purescript_app(
#     name = "playground",
#     srcs = glob(["src/**/*.purs"]) + glob(["src/**/*.js"]) + glob(["generated/**/*.purs"]),
#     entry_function = "main",
#     entry_module = "Main",
#     visibility = ["//visibility:public"],
#     deps = dependencies,
# )
