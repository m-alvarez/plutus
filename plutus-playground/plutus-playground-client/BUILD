load("@bazel_rules_purescript//purescript:purescript.bzl", "purescript_library", "purescript_app")

purescript_library(
    name = "pkg",
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

# # Defines an application with default entrypoint (Main.main):
# purescript_app(
#     name = "playground",
#     srcs = glob(["src/**/*.purs"]) + glob(["src/**/*.js"]) + glob(["generated/**/*.purs"]),
#     entry_function = "main",
#     entry_module = "Main",
#     visibility = ["//visibility:public"],
#     deps = dependencies,
# )
