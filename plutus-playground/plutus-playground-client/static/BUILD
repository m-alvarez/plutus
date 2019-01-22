load("@io_bazel_rules_sass//:defs.bzl", "sass_binary", "sass_library")

sass_library(
    name = "sass_variables",
    srcs = ["variables.scss"],
)

sass_binary(
    name = "main",
    src = "main.scss",
    deps = [
      ":sass_variables",
      "@com_github_bootstrap//:bootstrap_sass",
    ],
    visibility = ["//visibility:public"],
)

filegroup(
  name = "static_files",
  srcs = glob(["*.html", "*.ico", "*.scss"]),
  visibility = ["//visibility:public"],
)
