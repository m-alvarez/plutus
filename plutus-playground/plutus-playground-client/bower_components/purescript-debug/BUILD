package(default_visibility = ["//visibility:public"])
load("@bazel_rules_purescript//purescript:purescript.bzl", "purescript_library")
load("@bazel_tools//tools/build_defs/pkg:pkg.bzl", "pkg_tar")

purescript_library(
    name = "pkg",
    srcs = glob(["src/**/*.purs"]) + glob(["src/**/*.js"]),
    deps = ["//bower_components/purescript-prelude:archive"],
)
