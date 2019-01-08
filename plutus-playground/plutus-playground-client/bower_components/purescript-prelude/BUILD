package(default_visibility = ["//visibility:public"])
load("@bazel_rules_purescript//purescript:purescript.bzl", "purescript_library")

purescript_library(
    name = "pkg",
    srcs = glob(["src/**/*.purs"]) + glob(["src/**/*.js"]),
)
