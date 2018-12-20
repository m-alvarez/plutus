"""Rules for purescript"""

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")
load("@bazel_skylib//lib:paths.bzl", "paths")

run_template = """
#!/usr/bin/env bash
set -o errexit

node -e "require('./{target_path}/{entry_module}/index.js').{entry_function}({entry_params})"
"""

compile_trans_template = "cp -R {path}/* {output}"

def _purescript_compile(ctx):
    srcs = ctx.files.srcs + ctx.files.deps
    target = ctx.actions.declare_file(ctx.outputs.target.basename)
    purs = ctx.executable.purs
    flags = " ".join(ctx.attr.compiler_flags)

    bazel_ps_deps = []
    for d in ctx.attr.deps:
        for f in d.files:
            if f.basename == "target_srcs":
                bazel_ps_deps = [f.path + "/**/*.purs"] + bazel_ps_deps

    compileCmd = """
        set -o errexit
        mkdir "$2"
        "$1" compile """ + flags + """ --output "$2" "${@:3}"
        """

    ctx.actions.run_shell(
        inputs = srcs + [purs],
        outputs = [target],
        command = compileCmd,
        arguments = [purs.path, target.path] +
                    [src.path for src in srcs if src.extension == "purs"] +
                    bazel_ps_deps,
    )

    # TODO -- this will currently break if files have the same names, so --
    #         gotta fix that somehow
    cpSrcsCmd = "\n".join(
        [
            "set -o errexit",
            """mkdir -p "$1" """,
            """cp "${@:2}" "$1" """,
        ],
    )

    target_srcs = ctx.actions.declare_file(ctx.outputs.target_srcs.basename)

    ctx.actions.run_shell(
        inputs = ctx.files.srcs,
        outputs = [target_srcs],
        command = cpSrcsCmd,
        arguments = [target_srcs.path] + [src.path for src in ctx.files.srcs],
    )

    return target

def _purescript_app(ctx):
    target = _purescript_compile(ctx)

    entry_params = ",".join([
        '\\"{entry}\\"'.format(entry = e)
        for e in ctx.attr.entry_parameters
    ])

    script = ctx.actions.declare_file(ctx.label.name)
    script_content = run_template.format(
        target_path = target.short_path,
        entry_module = getattr(ctx.attr, "entry_module"),
        entry_function = getattr(ctx.attr, "entry_function"),
        entry_params = entry_params,
    )
    ctx.actions.write(script, script_content, is_executable = True)

    runfiles = ctx.runfiles(files = [target])

    return [DefaultInfo(executable = script, runfiles = runfiles)]

purescript_app = rule(
    implementation = _purescript_app,
    attrs = {
        "srcs": attr.label_list(
            allow_files = True,
        ),
        "deps": attr.label_list(
            default = [],
        ),
        "purs": attr.label(
            allow_single_file = True,
            executable = True,
            cfg = "host",
            default = "@purs",
        ),
        "compiler_flags": attr.string_list(
            default = [],
        ),
        "entry_module": attr.string(
            default = "Main",
        ),
        "entry_function": attr.string(
            default = "main",
        ),
        "entry_parameters": attr.string_list(
            default = [],
        ),
    },
    outputs = {
        "target": "target",
        "target_srcs": "target_srcs",
    },
    executable = True,
)

def _purescript_lib(ctx):
    _purescript_compile(ctx)

purescript_lib = rule(
    implementation = _purescript_lib,
    attrs = {
        "srcs": attr.label_list(
            allow_files = True,
        ),
        "deps": attr.label_list(
            default = [],
        ),
        "purs": attr.label(
            allow_single_file = True,
            executable = True,
            cfg = "host",
            default = "@purs",
        ),
        "compiler_flags": attr.string_list(
            default = [],
        ),
    },
    outputs = {
        #"tar": "%{name}.tar",
        "target": "target",
        "target_srcs": "target_srcs",
    },
)

test_template = """
err=0
node -e "require('./{target_path}/{test_file}/index.js').{entry_function}()" || err=1
echo
"""

def _run_test(target_path, entry_module, entry_function):
    return test_template.format(
        target_path = target_path,
        test_file = entry_module,
        entry_function = entry_function,
    )

def _purescript_test(ctx):
    target = _purescript_compile(ctx)

    script = "\n".join(
        [
            """
#!/usr/bin/env bash
err=0
""",
            _run_test(target.short_path, ctx.attr.main_module, ctx.attr.main_function),
            "exit $err",
        ],
    )
    ctx.actions.write(
        output = ctx.outputs.executable,
        content = script,
    )

    runfiles = ctx.runfiles(files = [target])
    return [DefaultInfo(runfiles = runfiles)]

purescript_test = rule(
    implementation = _purescript_test,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "deps": attr.label_list(),
        "main_module": attr.string(
            default = "Test.Main",
        ),
        "main_function": attr.string(
            default = "main",
        ),
        "purs": attr.label(
            allow_single_file = True,
            executable = True,
            cfg = "host",
            default = "@purs",
        ),
        "compiler_flags": attr.string_list(
            default = [],
        ),
    },
    outputs = {
        "target": "test-target",
        "target_srcs": "target_srcs",
    },
    test = True,
)

_default_purs_pkg_url_linux = \
    "https://github.com/purescript/purescript/releases/download/v0.11.7/linux64.tar.gz"
_default_purs_pkg_url_darwin = \
    "https://github.com/purescript/purescript/releases/download/v0.11.7/macos.tar.gz"
_default_purs_pkg_sha256_linux = \
    "fd8b96240e9485f75f21654723f416470d8049655ac1d82890c13187038bfdde"
_default_purs_pkg_sha256_macos = \
    "d8caa11148f8a9a2ac89b0b0c232ed8038913576e46bfc7463540c09b3fe88ce"
_default_purs_pkg_strip_prefix = \
    "purescript"

def purescript_toolchain(url = "default", sha256 = _default_purs_pkg_sha256_linux, strip_prefix = _default_purs_pkg_strip_prefix):
    is_darwin = select({
        "@bazel_tools//src/conditions:darwin": True,
        "//conditions:default": False,
    })

    if is_darwin and url == "default":
        url = _default_purs_pkg_url_darwin
        sha256 = _default_purs_pkg_sha256_macos
    elif url == "default":
        url = _default_purs_pkg_url_linux

    http_archive(
        name = "purs",
        urls = [url],
        sha256 = sha256,
        strip_prefix = strip_prefix,
        build_file_content = """exports_files(["purs"])""",
    )

_purescript_dep_build_content = """
package(default_visibility = ["//visibility:public"])
load("@bazel_rules_purescript//purescript:purescript.bzl", "purescript_library")

purescript_library(
    name = "pkg",
    srcs = glob(["src/**/*.purs"]) + glob(["src/**/*.js"]),
)
"""

def purescript_dep(name, url, sha256, strip_prefix):
    http_archive(
        name = name,
        urls = [url],
        sha256 = sha256,
        strip_prefix = strip_prefix,
        build_file_content = _purescript_dep_build_content,
    )

def output_file(ctx, name, src):
    path = paths.join(
        "output",
        ".".join(paths.split_extension(src.short_path)[0].split("/")[3:]),
        name,
    )
    f = ctx.actions.declare_file(path)
    return ctx.actions.declare_file(path)

def _purescript_library(ctx):
    srcs = ctx.files.srcs
    deps = ctx.attr.deps
    purs = ctx.executable.purs

    ps_dep_tar = []
    for d in ctx.attr.deps:
        if d.label.name == "archive":
            ps_dep_tar = ps_dep_tar + d.files.to_list()
    print(ps_dep_tar)

    # Build this lib.
    outputs = []
    for src in srcs:
        if src.extension == "purs":
            outputs += [output_file(ctx, "index.js", src)]
            outputs += [output_file(ctx, "externs.json", src)]

        if src.extension == "js":
            outputs += [output_file(ctx, "foreign.js", src)]

    compileCmd = """
      set -e
      if [ -n "$4" ]
      then
        tar -xf $4 -C $3
        tar -xf $4 -C bazel-out/darwin-fastbuild/genfiles/$3
      fi
      $1 compile --output $2 $(find ${3}/src/ -name '*.purs')
    """

    tar_file = ""
    if len(ps_dep_tar) == 1:
        tar_file = ps_dep_tar[0].path

    ctx.actions.run_shell(
        inputs = srcs + ps_dep_tar,
        tools = [purs],
        command = compileCmd,
        arguments = [purs.path, paths.join(ctx.genfiles_dir.path, ctx.label.package, "output"), ctx.label.package, tar_file] + [s.path for s in srcs if s.extension == "purs"],
        outputs = outputs,
    )

    return [
        DefaultInfo(files = depset(srcs + outputs)),
    ]

purescript_library = rule(
    implementation = _purescript_library,
    output_to_genfiles = True,
    attrs = {
        "purs": attr.label(
            allow_single_file = True,
            executable = True,
            cfg = "host",
            default = "@purs",
        ),
        "srcs": attr.label_list(
            allow_files = True,
        ),
        "deps": attr.label_list(
            default = [],
        ),
    },
)
