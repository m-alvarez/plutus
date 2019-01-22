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
    deps = [%s],
)
"""

def purescript_dep(name, url, sha256, strip_prefix, deps = [], patches = []):
    http_archive(
        name = name,
        urls = [url],
        sha256 = sha256,
        strip_prefix = strip_prefix,
        build_file_content = _purescript_dep_build_content % ",".join([repr(d) for d in deps]),
        patches = patches,
    )

def drop_til_initcaps(l):
    drop_at = None
    for (idx, part) in enumerate(l):
        if part[0].upper() == part[0] and not drop_at:
            drop_at = idx

    if not drop_at:
        drop_at = 0

    return l[drop_at:]

# We need a good way of figuring out the module name just by looking at the file path.
#   I don't think there is one.
def output_file(ctx, name, src, outdir):
    components = paths.split_extension(src.short_path)[0].split("/")
    module_parts = drop_til_initcaps(components)

    path = paths.join(
        "output",
        ".".join(module_parts),
        name,
    )
    return ctx.actions.declare_file(path, sibling = outdir)

def _path_above_output(path):
  parts = path.split("/")
  topParts = parts[(parts.index("output"))+1:]
  return "/".join(topParts)

def _purescript_library(ctx):
    purs = ctx.executable.purs
    srcs = ctx.files.srcs
    deps = ctx.attr.deps
    zipper = ctx.executable._zipper

    ps_dep_srcs = depset(transitive = [dep[OutputGroupInfo].srcs for dep in deps])
    ps_dep_outputs = depset(transitive = [dep[OutputGroupInfo].outputs for dep in deps])

    deps_zip = ctx.actions.declare_file("deps.zip")
    zipPaths = ["%s=%s" % (_path_above_output(p.path), p.path) for p in ps_dep_outputs.to_list()]

    # We need to create a single zip file of all the dependencies'
    # precompiled outputs, so we can pass them all through as a single
    # argument..

    ctx.actions.run_shell(
        inputs = ps_dep_outputs.to_list(),
        tools = [ctx.executable._zipper],
        command = """
        set -e

        if [ $# -gt 1 ]
        then
          echo Creating {deps_zip}
          {zipper} c {deps_zip} $@
        else
          echo Simulating
          touch empty
          {zipper} c {deps_zip} empty=empty
        fi
        """.format(zipper = ctx.executable._zipper.path,
                   deps_zip = deps_zip.path),
        arguments = zipPaths,
        outputs = [deps_zip],
    );

    # Build this lib.
    outdir = ctx.actions.declare_directory("output")
    outputs = []
    for src in srcs:
        if src.extension == "purs":
            outputs += [output_file(ctx, "index.js", src, outdir)]
            outputs += [output_file(ctx, "externs.json", src, outdir)]

        if src.extension == "js":
            outputs += [output_file(ctx, "foreign.js", src, outdir)]

    ctx.actions.run_shell(
        inputs = srcs + ps_dep_srcs.to_list() + [deps_zip],
        tools = [purs, zipper],
        command = """
          set -e

          if [ -s {output} ]
          then
              {zipper} x {deps_zip} -d {output}
              chmod -R +w ./*
          fi

          {purs} compile --output {output} $@
        """.format(zipper = ctx.executable._zipper.path,
                   purs = ctx.executable.purs.path,
                   output = outdir.path,
                   deps_zip = deps_zip.path,
                   ),
        arguments = [
            s.path
            for s
            in srcs + ps_dep_srcs.to_list()
            if s.extension == "purs"
        ],
        outputs = outputs + [outdir],
    )

    output_zip = ctx.actions.declare_file("output.zip")
    outputZipPaths = ["%s=%s" % (_path_above_output(p.path), p.path) for p in outputs]
    ctx.actions.run_shell(
      inputs = outputs,
      tools = [zipper],
      command = "{zipper} c {output_zip} $@".format(zipper = ctx.executable._zipper.path, output_zip = output_zip.path),
      arguments = outputZipPaths,
      outputs = [output_zip],
    )

    return [
        DefaultInfo(files = depset(srcs + outputs)),
        OutputGroupInfo(
            srcs = depset(srcs, transitive = [ps_dep_srcs]),
            outputs = depset(outputs, transitive = [ps_dep_outputs]),
            output_zip = [output_zip, deps_zip],
        ),
    ]

purescript_library = rule(
    implementation = _purescript_library,
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
        "_zipper": attr.label(executable=True, cfg="host", default=Label("@bazel_tools//tools/zip:zipper"), allow_files=True)
    },
)

def _trim_package_node_modules(package_name):
    # trim a package name down to its path prior to a node_modules
    # segment. 'foo/node_modules/bar' would become 'foo' and
    # 'node_modules/bar' would become ''
    segments = []
    for n in package_name.split("/"):
        if n == "node_modules":
            break
        segments += [n]
    return "/".join(segments)

def _purescript_bundle(ctx):
    webpack = ctx.executable.webpack
    zipper = ctx.executable._zipper
    srcs = ctx.files.srcs
    dep_outputs = depset(transitive = [dep[OutputGroupInfo].outputs for dep in ctx.attr.deps])
    output_zip = depset(transitive = [dep[OutputGroupInfo].output_zip for dep in ctx.attr.deps])
    files = [z for z in output_zip.to_list()] + [p for p in dep_outputs.to_list()] + [f for f in srcs] + [ctx.file.config] + [ctx.file.entry] + ctx.files.node_modules
    output = ctx.actions.declare_file("dist.zip")

    node_modules_root = "/".join([f for f in [
        ctx.attr.node_modules.label.workspace_root,
        _trim_package_node_modules(ctx.attr.node_modules.label.package),
        "node_modules",
    ] if f])

    ctx.actions.run_shell(
        inputs = files,
        tools = [webpack, zipper],
        command = """
        set -e
        zips=({zips})
        for f in "${{zips[@]}}"; do
          {zipper} x $f -d ./deps
        done
        ln -s {node_modules} .
        {webpack} --config {config} --display errors-only
        for file in $(find dist -type f); do
          files_to_zip="$files_to_zip${{file#dist/}}=$file "
        done
        {zipper} c {output} $files_to_zip
        """.format(webpack = webpack.path,
                   config = ctx.file.config.path,
                   entry = ctx.file.entry.path,
                   node_modules = node_modules_root,
                   zipper = zipper.path,
                   zips = " ".join([z.path for deps in [dep[OutputGroupInfo].output_zip.to_list() for dep in ctx.attr.deps] for z in deps]),
                   output = output.path,
                   ),
        arguments = [],
        outputs = [output],
    );
    return [DefaultInfo(executable = output)]

purescript_bundle = rule(
  implementation = _purescript_bundle,
  attrs = {
    "deps": attr.label_list(
      default = [],
    ),
    "srcs": attr.label_list(
        allow_files = True,
    ),
    "config": attr.label(allow_single_file = True,),
    "entry": attr.label(allow_single_file = True,),
    "node_modules": attr.label(allow_files = True,),
    "webpack": attr.label(
        allow_files = True,
        executable = True,
        cfg = "host",
        # default = "@webpack",
    ),
    "_zipper": attr.label(executable=True, cfg="host", default=Label("@bazel_tools//tools/zip:zipper"), allow_files=True)
  },
)
