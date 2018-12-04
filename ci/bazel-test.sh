#!/usr/bin/env nix-shell
#!nix-shell -p bazel python -i bash -I nixpkgs=https://github.com/input-output-hk/nixpkgs/archive/ce68b263fe25a05a1111acac8ccbe538d139d2dc.tar.gz

set -euo pipefail

echo '~~~ Running tests with Bazel'

command time --format '%e' -o eval-time.txt \
    bazel test --remote_http_cache=https://bazel-cache:"$BAZEL_PASS"@bazel-cache.aws.iohkdev.io/plutus \
               --test_tag_filters "" \
               //...

EVAL_TIME=$(cat eval-time.txt)
rm eval-time.txt

echo -e "\\e[32;1mOK: evaluation completed in $EVAL_TIME seconds with no errors\\e[0m"
