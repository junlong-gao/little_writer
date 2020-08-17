#!/bin/bash -ex

function build() {
    PROJ=$1; shift
    pdflatex $PROJ
    bibtex $PROJ || true
    pdflatex $PROJ
    pdflatex $PROJ
}

for proj in "filesystems" \
            "spanner-transaction-and-replication"\
            "consensus-for-replication" \
            "distributed-transactions" \
            "storage-engines-and-rum-conjecture" \
    ;do
    build $proj
done