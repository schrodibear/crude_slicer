#!/bin/bash

OTHER=()
while [[ $# -gt 0 ]]; do
    key="$1"
    case $key in
        -ldv-bam-svcomp|-sv-comp17-bam-bnb|-skipRecursion|-32|-64|-noout|-stats)
            OTHER+=("$1")
            shift
            ;;
        -spec)
            PROPERTYFILE="$2"
            shift # past argument
            shift # past value
            ;;
        -*)
            OTHER+=("$1" "$2")
            shift # past argument
            shift # past value
            ;;
        *)
            TASK="$1"
            shift
            ;;
    esac
done

if [[ ! -f "$PROPERTYFILE" ]] || grep -q 'CHECK(.*,.*LTL(G.*!.*call(.*).*).*)' "$PROPERTYFILE"; then
    if [[ ! -f "$PROPERTYFILE" ]]; then
        PROPERTYFILE=config/specification/sv-comp-reachability.spc
    fi
    STASK="${TASK}.sliced.c"

    ./frama-c-Crude_slicer.native \
        -machdep gcc_x86_64 \
        -crude_slicer \
        -timeout 400 \
        -no-recognize_wrecked_container_of \
        -widening_threshold 2000 \
        -no-summaries \
        -no-assert_stratification \
        -print \
        -ocode ${STASK} \
        ${TASK}

    if [[ ! -f "${STASK}" ]]; then
        STASK="${TASK}"
    fi
    rm -rf "$(find . -name '**.graphml')"

    ./scripts/cpa.sh "${OTHER[@]}" -spec "${PROPERTYFILE}" "${STASK}"

    IWITNESSFILE=$(find . -name "**.graphml")
    if [[ -f "${IWITNESSFILE}" ]]; then
        OWITNESSFILE="$(dirname ${IWITNESSFILE})/restored_$(basename ${IWITNESSFILE})"
        ./filter_witness.native \
            -progfile "${TASK}" \
            -o "${OWITNESSFILE}" \
            "${IWITNESSFILE}"
    fi
    rm -rf "${IWITNESSFILE}"
else
    echo "Verification result: UNKNOWN"
    exit 0
fi
