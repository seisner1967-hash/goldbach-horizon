#!/bin/bash
set -e
echo "=== Goldbach Horizon — Lake Build ==="
echo ""

echo "[0] Checking files..."
FILE_COUNT=$(ls Goldbach/*.lean | wc -l)
echo "  $FILE_COUNT Lean files found"
echo ""

echo "[1] lake update..."
lake update
echo ""

echo "[2] lake exe cache get..."
lake exe cache get
echo ""

echo "[3] Building incrementally..."
for mod in Basic Collage Framework Thresholds Interfaces AxiomsToLemmas \
           Budget G43Budget CompactWindowShadow SmallInstances Roadmap Status \
           ExpBounds A2CertificateData ThresholdReal BreakpointGrid A2Certificate; do
  echo -n "  Goldbach.$mod... "
  if lake build "Goldbach.$mod" 2>/dev/null; then
    echo "ok"
  else
    echo "FAILED"
    exit 1
  fi
done

echo -n "  Goldbach.PrimeLogEnclosures... "
echo "(this may take 10-60 minutes)"
lake build Goldbach.PrimeLogEnclosures

echo ""
echo "[4] Full lake build..."
lake build
echo ""

echo "[5] Sorry/Axiom audit..."
SORRY_COUNT=$(grep -Rnw Goldbach -e '\bsorry\b' --include="*.lean" | wc -l)
AXIOM_COUNT=$(grep -Rn '^axiom ' Goldbach/*.lean | wc -l)
echo "  sorry count:  $SORRY_COUNT"
echo "  axiom count:  $AXIOM_COUNT"

if [ "$SORRY_COUNT" -eq 0 ] && [ "$AXIOM_COUNT" -eq 0 ]; then
  echo "  STATUS: 0 sorry, 0 axiom — clean build"
else
  echo "  STATUS: review needed"
fi
