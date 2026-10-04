"""Only the distinct reviewed ROOT20 composite gate permits this NEW producer."""
from pathlib import Path
import sys
import bank
import ap
import arithmetic
import outward
import reference
import storage
import integral
import certify


if __name__ == "__main__":
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    expected_parent = Path(__file__).resolve().parent
    for dependency in (bank, ap, arithmetic, outward, reference, storage, integral, certify):
        assert Path(dependency.__file__).resolve().parent == expected_parent
    bank.run()
