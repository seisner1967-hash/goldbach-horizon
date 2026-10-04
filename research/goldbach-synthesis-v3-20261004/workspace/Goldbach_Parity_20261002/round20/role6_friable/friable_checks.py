"""NEW canonical friable20 entry point; never called before explicit root gate."""
from __future__ import annotations

import sys

sys.set_int_max_str_digits(0)

from bank import run


if __name__ == "__main__":
    run()
