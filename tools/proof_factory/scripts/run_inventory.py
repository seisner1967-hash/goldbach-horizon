import sys; sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parents[1]))
from main import cmd_inventory
if __name__ == "__main__": cmd_inventory()
