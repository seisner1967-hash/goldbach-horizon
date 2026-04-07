import sys, json; sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parents[1]))
from pf.config import load_config
from pf.models import Goal
from pf.status_board import render_status_board, load_jsonl
if __name__ == "__main__":
    cfg = load_config()
    goals = [Goal.from_dict(x) for x in json.loads(cfg.goals_path.read_text(encoding="utf-8"))] if cfg.goals_path.exists() else []
    board = render_status_board(goals, load_jsonl(cfg.attempts_path), load_jsonl(cfg.builds_path))
    print(board)
    (cfg.state_dir / "status_board.txt").write_text(board, encoding="utf-8")
