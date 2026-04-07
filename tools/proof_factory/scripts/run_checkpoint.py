import sys, argparse; sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parents[1]))
from pf.config import load_config
from pf.git_utils import git_commit_all, git_create_tag, git_is_repo
if __name__ == "__main__":
    p = argparse.ArgumentParser(); p.add_argument("--commit",default=None); p.add_argument("--tag",default=None); p.add_argument("--tag-message",default=None)
    args = p.parse_args(); cfg = load_config()
    if not git_is_repo(cfg.repo_root): print("Not a git repo"); sys.exit(1)
    if args.commit: print(f"commit: {'ok' if git_commit_all(cfg.repo_root, args.commit) else 'fail'}")
    if args.tag: print(f"tag: {'ok' if git_create_tag(cfg.repo_root, args.tag, args.tag_message) else 'fail'}")
