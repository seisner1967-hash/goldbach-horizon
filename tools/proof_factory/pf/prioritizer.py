from __future__ import annotations
from collections import defaultdict
from pf.models import Goal

WEIGHTS = {"numeric":1,"bridge":2,"structural":3,"analytic_deep":10,"unknown":50}

def prioritize_goals(goals, *, category=None, remaining_only=True):
    items = goals[:]
    if remaining_only: items = [g for g in items if g.status in {"open","failed","attempting","stubbed"}]
    if category: items = [g for g in items if g.category == category]
    items.sort(key=lambda g: (WEIGHTS.get(g.category,50), g.difficulty, g.file, g.line_start))
    return items
