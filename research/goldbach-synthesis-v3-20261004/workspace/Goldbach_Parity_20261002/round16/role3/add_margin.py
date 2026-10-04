from pathlib import Path
p=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round16\role3\EulerAnchor.lean')
s=p.read_text(encoding='utf-8-sig')
s=s.replace('import ThreeAdicPrimePairing','import ThreeAdicPrimePairing\nimport LeastMissingPrimeMargin')
a=s.index('lemma singularSeries_ge_euler_tail')
b=s.index('  have hE :',a)
body=s[s.index('  classical',a):b]
helper='''lemma singularSeries_ge_forced_product {N p : ℕ} (hN : N ≠ 0) (heven : Even N)
    (hp : 3 ≤ p) (hforced : ∀ l, l.Prime → l < p → l ∣ N) :
    2 * GoldbachRound11.twinConstant *
      (∏ l ∈ forcedPrefix p, ((l : ℝ)-1)/((l : ℝ)-2)) ≤ GoldbachRound11.singularSeries N := by
'''+body+'  exact hS\n\n'
header=s[a:s.index('  classical',a)]
s=s[:a]+helper+header+'  have hS := singularSeries_ge_forced_product hN heven hp hforced\n'+s[b:]
s=s[:s.index('#print axioms harmonic_le_eulerPrefix')]
p.write_text(s,encoding='utf-8')
bp=p.parent/'build.py'; bt=bp.read_text(encoding='utf-8-sig'); bt=bt.replace('[W,DEPS,','[W,R/\'round16\'/\'role4\',DEPS,'); bp.write_text(bt,encoding='utf-8')
