from pathlib import Path
p=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round16\role3\EulerAnchor.lean')
s=p.read_text(encoding='utf-8-sig')
a=s.index('lemma singularSeries_ge_forced_product');b=s.index('lemma singularSeries_ge_euler_tail',a)
x=s[a:b].replace('(hp : 3 ≤ p)','(_hp : 3 ≤ p)',1)
s=s[:a]+x+s[b:]
s=s[:s.index('#print axioms real_prod_antitone')]
p.write_text(s,encoding='utf-8')
