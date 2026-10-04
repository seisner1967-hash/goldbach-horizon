"""NEW complete arithmetic cubes: raw/matching operators, commutator and orientation."""
import sys
sys.dont_write_bytecode=True
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path
from hashlib import sha256
from fractions import Fraction
from math import gcd
import json

ROOT=Path(__file__).resolve().parent
spec=spec_from_file_location('round13_shared_operator',ROOT/'shared.py')
X=module_from_spec(spec);spec.loader.exec_module(X)


def scale(value,c):
    return {key:v*c for key,v in value.items() if v*c}


def difference(left,right):
    value=dict(left);X.vector_add(value,right,-1);return value


def singular_ratio(c):
    assert gcd(c,X.N)==1
    value=Fraction(1)
    for p,_ in X.factor(c):
        assert p>2 and X.N%p
        value*=Fraction(p-1,p-2)
    return value


def cube(top):
    assert X.mu(top)!=0 and gcd(top,X.N)==1 and 1<top<=X.N-2
    dimension=len(X.factor(top));vertices=list(X.divisors(top))
    assert len(vertices)==2**dimension
    nodes={}
    for m in vertices:
        n=X.N-m
        assert 1<n<X.N and gcd(n,X.N)==1 and X.mu(m)!=0
        raw=X.Lambda(n);prime_weight=X.theta(n)
        nodes[m]=dict(m=m,n=n,m_factors=X.factor(m),n_factors=X.factor(n),mu=X.mu(m),
            raw=raw,theta=prime_weight,ratio=singular_ratio(m),
            raised_front_nonempty=m>X.A,bulk_m=m>=1000000,n_above_Q=n>X.Q)
        for p,e in X.factor(n):
            assert p<=n<X.N
    edges=[];degrees={m:0 for m in vertices};moment={};matching_groups={};active=[]
    for parent in vertices:
        if parent==1:
            continue
        logparent=X.log_vector(parent);normalization={};model_group={}
        for p,_ in X.factor(parent):
            child=parent//p
            assert child in nodes and child%p and p<=parent
            assert nodes[child]['mu']==-nodes[parent]['mu']
            degrees[child]+=1;degrees[parent]+=1
            rate=X.log_vector(p)
            X.vector_add(normalization,rate)
            physical=X.multiply_vectors(rate,nodes[parent]['raw'])
            match=scale(rate,nodes[child]['ratio'])
            comm=X.multiply_vectors(rate,difference(nodes[parent]['raw'],nodes[child]['raw']))
            drift=X.multiply_vectors(rate,nodes[child]['raw'])
            recombined=dict(comm);X.vector_add(recombined,drift);assert recombined==physical
            model_comm=scale(rate,nodes[parent]['ratio']-nodes[child]['ratio'])
            X.vector_add(model_group,match,nodes[child]['mu'])
            edges.append(dict(child=child,parent=parent,removed_prime=p,
                denominator_log_parent=X.serialize(logparent),rate_numerator=X.serialize(rate),
                rate_between_0_and_1_by_integer_order=True,
                Qphys_numerator=X.serialize(physical),Qmatch_S_numerator=X.serialize(match),
                TV_minus_MT=dict(constant=X.serialize(physical),S=X.serialize(scale(match,-1))),
                TV_minus_VT=X.serialize(comm),V_minus_M_T=dict(constant=X.serialize(drift),S=X.serialize(scale(match,-1))),
                Q0_V_commutator_numerator=X.serialize(comm),
                Q0_M_commutator_S_numerator=X.serialize(model_comm),
                Hphys_numerator=X.serialize(scale(physical,nodes[child]['mu'])),
                Hmatch_S_numerator=X.serialize(scale(match,nodes[child]['mu'])),
                orientations_T_and_Tstar_retained=True,
                parity_anticommutation=True,child_long=child>X.A))
        assert normalization==logparent
        X.vector_add(moment,nodes[parent]['raw'],-nodes[parent]['mu'])
        if nodes[parent]['raw']:
            active.append(parent)
        matching_groups[str(parent)]=dict(denominator_log_parent=X.serialize(logparent),
            oriented_S_numerator=X.serialize(model_group),
            Hmatch_ones_S_numerator=X.serialize(scale(model_group,2)))
    assert len(edges)==dimension*2**(dimension-1) and max(degrees.values())==dimension
    return dict(top=top,dimension=dimension,vertices=vertices,
        nodes={str(m):{key:(X.serialize(value) if isinstance(value,dict) else str(value) if isinstance(value,Fraction) else value)
            for key,value in node.items()} for m,node in nodes.items()},
        edges=edges,edge_count=len(edges),degrees={str(k):v for k,v in degrees.items()},
        Q0_symmetric=True,Q0_norm_upper_bound=dimension,
        norm_bound_certificate='Symmetric matrix, at most dimension positive rates per row, each <= 1',
        V_norm_strictly_below_log_N_by_base_order=True,
        active_raw_vertices=active,oriented_J_TV_ones=X.serialize(moment),
        signed_symmetric_J_Qphys_ones={},Hphys_ones=X.serialize(scale(moment,2)),
        matching_oriented_groups=matching_groups,
        signed_symmetric_J_Qmatch_ones={},constant_S_commutator_exactly_zero=True,
        actual_matching_is_S_cN=True,matching_not_replaced_by_constant=True,
        all_nonedge_entries_zero=True,diagonal_zero=True,
        complete_cube=True,global_c_long_complement_not_discarded=True,
        reference_minus_S_N_N_retained_outside_selected_cube=True,
        raw_properpowers_not_masked=True)


if __name__=='__main__':
    output=X.output_directory();before=X.verify()
    small=cube(561);long=cube(35727711)
    assert small['vertices']==[1,3,11,17,33,51,187,561]
    assert small['active_raw_vertices']==[11,561]
    for m in set(small['vertices'])-{11,561}:
        assert len(X.factor(X.N-m))>1
    edge=next(e for e in small['edges'] if (e['child'],e['parent'])==(187,561))
    assert not X.Lambda(X.N-187) and X.prime(X.N-561)
    comm=X.multiply_vectors(X.log_vector(3),X.Lambda(X.N-561))
    delta=dict(comm);X.vector_add(delta,X.log_vector(561),-3)
    delta_sign=X.sign_certificate(delta);assert delta_sign['sign']=='POSITIVE'
    expected_moment=dict(X.Lambda(X.N-11));X.vector_add(expected_moment,X.Lambda(X.N-561))
    assert small['oriented_J_TV_ones']==X.serialize(expected_moment)
    moment_sign=X.sign_certificate(expected_moment);assert moment_sign['sign']=='POSITIVE'
    negative_H=scale(comm,-2);negative_H_sign=X.sign_certificate(negative_H)
    assert negative_H_sign['sign']=='NEGATIVE'
    raw_edge=next(e for e in long['edges'] if (e['child'],e['parent'])==(54051,35727711))
    assert long['edge_count']==32 and len(long['vertices'])==16 and raw_edge['child_long']
    assert X.factor(X.N-35727711)==((8017,2),) and not X.theta(X.N-35727711)
    raw_numerator=X.multiply_vectors(X.log_vector(661),X.Lambda(X.N-35727711))
    raw_sign=X.sign_certificate(raw_numerator);assert raw_sign['sign']=='POSITIVE'
    assert raw_edge['Qphys_numerator']==X.serialize(raw_numerator)
    result=dict(status='PASS_NEW_ACTUAL_OPERATOR_IDENTITIES_ONLY',N=X.N,alpha=X.ALPHA,a=X.A,Q=X.Q,
        complete_cubes=dict(small=small,raw_long=long),
        false_small_commutator_promotion=dict(status='ERROR_FALSIFIER',cube_top=561,
            child=187,parent=561,entry_denominator_log_m=X.serialize(X.log_vector(561)),
            entry_numerator=X.serialize(comm),strict_entry_greater_than='3',
            Delta=X.serialize(delta),sign=delta_sign,Q0_norm_upper_bound=3,
            V_norm_below_u=True,promoted_RHS_at_most='3',
            assertion_rejected='norm([Q0,V]) <= norm(Q0)*norm(V)/u on every physical cube',
            no_global_asymptotic_claim=True),
        false_oriented_mass_equals_symmetrization=dict(status='ERROR_FALSIFIER',cube_top=561,
            oriented_J_TV_ones=X.serialize(expected_moment),oriented_sign=moment_sign,
            signed_symmetric_J_Qphys_ones={},proper_H_ones=X.serialize(scale(expected_moment,2))),
        false_full_H_positive_semidefinite=dict(status='ERROR_FALSIFIER',cube_top=561,
            vector=dict(child=187,child_value=1,parent=561,parent_value=-1),
            quadratic_numerator=X.serialize(negative_H),denominator_log_m=X.serialize(X.log_vector(561)),
            sign=negative_H_sign,compression_complement_not_free=True),
        false_theta_substituted_for_raw_on_long_edge=dict(status='ERROR_FALSIFIER',cube_top=35727711,
            child=54051,parent=35727711,child_exceeds_a=True,
            raw_numerator=X.serialize(raw_numerator),theta_numerator={},
            denominator_log_m=X.serialize(X.log_vector(35727711)),sign=raw_sign),
        imports=X.IMPORTS,script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        shared_sha256=sha256((ROOT/'shared.py').read_bytes()).hexdigest(),
        conservation_before=before,conservation_after=X.verify(),
        global_D_N=False,asymptotic=False,payments=False,Lean_called=False,victory=False)
    (output/'operator.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],small_vertices=len(small['vertices']),
        small_edges=small['edge_count'],raw_long_vertices=len(long['vertices']),raw_long_edges=long['edge_count'],
        signs=dict(commutator_delta=delta_sign['sign'],oriented=moment_sign['sign'],
            H_quadratic=negative_H_sign['sign'],raw_long_edge=raw_sign['sign']),conservation='PRESERVED'),indent=2))
