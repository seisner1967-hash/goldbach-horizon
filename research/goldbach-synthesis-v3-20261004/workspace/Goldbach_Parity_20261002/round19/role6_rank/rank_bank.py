"""NEW complete conductor/candidate bank.  No mathematics runs on import."""
from collections import Counter
from fractions import Fraction
import gzip
from hashlib import sha256
import json
from math import gcd
from pathlib import Path

from strict_rank import (N,A,Q,M,H,P,LEFT,RIGHT,START,BITS,SCALE,S_BOX,Strict,
                         ceildiv,fracstr,scaled_bounds,scale,mul,cert,interval_data,addvec)


def expression_vector(bases, expression):
    vector = {}
    for name, coefficient in expression.items():
        addvec(vector, bases[name], coefficient)
    return vector


def clean_expression(value):
    return {name: coefficient for name, coefficient in value.items() if coefficient}


def expression_data(value):
    return {name: fracstr(coefficient) for name, coefficient in sorted(value.items()) if coefficient}


def exact_vector_digest(vector):
    h = sha256()
    for base, value in sorted(vector.items()):
        h.update(f"{base}:{value.numerator}/{value.denominator}\n".encode("ascii"))
    return h.hexdigest()


def affine_certificate(constant_bounds, coefficient_bounds, exact_zero=False):
    endpoints = []
    for value in S_BOX:
        lo, hi = scale(coefficient_bounds,value)
        bounds = constant_bounds[0]+lo, constant_bounds[1]+hi
        endpoints.append({"S":fracstr(value),"certificate":cert(bounds,exact_zero)})
    lo = min(int(v["certificate"]["lower_scaled"]) for v in endpoints)
    hi = max(int(v["certificate"]["upper_scaled"]) for v in endpoints)
    sign = "ZERO" if exact_zero else ("POSITIVE" if lo>0 else "NEGATIVE" if hi<0 else "PARAMETER_BOX_MAY_CHANGE_SIGN")
    return {"acquired_S_box":[fracstr(v) for v in S_BOX],"endpoint_certificates":endpoints,
            "whole_box_enclosure":interval_data((lo,hi)),"whole_box_sign":sign,
            "exact_zero":exact_zero,"affine_in_S_no_new_S_evaluation":True}


def accumulator():
    return {"constant":[0,0],"coefficient":[0,0],"all_exact_zero":True}


def accumulate(state, constant, coefficient, exact_zero):
    for i in (0,1):
        state["constant"][i] += constant[i]
        state["coefficient"][i] += coefficient[i]
    state["all_exact_zero"] = state["all_exact_zero"] and exact_zero


def beta_support(st,c,r,d,prime_flags,proper_map):
    lo_m, hi_m = N-RIGHT,N-LEFT-1
    result = {}
    for s in st.primes:
        if s<=r or c*s>A or gcd(s,N)!=1 or r*s<=A or c*r*s<=A:
            continue
        low = max(A+1,r*s+1,ceildiv(lo_m,d*s))
        high = min(10000,hi_m//(d*s))
        for q in st.primes:
            if q<low:
                continue
            if q>high:
                break
            if gcd(q,N)!=1:
                continue
            b,m = s*q,d*s*q
            j=N-m
            assert c<r<s<=A<q and c*r<=A and c*s<=A<r*s<q and c*r*s>A
            assert M<=m and m+Q<N and gcd(m,N)==1 and LEFT<j<=RIGHT
            assert q*3*A<88000000 and s<=A//3<1055
            assert b not in result
            result[b] = {"b":b,"m":m,"j":j,"prime_factors_c_r_s_q":[c,r,s,q],
                         "candidate_prime_indicator":bool(prime_flags[j-START]),
                         "candidate_properpower":proper_map.get(j),
                         "physical_mask_has_no_candidate_prime_filter":True}
    return result


def run_bank(output_directory):
    st=Strict()
    assert gcd(P,N*H)==1 and P==7*11*23 and all(p*p<=A for p in (7,11,23))
    assert Q==(N-1)//100 and (A-1)**16<N**7<=A**16
    assert 1**32<N<=2**32
    cuts=(2,17)
    flags,base_sieve,proper=st.candidate_sieve()
    proper_map={j:[p,k] for j,p,k in proper}
    out=Path(output_directory)
    bitpacked=bytearray((RIGHT-LEFT+7)//8)
    for i,value in enumerate(flags):
        if value:
            bitpacked[i//8]|=1<<(i%8)
    bitmap=out/"all_12000000_candidate_prime_bits.bin.gz"
    with bitmap.open("xb") as handle:
        handle.write(gzip.compress(bytes(bitpacked),mtime=0))
    bitmap_meta={"path":str(bitmap),"bytes":bitmap.stat().st_size,
                 "sha256":sha256(bitmap.read_bytes()).hexdigest(),
                 "uncompressed_sha256":sha256(bitpacked).hexdigest(),
                 "bit_order":"least significant bit, index j-12000001",
                 "integer_axes":RIGHT-LEFT,"left_exclusive":LEFT,"right_inclusive":RIGHT,
                 "full_prime_count":sum(flags),"all_base_primes_through_sqrt_right":base_sieve,
                 "all_nonprime_axes_are_retained_by_domain_and_bit0":True}
    pairs=[(c,r,c*r) for c in st.primes for r in st.primes
           if c<r and c*r<=A and gcd(c*r,N)==1]
    assert pairs==sorted(set(pairs))
    e0=st.rad(H)//gcd(st.rad(H),N)
    delta0=Fraction(st.phi(N*H),N*H)
    divisor_catalog, fibers, physical, modules = {}, [], {}, {str(R):{} for R in cuts}
    global_components={measure:{} for measure in ("theta","raw","properpower")}
    counts=Counter()
    chi_values={t:Fraction(t-st.phi(t),st.phi(t)*(t-1)) for t in (7,11,23,77,161,253,1771)}
    assert min(chi_values.values())==Fraction(451,2336400)
    cstar=Fraction(143,384)*Fraction(451,2336400)
    assert cstar==Fraction(64493,897177600)
    for c,r,d in pairs:
        blo,bhi=ceildiv(N-RIGHT,d),ceildiv(N-LEFT,d)-1
        length=max(0,bhi-blo+1)
        assert length>0
        nlo,nhi=N-d*bhi,N-d*blo
        xwidth=nhi-nlo+1
        assert xwidth==d*(length-1)+1 and xwidth<=d*length
        pd=P//gcd(P,d)
        assert pd>1 and gcd(pd,N*H*d)==1 and pd in chi_values
        beta=beta_support(st,c,r,d,flags,proper_map)
        mass=len(beta)
        reference_moduli={"U0":N*H,"U":N*H*d,"Uprime":N*H*d}
        for R in cuts:
            ds=1
            for p in (c,r):
                if p<=R:
                    ds*=p
            reference_moduli[f"Us{R}"]=N*H*ds
            reference_moduli[f"Usprime{R}"]=N*H*ds
        reference_names=list(reference_moduli)
        rad_units={name:st.rad(modulus) for name,modulus in reference_moduli.items()}
        ie_records,cardinalities={},{}
        for name,modulus in reference_moduli.items():
            face=pd if "prime" in name else 1
            # Outside-face references are J-J_F, never J_F itself.
            total,ie=st.unit_ie(blo,bhi,modulus)
            face_count,face_ie=st.unit_ie(blo,bhi,modulus,pd)
            cardinalities[name]=total-face_count if face==pd else total
            original=ie.pop("complete_divisors_including_mu0")
            face_original=face_ie.pop("complete_divisors_including_mu0")
            assert original==face_original
            if str(modulus) in divisor_catalog:
                assert divisor_catalog[str(modulus)]==original
            else:
                divisor_catalog[str(modulus)]=original
            ie["complete_divisors_ref"]=str(modulus)
            face_ie["complete_divisors_ref"]=str(modulus)
            ie_records[name]={"unit_count":ie,"face_count":face_ie,
                              "outside_face":face==pd,"actual_reference_count":cardinalities[name]}
        bases={measure:{name:{} for name in ["beta"]+reference_names}
               for measure in ("theta","raw","properpower")}
        measured_counts=Counter()
        prime_members,pp_members=[],[]
        for b in range(blo,bhi+1):
            j=N-d*b
            assert LEFT<j<=RIGHT and (P%(gcd(P,d)))==0
            onface=b%pd==0
            assert (d*b)%P==0 if onface else (d*b)%P!=0
            selected={name:gcd(b,rad_units[name])==1 and (not onface if "prime" in name else True)
                      for name in reference_names}
            for name,yes in selected.items():
                measured_counts[name]+=yes
            is_beta=b in beta
            if is_beta:
                assert selected["Uprime"] and not onface and all(selected.values())
            prime=bool(flags[j-START])
            pp=proper_map.get(j)
            if prime or pp:
                mask=sum((1<<i) for i,name in enumerate(reference_names) if selected[name])
                record=[j,b,mask,int(is_beta)]
                if prime:
                    prime_members.append(record)
                else:
                    pp_members.append(record+pp)
                raw_base=j if prime else pp[0]
                raw_active=gcd(j,N)==1
                for name,yes in [("beta",is_beta)]+list(selected.items()):
                    if not yes or not raw_active:
                        continue
                    bases["raw"][name][raw_base]=bases["raw"][name].get(raw_base,0)+1
                    measure="theta" if prime else "properpower"
                    bases[measure][name][raw_base]=bases[measure][name].get(raw_base,0)+1
        assert all(measured_counts[name]==cardinalities[name] for name in reference_names)
        assert mass<=min(cardinalities.values())
        for name in bases["raw"]:
            split={}
            addvec(split,bases["theta"][name])
            addvec(split,bases["properpower"][name])
            assert split==bases["raw"][name]
        rho={name:Fraction(mass,J) if J else Fraction(0) for name,J in cardinalities.items()}
        assert all(value<=1 for value in rho.values())
        assert all(J or mass==0 for J in cardinalities.values())
        expressions={
            "Gamma0":{"beta":Fraction(1),"U0":-rho["U0"]},
            "Gamma_rank":{"beta":Fraction(1),"Uprime":-rho["Uprime"]},
            "E_unit":{"U":rho["U"],"U0":-rho["U0"]},
            "L_rank":{"Uprime":rho["Uprime"],"U":-rho["U"]},
            "Pi":{"Uprime":rho["Uprime"],"U0":-rho["U0"]}}
        for R in cuts:
            expressions[f"Pi_small_R{R}"]={f"Usprime{R}":rho[f"Usprime{R}"],"U0":-rho["U0"]}
            expressions[f"large_unit_difference_R{R}"]={"Uprime":rho["Uprime"],f"Usprime{R}":-rho[f"Usprime{R}"]}
        expressions={name:clean_expression(expr) for name,expr in expressions.items()}
        component_data={measure:{} for measure in bases}
        component_vectors={measure:{} for measure in bases}
        for measure in bases:
            for name,expr in expressions.items():
                vector=expression_vector(bases[measure],expr)
                component_vectors[measure][name]=vector
                bounds=st.vector_bounds(vector)
                zero=not vector
                constant=mul(st.log(c),bounds)
                data={"exact_basis_expression":expression_data(expr),"basis_measure":measure,
                      "exact_prime_log_vector_sha256":exact_vector_digest(vector),
                      "inner_certificate":cert(bounds,zero),
                      "weighted_kappa_affine_certificate":affine_certificate(constant,bounds,zero)}
                component_data[measure][name]=data
                state=global_components[measure].setdefault(name,accumulator())
                accumulate(state,constant,bounds,zero)
            k4={}
            addvec(k4,component_vectors[measure]["Gamma_rank"])
            addvec(k4,component_vectors[measure]["Pi"])
            assert k4==component_vectors[measure]["Gamma0"]
            k4={}
            addvec(k4,component_vectors[measure]["E_unit"])
            addvec(k4,component_vectors[measure]["L_rank"])
            assert k4==component_vectors[measure]["Pi"]
        for name in expressions:
            split={}
            addvec(split,component_vectors["theta"][name])
            addvec(split,component_vectors["properpower"][name])
            assert split==component_vectors["raw"][name]
        ap_catalog,ap_index_sets,cut_records={},{},{}
        def ap(multiplier):
            key=str(multiplier)
            if key not in ap_catalog:
                module=d*multiplier
                assert gcd(N,module)==1
                members=[i for i,(_,b,_,_) in enumerate(prime_members) if b%multiplier==0]
                ap_index_sets[key]=set(members)
                vector={prime_members[i][0]:Fraction(1) for i in members}
                theta_bounds=st.vector_bounds(vector)
                principal=Fraction(xwidth,st.phi(module))
                pl,ph=scaled_bounds(principal)
                error=(theta_bounds[0]-ph,theta_bounds[1]-pl)
                ap_catalog[key]={"module":module,"residue_N_mod_module":N%module,
                                 "real_interval_nlo_nhi":[nlo,nhi],"X":xwidth,
                                 "prime_member_indices":members,"unmasked_theta_count":len(members),
                                 "X_over_phi_module":fracstr(principal),
                                 "interval_AP_error_certificate":cert(error),
                                 "prime_divisors_of_N_exception_mass":0,
                                 "exception_reason":"2,5 lie strictly below nlo",
                                 "this_is_an_interval_error_not_BV_or_global_Etheta":True}
            return ap_catalog[key]
        a0=sum((Fraction(st.mu(k),st.phi(d*k)) for k in st.divisors(e0)),Fraction(0))
        md=Fraction(mass*xwidth,length)*a0/delta0
        principal_inner=-md*chi_values[pd]
        assert md>=Fraction(143*mass,384) if length>=2 else True
        principal_constant=scale(st.log(c),principal_inner)
        principal_coefficient=scaled_bounds(principal_inner)
        principal_weight=affine_certificate(principal_constant,principal_coefficient,not principal_inner)
        principal_state=global_components["theta"].setdefault("Pi_principal",accumulator())
        accumulate(principal_state,principal_constant,principal_coefficient,not principal_inner)
        for R in cuts:
            ds=1
            for p in (c,r):
                if p<=R:
                    ds*=p
            hs=N*H*ds
            es=st.rad(H*ds)//gcd(st.rad(H*ds),N)
            deltas=Fraction(st.phi(hs),hs)
            asmall=sum((Fraction(st.mu(k),st.phi(d*k)) for k in st.divisors(es)),Fraction(0))
            assert asmall/deltas==a0/delta0
            qr=H*P*max(A*R,R**4)
            expansions={"T0":[],"Ts":[],"TFs":[]}
            for kind,radical,face in (("T0",e0,1),("Ts",es,1),("TFs",es,pd)):
                for k in st.divisors(radical):
                    t=1
                    for p in (3,13):
                        if k%p==0:
                            t*=p
                    ks=k//t
                    assert ds%ks==0 and gcd(ks,H)==1
                    module=d*k*face
                    f=t*face
                    assert module==d*ks*f and (H*P)%f==0
                    assert d*ks<=max(A*R,R**4) and module<=qr
                    recovered=st.factor_small_product(module//f)
                    assert sorted(set(recovered))==[c,r]
                    recovered_d=c*r
                    recovered_ks=1
                    for p in (c,r):
                        assert recovered.count(p) in (1,2)
                        if recovered.count(p)==2:
                            recovered_ks*=p
                    assert (recovered_d,recovered_ks)==(d,ks)
                    representation={"kind":kind,"R":R,"d":d,"c":c,"r":r,"k":k,
                                    "k_s":ks,"t_divisor39":t,"P_d":pd,"face_multiplier":face,
                                    "fixed_f_divisor39P":f,"mu_k":st.mu(k),"module":module,
                                    "factor_recovery_d_ks_verified":True}
                    modules[str(R)].setdefault(str(module),[]).append(representation)
                    value=ap(k*face)
                    expansions[kind].append({"k":k,"mu":st.mu(k),"AP_multiplier_ref":str(k*face)})
                    assert value["module"]==module
            for index,(j,b,_,_) in enumerate(prime_members):
                for kind,ref,face in (("T0","U0",1),("Ts",f"Us{R}",1),("TFs",f"Us{R}",pd)):
                    ie_value=sum(v["mu"] for v in expansions[kind] if index in ap_index_sets[v["AP_multiplier_ref"]])
                    target=int(gcd(b,rad_units[ref])==1 and b%face==0)
                    assert ie_value==target
            lost=cardinalities[f"Usprime{R}"]-cardinalities["Uprime"]
            assert lost>=0
            large=[p for p in (c,r) if p>R]
            plus1=sum((Fraction(length,p)+1 for p in large),Fraction(0))
            assert lost<=plus1<=2*(Fraction(length,R)+1)
            sharpened=Fraction(mass*lost,cardinalities[f"Usprime{R}"]) if cardinalities[f"Usprime{R}"] else Fraction(0)
            difference=component_vectors["theta"][f"large_unit_difference_R{R}"]
            diff_bounds=st.vector_bounds(difference)
            bound=scale(st.log(N),sharpened)
            assert max(abs(diff_bounds[0]),abs(diff_bounds[1]))<=bound[0] if sharpened else not difference
            rho_s=rho[f"Usprime{R}"]
            rho_0=rho["U0"]
            r_s=Fraction(mass,length)/deltas/(1-Fraction(1,pd))
            r_0=Fraction(mass,length)/delta0
            error_bound=Fraction(0)
            for kind,coefficient in (("Ts",rho_s),("TFs",rho_s),("T0",rho_0)):
                for entry in expansions[kind]:
                    error=ap_catalog[entry["AP_multiplier_ref"]]["interval_AP_error_certificate"]
                    error_bound+=coefficient*Fraction(max(abs(int(error["lower_scaled"])),abs(int(error["upper_scaled"]))),SCALE)
            error_bound+=abs(rho_s-r_s)*xwidth*asmall*(1-Fraction(1,st.phi(pd)))
            error_bound+=abs(rho_0-r_0)*xwidth*a0
            pis_bounds=st.vector_bounds(component_vectors["theta"][f"Pi_small_R{R}"])
            pl,ph=scaled_bounds(principal_inner)
            discrepancy=(pis_bounds[0]-ph,pis_bounds[1]-pl)
            # The REAL triangle bound is error_bound.  A separate, explicit
            # interval-rounding allowance certifies a potentially tight bound
            # when independent enclosing computations touch its endpoint.
            rounding_allowance=Fraction((pis_bounds[1]-pis_bounds[0])+(ph-pl),SCALE)
            measured_error_bounds=scaled_bounds(error_bound+rounding_allowance)
            assert max(abs(discrepancy[0]),abs(discrepancy[1]))<=measured_error_bounds[1]
            pi_bounds=st.vector_bounds(component_vectors["theta"]["Pi"])
            full_rounding_allowance=rounding_allowance+Fraction(pi_bounds[1]-pi_bounds[0],SCALE)
            total_error=error_bound+Fraction(bound[1],SCALE)+full_rounding_allowance
            assert max(abs(pi_bounds[0]-ph),abs(pi_bounds[1]-pl))<=scaled_bounds(total_error)[1]
            cut_records[str(R)]={"R":R,"is_source_R":R==2,"d_s":ds,"H_s":hs,"e_s":es,
                "delta_s":fracstr(deltas),"a_s":fracstr(asmall),"a_s_over_delta_s_equals_a0_over_delta0":True,
                "Q_R_exact_integer_level":qr,"IE_AP_expansions":expansions,
                "lost_integer_count":lost,"large_primes_removed":large,"large_unit_plus1_bound":fracstr(plus1),
                "K6_sharpened_A_lost_over_Jsprime":fracstr(sharpened),
                "K6_logN_times_sharpened_bound":interval_data(bound),"K6_actual_normalized_loss_verified":True,
                "K7_with_each_plus1_verified":True,"normalization_rho_sprime":fracstr(rho_s),
                "normalization_rho0":fracstr(rho_0),"principal_r_sprime":fracstr(r_s),"principal_r0":fracstr(r_0),
                "measured_AP_plus_actual_normalization_error_bound":fracstr(error_bound),
                "small_price_computational_rounding_allowance":fracstr(rounding_allowance),
                "full_price_computational_rounding_allowance":fracstr(full_rounding_allowance),
                "literal_small_price_minus_principal_enclosure":interval_data(discrepancy),
                "full_Pi_minus_principal_bound_with_large_units":fracstr(total_error),
                "literal_finite_error_dominates_actual_price_minus_principal":True,
                "source_normalization_guards":{"L_ge2":length>=2,
                    "L_delta_s_ge4_eta_s":length*deltas>=4*ie_records[f"Us{R}"]["unit_count"]["eta"],
                    "L_delta0_ge4_eta0":length*delta0>=4*ie_records["U0"]["unit_count"]["eta"]},
                "BV_and_source_onset_not_applied":True}
        for b,entry in beta.items():
            assert entry["m"] not in physical
            physical[entry["m"]]={"d":d,"c":c,"r":r,"b":b,"j":entry["j"],"factors":entry["prime_factors_c_r_s_q"]}
        # Face principal is literally nonpositive because every beta on it is zero.
        face_prime=[row[0] for row in prime_members if row[1]%pd==0 and gcd(row[1],rad_units["U0"])==1]
        face_pp=[row[4] for row in pp_members if row[1]%pd==0 and gcd(row[1],rad_units["U0"])==1]
        assert all(entry["m"]%P!=0 for entry in beta.values())
        fiber={"c":c,"r":r,"d":d,"b_interval_complete":[blo,bhi],"L":length,"real_j_interval":[nlo,nhi],"X":xwidth,
               "P_d":pd,"P_sharing_count":sum(d%p==0 for p in (7,11,23)),"A_beta":mass,
               "all_beta_physical_witnesses":list(beta.values()),"reference_mask_bit_names":reference_names,
               "reference_unit_moduli":reference_moduli,"reference_counts":cardinalities,"reference_IE_counts":ie_records,
               "all_prime_member_rows_j_b_mask_beta":prime_members,
               "all_properpower_member_rows_j_b_mask_beta_base_exponent":pp_members,
               "coefficients_A_over_J_empty_zero":{name:fracstr(value) for name,value in rho.items()},
               "actual_components":component_data,"AP_interval_catalog_by_b_multiplier":ap_catalog,"two_R_cuts":cut_records,
               "a0":fracstr(a0),"delta0":fracstr(delta0),"M_d":fracstr(md),"chi_Pd":fracstr(chi_values[pd]),
               "Pi_principal_inner":fracstr(principal_inner),"Pi_principal_weighted":principal_weight,
               "face_prime_members_U0":face_prime,"face_raw_properpower_bases_U0":face_pp,
               "K1_beta_face_impossible_on_all_physical_images":True,"K2_face_Gamma0_theta_raw_nonpositive":True,
               "K3_P_divides_db_iff_Pd_divides_b_all_integer_axes":True,
               "K4_all_prices_and_K20_raw_split_exact_prime_log_coefficients":True,
               "all_empty_reference_branches_force_A0":True,"all_nonprime_b_axes_retained":True}
        fibers.append(fiber)
        counts["fibers"]+=1
        counts["all_integer_b_axes"]+=length
        counts["physical_beta_images"]+=mass
        counts["fibers_A0"]+=mass==0
        counts[f"P_d={pd}"]+=1
        counts["beta_prime_candidate_images"]+=sum(entry["candidate_prime_indicator"] for entry in beta.values())
        counts["beta_properpower_candidate_images"]+=sum(bool(entry["candidate_properpower"]) for entry in beta.values())
        if counts["fibers"]%50==0:
            print(json.dumps({"phase":"NEW_ALL_RANK_BANK_IN_PROGRESS","completed_fibers":counts["fibers"],
                              "all_integer_b_axes_so_far":counts["all_integer_b_axes"],
                              "physical_beta_images_so_far":counts["physical_beta_images"]}),flush=True)
    return finish(st,out,bitmap_meta,proper,pairs,fibers,physical,modules,divisor_catalog,global_components,counts,chi_values,cstar)


def finish(st,out,bitmap_meta,proper,pairs,fibers,physical,modules,divisors,components,counts,chi_values,cstar):
    # Kept separate to make all serialization and final checks inspectable.
    module_meta={}
    for R,catalog in modules.items():
        maximum=max((len(values) for values in catalog.values()),default=0)
        assert maximum<=40<=64
        module_meta[R]={"all_module_representations":catalog,"distinct_modules":len(catalog),
                        "max_actual_representation_multiplicity":maximum,"bounded_by40_and64":True,
                        "all_T0_Ts_TFs_entries_retained":True}
    actual={measure:{name:affine_certificate(tuple(state["constant"]),tuple(state["coefficient"]),state["all_exact_zero"])
                     for name,state in values.items()} for measure,values in components.items()}
    logs_path=out/"strict_primitive_log_enclosures.jsonl.gz"
    with logs_path.open("xb") as file_handle:
        with gzip.GzipFile(fileobj=file_handle,mode="wb",mtime=0) as zipped:
            for n,(lo,hi) in sorted(st.logs.items()):
                zipped.write(f"[{n},\"{lo}\",\"{hi}\"]\n".encode("ascii"))
    logs_meta={"path":str(logs_path),"sha256":sha256(logs_path.read_bytes()).hexdigest(),
               "bytes":logs_path.stat().st_size,"primitive_log_count":len(st.logs),"dyadic_bits":BITS,
               "rows":"[integer_n,lower_scaled_decimal_string,upper_scaled_decimal_string]",
               "method":"positive_atanh48_with_integer_outward_rounding_and_geometric_tail",
               "range_reduction":"log n = bit_length_exponent*log2 + 2*atanh((n-2^exponent)/(n+2^exponent))",
               "no_floats_or_hidden_old_log_cache":True}
    assert len(physical)==counts["physical_beta_images"] and len(fibers)==len(pairs)
    source_log_bounds=st.log(N)
    assert source_log_bounds[1]<(10**24)*SCALE
    examples={}
    def record(name,values):
        examples[name]={"status":"COUNTEREXAMPLE" if values else "NO_COUNTEREXAMPLE_IN_BANK",
                        "first_example":values[0] if values else None,"finite_only":True}
    record("replace_Pd_by_P_despite_shared_P",[{"d":f["d"],"P_d":f["P_d"],"P":P}
           for f in fibers if f["P_d"]!=P])
    record("Pi_measured_zero_by_face_removal",[{"d":f["d"],"Pi":f["actual_components"]["theta"]["Pi"]}
           for f in fibers if not f["actual_components"]["theta"]["Pi"]["inner_certificate"]["exact_zero"]])
    record("X_equals_dL_front_erased",[{"d":f["d"],"L":f["L"],"X":f["X"],"d_times_L":f["d"]*f["L"]}
           for f in fibers if f["X"]!=f["d"]*f["L"]])
    record("d_and_ks_always_disjoint",[v for catalog in modules.values() for values in catalog.values()
           for v in values if gcd(v["d"],v["k_s"])>1])
    record("omit_PP_price",[{"d":f["d"],"PP_Pi":f["actual_components"]["properpower"]["Pi"]}
           for f in fibers if not f["actual_components"]["properpower"]["Pi"]["inner_certificate"]["exact_zero"]])
    examples["Rtest_or_BV_onset_equals_source"]={"status":"GUARD_FALSE_NOT_APPLIED",
        "R_source":2,"R_test":17,"logN_10power24_guard":False,"BV_onset_unknown":True}
    counts["all_candidate_integer_axes"]=RIGHT-LEFT
    counts["all_candidate_primes"]=bitmap_meta["full_prime_count"]
    counts["all_candidate_properpowers"]=len(proper)
    return {"round":19,"role":6,"node":"13.11","status":"PASS_NEW_ALL_RANK_FINITE_IDENTITIES_ONLY",
            "N":N,"candidate_domain_left_exclusive_right_inclusive":[LEFT,RIGHT],
            "fixed_parameters":{"alpha":100,"a":A,"Q":Q,"M":M,"h":H,"P":P},
            "all_prime_pairs_c_lt_r_unit_N_cr_le_a":pairs,"counts":dict(counts),
            "candidate_full_domain_prime_bitmap":bitmap_meta,
            "all_candidate_properpowers_value_primebase_exponent_including_nonunits":proper,
            "all_conductor_fibers":fibers,"all_complete_original_IE_divisors_including_mu0":divisors,
            "physical_beta_union_unique":{str(m):value for m,value in sorted(physical.items())},
            "all_AP_modules_representations_level_and_multiplicity":module_meta,
            "global_actual_affine_functionals_theta_raw_PP":actual,
            "chi_exact_cases":{str(t):fracstr(value) for t,value in chi_values.items()},
            "chi_min":fracstr(min(chi_values.values())),"C_star":fracstr(cstar),
            "strict_primitive_log_catalog":logs_meta,"falsifiers":examples,
            "all_integer_axes_and_nonprime_beta_retained":True,
            "K4_Gamma0_Gammarank_Pi_and_unit_rank_prices_exact":True,
            "K20_raw_theta_properpower_split_exact":True,"K6_K7_actual_normalized_loss_checked_both_R":True,
            "literal_measured_interval_AP_errors_not_BV":True,"source_onset_logN_10power24_applied":False,
            "Gamma_rank_DN_global_capacity_bound_proved":False,"W_D_kernel_or_parent_resource_evaluations":0,
            "old_producer_preflight_Lean_PDF_replays":0,"victory":False}
