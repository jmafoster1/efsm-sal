theory xxxmotorcontrolimprovedTheorems_hand
  imports XXXMotorControlImproved "../theories/efsm-ltl/EFSM_LTL"
begin

theorem mustDoreleaseOld : "(alw
        (((label_eq ''feed'') or (label_eq ''pass'')) impl
        (nxt (ev ((label_eq ''feed'') or (label_eq ''pass'')) aand (nxt (not (state_eq None)))))) impl
        (nxt (label_eq ''release''))
     ) (watch thegraph i)"
  oops

theorem mustDorelease : "(alw
        (((label_eq ''feed'') or (label_eq ''pass'')) impl
        (nxt
            (ev
                ((label_eq ''feed'') or (label_eq ''pass'')) aand (nxt (not (state_eq None)))
            )
        )) impl
        (nxt (not ((label_eq ''feed'') or (label_eq ''pass'')) until (label_eq ''release'')))
     )  (watch thegraph i)"
  oops
end
