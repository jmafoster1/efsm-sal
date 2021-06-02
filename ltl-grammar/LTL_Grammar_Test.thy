theory LTL_Grammar_Test
  imports "EFSM.EFSM_LTL"

begin

hide_const T
hide_const L
hide_const E
hide_const I
hide_const R
hide_const S
hide_const V
hide_const cis

lemma X_3: "(output_eq [Some B0a__7,(None),Some K6Y,(((Some (Num 88))))] aand output_eq [Some (Str LX__50)]) (watch MsN5S V5_p_e)" oops
lemma Q_36_5: "state_eq (Some 0) (watch Et_D b4i_1)" oops
lemma S9_C: "((ev (output_eq [Some (Str P___v5x6_w), Some uD8__fi, Some i2e_064,Some h_5] impl (label_eq ''!'' aand state_eq (Some 377))) suntil label_eq g_G) until ((((output_eq [(None),Some (Num r_5), (Some x_32e_r_f), Some h_T1] impl output_eq [])) impl state_eq None) suntil label_eq ''V'')) (watch W3d q___t0)" oops
lemma fX_2: "((output_eq [None, Some (Num i_s), None, Some (Str ''7@''), Some (Str eS__T),None] or ((((((label_eq '',-'' aand (output_eq [Some D7Ne_h,(Some (Str KN7))])) until ((output_eq [None, None, Some lvs, ((None)), Some (Num 40), None, Some I_c, Some x____D] or (output_eq []))))) suntil input_eq [(Num 21)])) until label_eq S_n)) or input_eq []) (watch A1bt n3a)" oops
lemma K_R: "((output_eq [None, (((Some (Num nzGr)))),Some E__F] or ((state_eq (Some 108)) suntil output_eq [])) or output_eq [None,Some S_h,(Some (Num 2))]) (watch C__2 c42)" oops
lemma Z3D: "(output_eq [Some (Str j_GN), None, ((Some P_p)), None,Some (Num 4318),Some (Num Z_W)] impl state_eq None) (watch JA_9 ASR)" oops
lemma N_5_W77U: "output_eq [(Some Esb0)] (watch a6H uI7_II)" oops
lemma W_2: "ev (((input_eq [(((((Str ''e''))))), Num s4SnK27,(Str L_6), Num mBA,Str ''K'']) suntil ((state_eq (Some 7257) or ((((input_eq [Num 210,Str U__5] impl output_eq [None,Some UI_0_x7, None, None,Some (Num h__3_p),None]) until (state_eq (Some 48558) aand label_eq '':'')) or (input_eq [(Str WV_y),Str ''>'',Str ''x`'', Num 402, Str p__c,(((((((Num J__f)))))))] or state_eq None)))) until (label_eq u_4)))) (watch t79 S_4)" oops
lemma e_z: "output_eq [Some (Str I___F)] (watch k0X__1q v_4__7)" oops
lemma m_6_2t: "((input_eq [Str a__R1,((Str b_e)),(Str x_Q_7),(((Str Qd_0))), ((((((Num U_83))))))] aand output_eq [Some (Str '',''),None, (Some G_7_3), None,Some (Str Ea14)])) (watch w0____5tn G_34)" oops
lemma t6K: "((label_eq onT aand (input_eq [Str ''A}''])) aand (label_eq ''}3'' until (((nxt ((((((label_eq ''.95v2('') suntil (state_eq None until ev (state_eq (Some 6) suntil (ev ((label_eq N_10__69 impl output_eq [Some (Num 4), Some Q8O,None, Some lW__R,Some t2IA, Some o_Ii,((None))]) aand input_eq [((Num D_0Y)),Num B1_T,Str ''@4{{'',(((((Str ''Z_<@}''))))),(Num a7r_1), Num D__Q_d])))))) or (label_eq ''2}'' impl (((alw ((input_eq []) aand label_eq ''{'')) suntil (state_eq (Some 3) impl label_eq ''2'')))))) or label_eq ''('') aand ((((((label_eq ''X'' aand input_eq [((Str ''!Q4''))]) impl (label_eq '':9''))) aand (((input_eq []) impl (input_eq [] suntil ((((output_eq [(Some (Str ''|'')), Some (Num b_2),Some gTc, Some U_40__1, None,(Some n8A)]) aand input_eq [Str ''rl-'', (Str e__T),Num I_1J,(Str hf_2)]) or ev (label_eq ''$,!u'')) or input_eq [Str ''=L(''])))))) until label_eq ''0>'')) suntil (((state_eq (Some 81) suntil nxt (label_eq Yv_J)) suntil (output_eq [] aand output_eq [Some (Num S_3G), None, Some (Str ''='')]))))))) (watch Tw_6 x81)" oops
lemma Cs__Z: "(((state_eq None impl output_eq [None,Some I6Y_h]) impl (label_eq ''3<^'' suntil label_eq ''5''))) (watch U_13 fv5)" oops
lemma O_f: "input_eq [] (watch PK9 M28)" oops
lemma zKe: "(input_eq [Str ''5?'']) (watch O9_KT_2 dXZ_4)" oops
lemma L__0: "nxt (output_eq [None, ((Some LD6)),None] aand ((input_eq []) impl input_eq [])) (watch ok9 K_a)" oops
lemma d_R9: "(label_eq D_HS) (watch a_9 x_3_p_1)" oops
lemma N__96_7k: "(state_eq None impl (((input_eq [Str M50]) or (((output_eq []) until alw (input_eq [] until (nxt ((((state_eq (Some 78)) impl nxt (((input_eq [Num a70,(((Num 46)))]) or (input_eq [] impl output_eq [Some OQ4,None,((Some (Str ''p-'')))])))) until (not (((output_eq [] suntil input_eq []) aand (input_eq [Num 3] aand (output_eq [])))) or (output_eq [] or state_eq None)))) until state_eq None))) until output_eq [((None))])))) (watch S19 q_p)" oops
lemma e70: "(not ((nxt (output_eq [] impl ((((state_eq (Some 1)) aand (input_eq [] until label_eq ''X''))) suntil state_eq (Some 7))) or label_eq l_534_n) impl input_eq []) or state_eq (Some 8)) (watch d9r F_7)" oops
lemma T01: "(((output_eq [] aand state_eq None) suntil state_eq (Some 3)) or label_eq ''=I*09'') (watch x_bY__7 z2___390)" oops
lemma cK6: "(state_eq None or state_eq (Some 3)) (watch g_o M__2)" oops
lemma lv_LZ: "((((((state_eq (Some 5) impl (state_eq (Some 9) or (input_eq [Num 6946, (Num 3)] suntil output_eq []))) or ((((((((state_eq (Some 6) suntil state_eq None) impl output_eq [(Some (Str Q_17))]) impl ((input_eq []) aand state_eq None))) impl state_eq None) until (state_eq (Some 570)))) suntil state_eq None))) aand ((((state_eq (Some 37) or ((((label_eq ''8'' until ((((output_eq [None,Some tAMj]) impl state_eq None) or (state_eq (Some 99) aand input_eq [(Num 555386)])))) suntil output_eq []) suntil ((state_eq (Some 7) suntil (state_eq (Some 5) until output_eq [])) suntil (state_eq (Some 38)))))) until (output_eq []))) or input_eq []))) impl label_eq q_7) (watch uz_59 KuI)" oops
lemma H______5: "(state_eq None) (watch GCG hw__K)" oops
lemma W_P: "(output_eq [] impl input_eq [(Num 3)]) (watch dqP w8Q)" oops
lemma n0I__0: "(((state_eq (Some 2) or (output_eq [] suntil (((state_eq (Some 61860) suntil label_eq m___EA1) until (output_eq [Some e30] suntil ((state_eq (Some 13) aand (((label_eq Q9_m7 impl output_eq [None]) suntil (input_eq [] impl output_eq [])))) suntil (state_eq (Some 83) or (((input_eq [((Num 63))]) impl (((((((output_eq [] impl (input_eq [] until state_eq (Some 2))) impl (input_eq [(Num y_0Iwi),(Num u_y)] suntil input_eq [])) until (state_eq None suntil label_eq B___2))) suntil ((output_eq [] aand (output_eq [] until (state_eq (Some 01) aand label_eq ''!h3^#+'')))))) until input_eq [(Num G_1),Str X4w_4o, (((Num 3))),(Num U__2)])))))))))) or ((((((state_eq None impl (((output_eq [None] or output_eq [(None)]) until (output_eq [] impl (state_eq (Some 8) until state_eq None))))) aand label_eq ''!'') aand not (output_eq [Some (Str gHF),Some (Str u8i)] aand state_eq None)) impl (output_eq [] or (label_eq p__0 suntil output_eq [])))) until ((state_eq None suntil label_eq ''%3'') until output_eq [(Some (Str R4pz)), Some f_1,None,None,None])))) (watch o__06 Op0)" oops
lemma m3B: "output_eq [] (watch QsI b13)" oops
lemma w_mc0___9: "(((label_eq ''^d&'') or (label_eq d_6_4 suntil ((((output_eq [Some (Str ''#}V''), None,(Some (Str ''9'')), Some l38,None, None,None,Some (Num i_88)]) impl (((((output_eq [] until ((label_eq ''62'' suntil alw ((label_eq y_1) until output_eq [Some y__5])) aand state_eq None)) or input_eq []) impl ((((((output_eq [Some (Str ''01>'')] impl (label_eq ''g-m,*}y9'')) until (state_eq (Some 15) aand (output_eq [Some (Str FTo),Some (Num 2), Some (Num 77)] until (state_eq None)))))) or (state_eq None aand ((output_eq [] or state_eq None) suntil state_eq None)))))) or (input_eq [] or output_eq [])))) suntil state_eq None)))) (watch PR678 J_I)" oops
lemma BE__y: "(label_eq J5__jS aand (output_eq [Some NyP0, Some L7y,(None)])) (watch qL0 Q_0)" oops
lemma N_F1: "(((state_eq None aand (label_eq f_YA)) impl (((state_eq None suntil output_eq []) impl (input_eq []))))) (watch a__Z M5d)" oops
lemma NE5: "(state_eq (Some 4) aand label_eq e3Nq) (watch K__c AL0)" oops
lemma W_V_v: "(label_eq gq475) (watch K5_mo b_6)" oops
lemma n4_s: "(ev (alw (output_eq [] aand (input_eq [(Str cx_4x),(((((Str s___R2Q))))),Str ''>*'',(Str ''('')] or (input_eq [(Str Vw067), Num 81, Str ''#'', (((((Str f_A))))),Num i_h2, Num ifm, Str d__5]))))) (watch j__o j__Z)" oops
lemma R_T: "label_eq VLq (watch h_7 w__7x)" oops
lemma K_5: "input_eq [(Str ''xA<7.7,''),(Str o_c)] (watch A_Q P0N)" oops
lemma z_9: "(label_eq yX_E aand (state_eq (Some 22018) aand (label_eq ''0'' suntil input_eq []))) (watch f_A___3 b_x)" oops
lemma i_6: "(((label_eq ''1'') impl state_eq (Some 3)) or ((label_eq n8o) or (((output_eq [] until ((state_eq None) aand (label_eq ''_>''))) suntil ((label_eq ''&8'') or ((label_eq M_V until (((label_eq S_0) until (label_eq B_j)))) suntil state_eq None)))))) (watch N2I TD5_60_i)" oops
lemma Cv3_3: "output_eq [Some (Num x5d),Some Jri_P] (watch xck clk7__8_g)" oops
lemma q_8_N: "(((state_eq (Some 5) impl state_eq (Some 1)) suntil input_eq [(((Num 5))), (((Str ''!('')))]) suntil state_eq None) (watch A_C14 jS_5)" oops
lemma R_4: "(((((output_eq [] suntil input_eq []) impl ((input_eq [] impl (output_eq [] or output_eq [])) suntil (((state_eq None) until (label_eq ''A'' suntil ((state_eq None suntil ((output_eq [] until (input_eq [])) or ((((((state_eq None or ((not (state_eq (Some 3))) until state_eq (Some 0))) suntil (input_eq [((Num k6_____3)), ((Num h___0)),Str ''7'', Num l_j,(Num 9),Str ''`''] aand ((((label_eq l_K impl label_eq ''`>0z'') until output_eq []) aand (state_eq (Some 3012) or ((output_eq [] impl ((((((state_eq (Some 383) until output_eq [Some H_6, None, (None)]) suntil (alw (((input_eq [] impl (state_eq (Some 006079))) until input_eq [(Num 27)]) impl output_eq []) aand input_eq [(Num S_50), (Num 6)]))) or not (output_eq [Some (Num 4)] or state_eq None)) suntil (label_eq jo_4 or input_eq [Num a5H,(Str c_x)])))) suntil label_eq Z6_Y))))))) suntil input_eq [((((Str h7_A)))),(Str ifR)]) suntil input_eq [])))) until label_eq L_p))))))) aand (state_eq (Some 656287763) aand (input_eq [])))) (watch T_v a_CK)" oops
lemma m_E: "input_eq [(Num 329), Num T_7,Num i_0] (watch v_1 n_7_l)" oops
lemma t_n: "(((state_eq None) or (((state_eq (Some 279) suntil (((state_eq None) or (alw (((input_eq []) aand (input_eq [] suntil input_eq []))))))) until ((state_eq None impl state_eq (Some 2)) until label_eq ''k''))))) (watch j_2 x__y)" oops
lemma D_4: "label_eq f_6 (watch I5_4__3 a_P)" oops
lemma p_b: "(not (((input_eq [Num v_a] suntil (input_eq [] aand output_eq [None,(Some (Str f__2)), Some (Num 43)])) suntil (state_eq None)))) (watch Ld_8 Z_n7)" oops
lemma A14: "input_eq [(((Str Q_1))), Num 404, Str o70,(Num J__7), Num 5,(Str ''4''),Str ''l'',(((((Num 487)))))] (watch x_U Wy8)" oops
lemma U_1: "(((((((output_eq [] until (output_eq [Some (Str Mz7), (Some (Str a_l)), Some (Str ''^v&''), Some (Str T_6),Some u__5,Some (Str ''h'')] or (output_eq []))) aand input_eq []) aand (label_eq ''&<'')))) impl (input_eq [Str D_6, (Num X0_83)] until input_eq []))) (watch I_i q_D)" oops
lemma a3_28: "(input_eq [] aand (label_eq ''^'')) (watch tp___J P6391)" oops
lemma F9X: "output_eq [Some (Num w_n1), (None)] (watch A_zE A_s)" oops
lemma k_5: "(((((not (input_eq [] or (((label_eq N21l until ((input_eq [] or (state_eq None)) suntil output_eq [])) aand (input_eq [(((((((Num 00))))))),(Str ''z1S''),Num M___S,((Str B7f)),Num 027835, (((((Str MHg)))))])))) until (output_eq [] suntil state_eq (Some 3))) suntil output_eq [((None)),None,(None), Some P_4, (None), Some (Num v_HM),(Some (Num 0)), (None),Some l8H]) impl (label_eq h9_5 impl ((output_eq [Some (Str ''Xw5''),(Some s97)] aand (input_eq [])) suntil input_eq [Str E94])))) aand state_eq None) (watch l_9Y7 KMCZ)" oops
lemma j5R: "((((input_eq [(Str I__2)])) suntil (((output_eq [] impl label_eq '';r'') suntil (state_eq (Some 1) until (label_eq ''F_'' until (((state_eq (Some 017)) aand ((((output_eq [None,Some GjV,Some (Str ''--L,'')] suntil (state_eq None)) aand state_eq (Some 93)) until ((((state_eq None impl label_eq ''5<,.0`A?'') suntil ((output_eq [(Some R_9), ((Some Y_1)),None, (Some (Str ''B''))] until (input_eq [] until (label_eq '' ''))) aand (((state_eq None until state_eq (Some 27)) impl (output_eq [Some (Num 02)])))))) until label_eq '':iu''))))))))))) (watch x_t BW7_8)" oops
lemma fTZ1: "output_eq [] (watch o_1Hp q6_13z)" oops
lemma I99u0: "(((output_eq [] suntil state_eq (Some 189)) or (input_eq [(((Str l9V_6j6)))]))) (watch c_5 e93_62)" oops
lemma Y2C: "input_eq [] (watch t_9 uK1)" oops
lemma sLC: "state_eq None (watch P2_f I_x)" oops
lemma w_8: "((input_eq []) or state_eq None) (watch T2l x_6)" oops
lemma z20: "state_eq (Some 87) (watch E_s C_d__o9__wZ)" oops
lemma TKZ: "(input_eq [] suntil input_eq [Num A_C, Str M27]) (watch Y_w X_41M)" oops
lemma U_6: "(input_eq [((Num rN6))] aand state_eq None) (watch h_Za j__78)" oops
lemma t_Mh: "(label_eq y___8 aand output_eq []) (watch l_3 X08)" oops
lemma lo5: "ev ((output_eq [] or ((label_eq V_b until ((((label_eq nr6y suntil input_eq []) or not (input_eq [] suntil label_eq ''/'')) until (output_eq [Some F_a___7,Some (Str p_L4)] aand state_eq (Some 9))))) suntil state_eq None)) or output_eq []) (watch GBw c9_3)" oops
lemma F_6: "input_eq [Num 8] (watch E_h i_Z_3)" oops
lemma NL_10: "((((output_eq [None, Some F5__q]) suntil (label_eq ''$f'' aand label_eq ''2;''))) or input_eq [((((Str ''7/''))))]) (watch D__M l_06H4)" oops
lemma K_9_6n4: "(output_eq []) (watch zT1_T s1e)" oops
lemma P_6: "input_eq [((Str k_2)),Str ''7hn'', (Str j2_G), Str Oz1] (watch Nt7 S_f)" oops
lemma DQ0_15: "(label_eq F__5 impl output_eq []) (watch p__9 PJ7)" oops
lemma o6g: "state_eq None (watch M_A j_e)" oops
lemma W81: "state_eq None (watch wf_F ClJ_h)" oops
lemma r2_S: "state_eq None (watch R89 e_0)" oops
lemma o1_8: "(output_eq []) (watch g82_X q_E1)" oops
lemma k___G: "((label_eq ''X'' until not (state_eq None until not ((output_eq [] suntil nxt (state_eq None)) or label_eq xev0))) impl state_eq (Some 2)) (watch b27 rX_7)" oops
lemma G_3A: "output_eq [] (watch U_5 V__9v)" oops
lemma p_a: "(state_eq None until input_eq []) (watch h_4 Q30)" oops
lemma Z4h: "((output_eq []) or label_eq RTV) (watch Y180 S04)" oops
lemma laj4: "state_eq None (watch L_1T__T o__d)" oops
lemma k_25: "(state_eq (Some 608) impl (state_eq (Some 575))) (watch C_pv O_8)" oops
lemma m_VN: "((label_eq ''Eu3'' until output_eq [Some (Num sv1)]) or input_eq [(Str ''17''),(Num Q__0),Num z22,Num Z6Q__2_90,Str ''|'',Str ''Z@'', Num 18, Num r__E]) (watch Q_15O Z_4)" oops
lemma E_6h_8: "(input_eq [(Num 5031),(Str ''/''), Str ''$''] until (output_eq [((Some (Str ''%''))), Some (Num M9v),Some (Str w__8),Some (Num 2), Some (Str TqO), Some (Num F_1),None] or (output_eq [] suntil output_eq []))) (watch C0h6 U8__05w3)" oops
lemma nk0: "((label_eq ''>'') impl state_eq None) (watch FCt72 v__2)" oops
lemma F9__8: "(input_eq []) (watch qy8 a3_5)" oops
lemma zHC: "((((input_eq [Num 896, Str d_F88271r]) until output_eq [Some z3_y,(((Some (Num A_6_3___6__5))))]) suntil alw (input_eq [])) impl label_eq m__6_g) (watch Y_V Fy_6)" oops
lemma E07_P: "output_eq [Some (Str n_5),(None)] (watch xocv o_2)" oops
lemma hy_k_K: "output_eq [Some (Num 43432), None] (watch q8O E6_85483)" oops
lemma f_sp0: "((label_eq '':0'') or output_eq []) (watch y0V p4_O)" oops
lemma Qyn: "output_eq [None] (watch Z_s_uO qU_0)" oops
lemma l_u: "(output_eq []) (watch f9S T___J)" oops
lemma d_G: "(((input_eq []) suntil (input_eq [Num Pi_X___8,((((((((((((Str '':<m''))))))))))))] suntil input_eq [((Str ''Z''))]))) (watch Q_0 js6J)" oops
lemma R5___S: "nxt (label_eq ''*'' impl (output_eq [])) (watch kq__0_3 F__9)" oops
lemma eL_V0: "state_eq (Some 13) (watch B_H Z__3)" oops
lemma U_4: "input_eq [] (watch e_8 w_w35)" oops
lemma z__5: "output_eq [] (watch k9A s65)" oops
lemma FL0: "(((output_eq [None]) suntil state_eq None) suntil alw ((input_eq [(Str S_Dp), (Num 6031),(Num 86)] suntil (((input_eq [] until (output_eq [Some (Num 5),(None),Some y_4,None,Some h_9] until output_eq [Some (Str ''1'')])) suntil (output_eq [((Some f9u)),(((Some (Num 31)))), ((None))] or label_eq Gpz)))) suntil state_eq (Some 3))) (watch u_I3 G__83z)" oops
lemma t_K: "(input_eq [] suntil (((((((((input_eq [] until label_eq ''b;D'') impl (input_eq [Num I5740,Num U_a,(Str IH_v)] aand state_eq (Some 2)))) until input_eq [(Num A0E),(Str ''H7+''),(Num 934),Str '' {f'',Str ''TzR'', Str ''}'',(Str ''7/wA'')]) impl (output_eq [Some (Num 1), Some (Str H_D__0)] suntil (output_eq [] suntil output_eq [Some h__6561V,None, None, None,None,Some R_Ap_4]))) impl (((((state_eq None suntil label_eq ''=?'') impl output_eq []) or input_eq []) aand (((output_eq [] suntil input_eq [(Num 49), (Str ''a'')]) or (label_eq ''.S>N4''))))))) until (((input_eq [Str ''.U'',(Str ''~=S''), Str ''~t''] or (state_eq None until ((((state_eq (Some 920)) suntil (output_eq [] until label_eq S_t_k)) aand (label_eq Xl_8 aand (((((state_eq None or input_eq []) suntil (state_eq None impl (label_eq n_2)))) impl (state_eq None impl (((((((((state_eq (Some 1) or input_eq [(Str L__N),(((((Str f__4)))))])) suntil (input_eq [Str k30,Num 9] until (((((state_eq None) or (output_eq [] until ((((((input_eq [] or state_eq (Some 7688)) suntil label_eq Ndt) impl (state_eq None))) until ((state_eq (Some 9) suntil (((((input_eq [] until (input_eq [((((((Str X_5D))))))] impl ((output_eq [] impl (output_eq [] suntil output_eq [])) aand label_eq F_q))) impl (label_eq j__M))) impl ((input_eq [((Num 770)),Str ''M'']) aand input_eq [])))))))))) suntil ((state_eq (Some 832) aand not (label_eq ''3t'')) until label_eq X_q)))))) until (label_eq ''5}4@6&'')) aand (state_eq (Some 326) impl input_eq [(Str '',>X@''),Num 18, (Str EtC)]))) aand ((label_eq ''4<'' impl (label_eq lN_84____7 or (((input_eq [(Str B4_6)] until (input_eq [] until state_eq (Some 260916))) suntil state_eq (Some 4))))) or input_eq [Num x1jM, ((Str cZ_6)),Str ''%'', Str ''F'',(Num K__Q)]))))))))))) suntil label_eq k__8) aand state_eq (Some 7))))) (watch I8U W_2)" oops
lemma TN1O3g: "output_eq [] (watch IM_85K0 f1j)" oops
lemma T__4: "(((((state_eq (Some 5) impl ((label_eq ''},e_9'' or (label_eq uL6 until label_eq ''8'')) impl input_eq [(((Num 8))), Str ''&''])) impl (label_eq Y_0))) until (label_eq ''E'' suntil (((state_eq (Some 4) or state_eq (Some 8)) or ((label_eq a9J until (output_eq [Some whO,Some (Str ''m''), (Some U_p), (Some (Num 80934))])) until label_eq s_1)))))) (watch u9h0X Gi2)" oops
lemma iv_6: "state_eq None (watch r___6 h_P)" oops
lemma u_6: "((state_eq (Some 930275) aand (state_eq (Some 892) or (state_eq None suntil output_eq [None]))) or state_eq None) (watch oP2i4_6V S8p8_t)" oops
lemma N_1: "label_eq ''>'' (watch Y__9 gQ_l8)" oops
lemma b__78C0: "ev (nxt ((input_eq [((Num P__3)), (Num 87280),((Str ''J.mi'')),Str c2_q] or (nxt (state_eq (Some 4)) aand (nxt (((state_eq (Some 4) until label_eq ''g'') aand output_eq [Some (Num i_0_Z),None]) or output_eq [None,None, None,Some (Num 6)]) impl input_eq []))) or output_eq [((Some (Str ''M''))),Some (Num 4),(((Some Da_0p))), None, None])) (watch A_89 O84_6)" oops
lemma L__1: "nxt ((state_eq (Some 26) suntil output_eq [None,None,(Some (Num 84)), (None),Some (Str ''n*}0 '')]) until output_eq []) (watch w__y P_C)" oops
lemma O___P_8: "output_eq [Some y2_3,Some (Str '':d_.>'')] (watch b_2 e3r)" oops
lemma zh_2: "(input_eq [(((((((((((Num 3))))))))))), Str ''1:'',(Num 628), (((Str U__s)))] suntil ((output_eq []))) (watch G00 X6i)" oops
lemma IP5: "(state_eq None) (watch w__9_f rXt)" oops
lemma M_m: "((label_eq DaD or ((input_eq [Num I78, (Str a27), Str ''%'',(((Num A04Z))),((((Num 5))))] suntil (input_eq [(Num NR_OK)] until (((input_eq []) aand (label_eq ''1'' until (label_eq ''S'')))))) suntil state_eq (Some 3))) until input_eq [(Str ''^''), (Num oI_0)]) (watch b___o3 x_C)" oops
lemma v4_m: "input_eq [] (watch P_P o00)" oops
lemma ad2x: "output_eq [] (watch Di_6 K_0)" oops
lemma xq8: "label_eq ''#'' (watch B_0 D6__E)" oops
lemma f_L: "output_eq [] (watch C06 X_f)" oops
lemma o_6: "input_eq [] (watch F8_3 J72)" oops
lemma f4n: "alw (input_eq [] until (((state_eq (Some 76)) suntil (output_eq [None])) or input_eq [(((Str ''r'')))])) (watch PbD x_e)" oops
lemma J_3: "(label_eq ''q>'' suntil label_eq ''5'') (watch y_9 K___V)" oops
lemma Sd_C: "((((output_eq [Some (Str ''l''), None, None,(((None))), Some (Str ''9x ''),Some R_t__39]) or state_eq None) impl (label_eq '':'' aand state_eq None))) (watch p__3 uC3)" oops
lemma a_38S: "(output_eq [] aand (nxt (input_eq [(Str ''7g$_Z''), (((Num q_7)))]) aand input_eq [(Str ''{S''),Str ''</`'',(Str ''b''),(Str E_1), (Num 5), ((((Str AA1))))])) (watch V_k j_6)" oops
lemma DN0: "(((((((ev ((((((((input_eq [Str J_V, ((((Str Sz6J_1)))),(Num qe___h_N),Str ''6lK#%3'',Num 01, Str Y_B] or (input_eq [] suntil (input_eq []))) suntil not ((label_eq ''.)v'' impl input_eq []) until label_eq ''+''))) or label_eq ''1'') or state_eq None) aand output_eq []) impl (label_eq r96 until (label_eq ''7''))))) aand input_eq []) impl (((input_eq [] suntil ((label_eq A_p impl state_eq None) or label_eq ''>'')) or (((state_eq None or (output_eq [] suntil input_eq [Str '',''])) impl (label_eq A9___K or state_eq None)))))))) or (output_eq [Some o_6] suntil state_eq None))) (watch m__rJ ql6_x)" oops
lemma t51A: "(input_eq []) (watch C_C mx__31)" oops
lemma e__4: "(output_eq [((Some (Num 28))),Some Sqr]) (watch J0_9VfW P_H6)" oops
lemma J__HV: "(((state_eq None impl output_eq []) or label_eq ''*'') impl label_eq vUn) (watch kP3 E__Q)" oops
lemma EJ8_2: "(state_eq (Some 65)) (watch aC_H QUR)" oops
lemma Jp0: "(output_eq []) (watch g_1 p7Q__O)" oops
lemma D747: "input_eq [Num 65875] (watch Y__2 Q_0)" oops
lemma I__TW: "state_eq None (watch J_x4_0 E27)" oops
lemma a_D: "input_eq [] (watch D__91 f87)" oops
lemma G_0: "(output_eq [Some (Str ''?Dj''), (((None)))] or ((input_eq []) until (state_eq (Some 3) suntil output_eq [Some (Num L_X8),Some (Str ''1-'')]))) (watch n__9v i_04x_c)" oops
lemma m39: "(input_eq [Str ''M_'',Str ''=3,7@''] aand state_eq (Some 5)) (watch mGh I__612)" oops
lemma N___O: "label_eq d_u_G__n_Uo (watch J_____Q g4N)" oops
lemma o_55: "(((label_eq K7T impl output_eq []) impl (output_eq [Some NO_8] aand input_eq []))) (watch f_f V_h)" oops
lemma Auy_52: "(input_eq [Str NB4,Str ''Zo)'', Num 134331,Str k_XD3_8] suntil (output_eq [])) (watch A__9 Q1O)" oops
lemma i_3I: "(((output_eq []) suntil (state_eq None or ((((((output_eq []) until label_eq me2e)) impl label_eq b13M) aand (label_eq pq1 suntil output_eq [])))))) (watch joa m_F)" oops
lemma H77: "input_eq [] (watch G_Ogh h6v7)" oops
lemma b_q: "(input_eq [] impl label_eq a_64) (watch b2D t_8_6)" oops
lemma c_7: "(((output_eq [Some xJT,None, Some o_x, (((None)))] or input_eq [(Str ''-''), Str ''s_''])) until state_eq None) (watch VD0 X_u_l)" oops
lemma O__J: "state_eq None (watch r_Q h2_j_PB4)" oops
lemma N_fI_E: "(label_eq R_Z impl label_eq '','') (watch k_p a_I)" oops
lemma m_7: "input_eq [((Str st_u))] (watch P__S Fg_7)" oops
lemma s_8s: "state_eq None (watch a2_v8v Ib9)" oops
lemma R_I: "(input_eq [Num 17769,(Str ''!;E''), (((((((((Num 6))))))))),(Str ''5'')] or ((label_eq ''j'') impl label_eq e_pd)) (watch u_47 l_1)" oops
lemma c_3: "(((((label_eq ''I4'') or (nxt (state_eq (Some 94)) aand label_eq u__M))) aand (((nxt (state_eq None) impl (state_eq (Some 7) impl (input_eq [] until (output_eq [Some DG3,Some (Str ygH9), Some k_F] or (alw (output_eq []) impl (((input_eq [(((Num 543950))), (Num 059)])) or input_eq [])))))) or (state_eq (Some 058) or output_eq []))))) (watch X_SB9 X_Z)" oops
lemma B0_0: "input_eq [] (watch Jw92C0 a_j)" oops
lemma Qpw: "(state_eq None impl (label_eq ''Gq'' or ((state_eq None aand (output_eq [(Some R___E),(None), Some Z_g, None,(Some m19),(None),(Some (Num 1)), Some K_L])) until not (state_eq (Some 81) impl state_eq None)))) (watch q5_Y Si_9)" oops
lemma c9s9: "(state_eq None or ((state_eq (Some 982) or ((label_eq PG_w suntil label_eq ''6'') suntil (output_eq [] until state_eq None))) aand nxt (input_eq [(((((Num c_n)))))] aand ((((output_eq [] until (state_eq (Some 3))) or state_eq (Some 191)) until (output_eq [(((None))), Some B_l, (Some by5o), Some (Num D__8_q),Some l_w, Some Pa_a_4] impl (input_eq [Str e_0] impl (((label_eq ''+&$'') aand ((output_eq [Some TbF,None,None]) suntil input_eq [Str On_5y,Str G_6K9])))))))))) (watch S362 v_c)" oops
lemma LOH3: "state_eq None (watch k7___2 vj6)" oops
lemma c_z: "(state_eq (Some 22) until label_eq dD8V2) (watch gy__v P_Z6)" oops
lemma L__5: "output_eq [] (watch J__k p_8)" oops
lemma W__a: "(input_eq [] or (((((output_eq [Some (Num 012537),Some (Num mkw)]) until alw ((((state_eq (Some 4) or (label_eq H_S suntil state_eq None)) or input_eq [(((((Num p96))))),((Str H____J))]) aand output_eq []) or output_eq [None])) impl state_eq None) until (state_eq (Some 8) or (state_eq None impl (((label_eq z__F1 until (((label_eq '';u{'' or output_eq []) aand (output_eq [] suntil (((((label_eq ''m'') aand ((state_eq (Some 05)) suntil state_eq None)) until label_eq ''G;/6'') until (state_eq (Some 22) until (input_eq [Num 5, Str RZn, Str g_Tli] impl (output_eq []))))))))) until (input_eq [Str b___D] until input_eq [])))))))) (watch h__I sig)" oops
lemma m__4: "(label_eq ''9'' or ((output_eq [] impl state_eq None) suntil (((output_eq [Some (Str t3R), Some (Str Xep), Some (Num y2_m),None,((Some x2v)), (Some V9m_1), Some (Str ''~,'')] aand (alw (state_eq None aand input_eq []))) until (state_eq (Some 5)))))) (watch T4e u____b)" oops
lemma nEu: "(state_eq None) (watch oWE WW_X)" oops
lemma A55: "(((label_eq ''Y:'' impl output_eq [Some y_9, Some Hh1,None,Some (Num 82)]) until (input_eq [(Num q_0)] or (output_eq [None])))) (watch Lib7 XWD)" oops
lemma m5_i39: "ev (state_eq None aand (((output_eq [None] or state_eq None) until ((((((input_eq [(Num 1)] until ((state_eq None or (input_eq [] suntil label_eq a2TV)) until output_eq [])) aand state_eq (Some 4)) until (label_eq ML_8))) impl (output_eq [] or label_eq ''tO:'')))))) (watch w_N r__7)" oops
lemma b_L___EE6: "(state_eq None) (watch E_o D_b)" oops
lemma FCC: "label_eq ''~'' (watch Z8E qsx____4_2)" oops
lemma d_9: "((state_eq None or (output_eq [])) impl output_eq [((((None))))]) (watch TF_89_U t_6_r42)" oops
lemma s_1: "((((state_eq None suntil label_eq P__y) until output_eq []) impl label_eq ''6'')) (watch R_2E C_155D0B)" oops
lemma a__1_D: "((state_eq None) suntil label_eq W1N) (watch O__6 q_s)" oops
lemma XqZ: "label_eq G__a (watch XJ1 o_y_o)" oops
lemma ih1u: "(((((label_eq XT_e)) suntil input_eq [(Num r7_4)]) aand (label_eq ''<`$7>'' aand label_eq ''%''))) (watch u5QyH A__Q)" oops
lemma A4I: "(input_eq [] suntil output_eq []) (watch U20U V_Q)" oops
lemma B2p: "((label_eq p44 suntil label_eq kMu) suntil ev (output_eq [(Some (Str s_U_9)),(None),Some KCHY5] aand output_eq [])) (watch Rn2_06 d225)" oops
lemma i_Ws: "state_eq None (watch z42 C__9)" oops
lemma i4_2: "(((output_eq []) or ((input_eq [])))) (watch s_9 p0I)" oops
lemma c50: "(((output_eq [] until (alw ((input_eq [] aand (label_eq ''H)''))) until (((input_eq [] until (output_eq [Some m_z, (Some (Num zbR)), Some (Str '')'')])) aand (label_eq Y9h aand output_eq []))))) aand (((((((input_eq [] or ((ev (alw (state_eq (Some 35) until (output_eq [])) until input_eq [])) aand output_eq [Some q_A, Some (Str S_Q)])) aand (((state_eq (Some 859)) until (alw (output_eq []))))) until output_eq [Some (Str qa4),(None), Some JF_S]) suntil output_eq [Some h4g]) until (input_eq [Num r_2] impl input_eq [Str ''('',(Str a__6), Str '';'',((Str ''YM'')),(Num 4),Str ''2'']))) until input_eq []))) (watch I_O7 IYE)" oops
lemma Yu6: "(alw (((output_eq [None]) until (((((output_eq []) aand (input_eq [(Str ''m4/''), Num 086] or (((output_eq []) suntil ((((output_eq [] or state_eq (Some 649)) until (label_eq ''5'' or (input_eq [] impl state_eq (Some 6))))) impl state_eq (Some 2510))))))) until (state_eq (Some 5))))))) (watch F_B Z_t)" oops
lemma t8Jd_k: "state_eq None (watch Vc6 R_it8)" oops
lemma f_b: "((state_eq (Some 6) suntil state_eq None) impl output_eq [(Some r_8), None, Some o_o]) (watch A2y g_2)" oops
lemma i9B: "(((((((state_eq None) until input_eq []) suntil input_eq [Num 0, (Num 9), Num Riw, Num 2]) aand output_eq []) suntil state_eq (Some 3)) or (output_eq [Some H3LK,(None), Some p_6,Some poLah8] suntil state_eq (Some 0)))) (watch s4s l_9)" oops
lemma j97: "(state_eq (Some 5)) (watch nD4 g1N)" oops
lemma y_5: "label_eq ''1'' (watch Vh_h W__1)" oops
lemma Uk1: "(((label_eq ''@4r'' impl ((label_eq G_8 until input_eq []) aand label_eq ''-7'')) aand (output_eq []))) (watch i3x v56)" oops
lemma e__t: "label_eq V7_7 (watch Q__3 X_H)" oops
lemma S_hHI: "(input_eq [((Str ''1''))]) (watch W3h U__8)" oops
lemma q_I: "state_eq (Some 1) (watch A_4 f_0)" oops
lemma q_3: "(label_eq cq_F aand (output_eq [Some R_6, None])) (watch i_E G7__0)" oops
lemma Jy6: "((((state_eq None impl ev (input_eq [Num 8, Str ''-}0'',Str nAV, Str ''~'', Str J0_6_g,Num 1, Num a_0, Num I04] until output_eq [])) until (state_eq None))) aand nxt (state_eq None aand (output_eq [None] or (label_eq X86)))) (watch i__5 qJ_yW)" oops
lemma f98: "input_eq [(Num q69), (Num r6_1__8)] (watch e_3 m97)" oops
lemma FFB: "(input_eq [] or (((((((label_eq xUQ) or label_eq IT0) until (state_eq None impl input_eq []))) suntil (nxt (output_eq [None,Some (Num Q_4___S_0), (None), Some S84_g, Some (Num J_N), None, Some a42, Some (Num f_2)] suntil (state_eq None impl (ev ((((label_eq ''_'' impl not (state_eq (Some 09174))) until ((output_eq [Some K3m]) until output_eq []))) impl input_eq []) until (output_eq [] impl (((label_eq M_2) until (((input_eq [] until input_eq []) suntil (state_eq None)))))))))))) impl label_eq Q26)) (watch H__j_9 D6z)" oops
lemma P___1: "label_eq ''{G'' (watch Y_o6_K m_2f)" oops
lemma GrP4E: "label_eq ''/*~'' (watch R_0 b_e)" oops
lemma M65: "(state_eq None impl not (state_eq None)) (watch d_63 Vet)" oops
lemma q1___L: "label_eq ''9'' (watch XpL H_c)" oops
lemma K_V: "input_eq [Str ''8''] (watch OVz TR_86)" oops
lemma p_lhJ: "input_eq [] (watch l_F C4W_e4)" oops
lemma E_gi7: "((alw (state_eq (Some 087) impl (input_eq [((Num 9)),((((Str ''-'')))), (((((Str ''6F$'')))))] impl (label_eq uw1 or output_eq [])))) suntil input_eq [(Str anr2)]) (watch w_5 L54)" oops
lemma gGTl: "input_eq [Num R93] (watch l_Ck l____7)" oops
lemma D_F: "input_eq [] (watch P6D_3 M__s_R)" oops
lemma s07: "((state_eq None) suntil output_eq [Some (Num 76)]) (watch R_5 t_4)" oops
lemma ue8: "label_eq ''?5'' (watch i__1 DNY)" oops
lemma F_Io5: "(input_eq []) (watch Ef_1fUW Kz__9)" oops
lemma v_q: "((state_eq None suntil state_eq None) or output_eq []) (watch YR3 zj4)" oops
lemma b5_9A5: "nxt (label_eq ''|'' impl ((((label_eq ''8)'') aand (label_eq ''Q'' until input_eq [((Num 4)),(((((Num 2)))))]))) or output_eq [Some (Num 90),(Some e_z61)])) (watch F_3 i_32)" oops
lemma BW4w8: "(output_eq [Some t__4] until state_eq None) (watch h6_8 M_2B)" oops
lemma N_6: "((label_eq ''/'') impl input_eq [(Num 559),(Num j5742), (Num m_1),Str ''5'',(Str ''V)OaY3''),((Num 4)), Str ''9H r@'', Str J_N]) (watch RE4 Os_y)" oops
lemma A_5: "(((label_eq A037 until (state_eq None or (output_eq [] suntil input_eq []))) impl (((output_eq [Some (Str ''3''),None]) until (input_eq [] until (state_eq None until (ev ((output_eq [(Some X_8)] impl (((ev (((input_eq []) until ((nxt (output_eq [] or label_eq LCRJ))))) or label_eq ''0'') impl (((((((((input_eq [((Str ''`'')),Str ''$''] until (output_eq [])) impl (((((label_eq ''3'' or (input_eq [Num 32146, ((Num 566))] until state_eq None)) aand (input_eq [] or output_eq [Some (Str ''x)'')]))) impl (((((((label_eq z1_7_____t_3 suntil (input_eq [])) suntil (output_eq [] until state_eq None))) aand (output_eq [(Some (Num o_f))] until state_eq None))) or output_eq []) suntil state_eq None))))) suntil output_eq []) impl (((state_eq (Some 5) until (state_eq None or ((label_eq ''02'' or (((label_eq g_2) or state_eq None) suntil (((input_eq [(Num Q_5), ((((Str ''y4='')))), Str ''~3&'',((((Num OV6K)))),Str ''0'']) until (output_eq [] impl ((label_eq cUC) suntil state_eq None)))))) aand (output_eq [None])))) suntil ((input_eq [] impl (alw ((input_eq [] aand output_eq []) aand input_eq [Str ''+'']) impl ev (((((((input_eq [] suntil (label_eq w_D until ((label_eq '' ,'') suntil label_eq ''0.9''))) aand (output_eq [] suntil state_eq None))) impl ((((input_eq [(Num 8)] suntil ((((label_eq ''66<'' aand ((((((label_eq '',-'' or output_eq []) suntil (output_eq [] or (alw (((label_eq ''('' impl output_eq [Some (Str B__G),Some (Str o_2),Some (Num q_1n), (Some I_E)]) or state_eq None) or input_eq []) until input_eq [])))) or state_eq (Some 23)) until (output_eq [])))) or (output_eq [Some (Str ''i7''), (((None))), None, Some ZW_d47,(Some o2____L), (Some (Str ''J4x'')), None, Some (Str lQ_3), Some (Num W9W)] impl label_eq J0__04))))) impl state_eq (Some 9)) or (((input_eq [] suntil (state_eq (Some 61))) aand (label_eq s___6 until input_eq []))))))) until ((state_eq None suntil label_eq '';.'') suntil state_eq (Some 2)))))) impl state_eq None))))) or input_eq [(Str S_0),Str q_N]) impl (label_eq e1_DY)))))) or label_eq Sc7)))))))) (watch Bk_1x1_2 vp_3)" oops
lemma gb3: "((((state_eq (Some 90) until (((output_eq [(Some (Num 93)), Some VR1,Some T__Q, Some t_bF0, None] until label_eq G_1_1P3a1) aand (output_eq [Some P_D,None] or (state_eq None impl (label_eq X92____R_wC)))))) until (input_eq [Str ''~'',Str B791])))) (watch f7E X_4_J__4)" oops
lemma pD___Z: "(alw (state_eq (Some 96) suntil state_eq (Some 50)) until input_eq []) (watch yb_1_7 n9i3)" oops
lemma G_r8_w: "label_eq W__h (watch v_S S_A)" oops
lemma Y___5bY8F: "state_eq None (watch U3y H_VG)" oops
lemma n_M: "(state_eq (Some 4)) (watch m_KK0RX7 GUM)" oops
lemma c_y: "state_eq None (watch iN41 Y__p0)" oops
lemma n_b___9__7: "(input_eq [Num O9_Q2__n,Num 75]) (watch K_8 b27)" oops
lemma F_J: "((((state_eq None) aand (output_eq [] impl label_eq n90))) suntil output_eq [((None)),Some ws0,None]) (watch W69 x92)" oops
lemma W_8: "((state_eq (Some 495)) suntil label_eq ''Y'') (watch j9S___8 gL40_v)" oops
lemma vd1: "output_eq [Some (Str mJm), Some (Str ''=1''),None,Some (Str bN4), Some (Str ''t'')] (watch G__ou P_65)" oops
lemma Af_5: "output_eq [] (watch C__1 f95)" oops
lemma iy3: "state_eq None (watch KdI r40)" oops
lemma FI__14: "(alw ((output_eq [None, None] impl label_eq ''K7'') until label_eq ''5@3'') aand (state_eq None)) (watch y_Q M78)" oops
lemma d1v_6: "(label_eq ''(9G'') (watch V__3Qj aQ77)" oops
lemma w_o: "output_eq [] (watch C_0 B_ZY8)" oops
lemma O_8: "label_eq Qs3 (watch I_si O_X2)" oops
lemma h_0: "state_eq None (watch cxu D_E)" oops
lemma D1_E: "not (state_eq (Some 40572)) (watch e_K x0_J)" oops
lemma RC_h: "label_eq ''g'' (watch q_X sJvgc)" oops
lemma E_K: "(output_eq [(None)]) (watch N_9 V__70)" oops
lemma R__C: "(input_eq [Num S_x, Num gd_7,Num y__9] suntil alw ((not ((((label_eq t__O or (input_eq [Str R___t, (((Num W_D2_F))), Num 258,Num Y__9, ((Num 1)), Str ''*j<o6?'',Str ''/t|<9)''] impl (((state_eq None until state_eq None) suntil (alw (output_eq []) suntil label_eq P_u))))) impl (state_eq (Some 1) suntil (((output_eq [(Some (Num 839)),Some s_3])) or label_eq '' u'')))) suntil ((output_eq [(Some Ir51)] until state_eq (Some 5)) impl output_eq []))) suntil input_eq [((Str ''/9!'')), Num 8,(Num sQ8W8), (Num D_5), Num 6,Str ''Y'', ((Num N8__Q))])) (watch EE83_n7 r0p)" oops
lemma W_6: "state_eq None (watch Sjk N_B)" oops
lemma fan4n: "output_eq [None, None,(Some (Str ''l'')), Some F3W] (watch C0mm K__4)" oops
lemma U_VG: "output_eq [] (watch tm3 j_z)" oops
lemma cSS4: "(((state_eq None) aand (label_eq ''{+qW'' until input_eq []))) (watch H___9 j0_4)" oops
lemma W_5_H: "state_eq (Some 3) (watch e__2U z_f)" oops
lemma d76t: "label_eq Fx34 (watch tBG_D J0_n)" oops
lemma V5_p: "alw (state_eq None or input_eq [(((Str r31))), Str R7k, ((((Str D5_0)))),(Str ''0'')]) (watch JlB i_3I)" oops
lemma u2O: "(((output_eq [] aand output_eq [((None))])) suntil output_eq [Some (Str ''R#k6M''),(None),Some (Num 913), (Some (Str Ky7))]) (watch i_k DoK_7y__b)" oops
lemma b_G: "(((label_eq ''{'' suntil output_eq [(Some B__4), Some (Str ''lQ4''), ((None)), Some (Num L_4),Some H___c,Some (Str q_628)]) until (((((state_eq None aand label_eq K33) impl ((((output_eq [] impl (state_eq None suntil (((input_eq [(Str n0__6),(((Str p422)))]) until (state_eq None impl (state_eq None or output_eq [])))))) suntil (output_eq [] suntil (output_eq [None])))) impl input_eq []))) until (((((state_eq (Some 40) until not (state_eq None)) aand (input_eq [(Num 33), (Str ''1 ''),Num P__4, Str FPG, Num 1,(((((Num 2725)))))]))) aand label_eq ''_'') until label_eq ''~W<''))))) (watch psA c_g)" oops
lemma JGjlW: "(((state_eq None or (state_eq (Some 79))) aand label_eq s8_i) impl state_eq None) (watch r_5___6 O21)" oops
lemma t_6: "(state_eq (Some 6)) (watch B_7 H_0)" oops
lemma o_X: "state_eq (Some 0) (watch S_ch E_h)" oops
lemma P2L: "output_eq [Some (Num 3)] (watch i_M IVy)" oops
lemma R_7: "(input_eq [(((Str QE79x))), Num Zm_l63] until input_eq [Str t83, (Str C___H), Str ''-'',Str Y0V, Str m0_4, ((Num 9))]) (watch pPk a_j)" oops
lemma T_v: "((((input_eq [Num 36] aand (((state_eq (Some 5) impl (state_eq (Some 80))) until (label_eq r1o suntil ((((((input_eq [] suntil (label_eq V___1 until nxt (output_eq []))) until state_eq None) suntil state_eq None) until input_eq []) or ((((output_eq [(None)]) suntil (input_eq [((Num 4)),Num 0,Num 76] suntil (label_eq O98 until (input_eq []))))) suntil ((((input_eq [Str s__4, ((Str ''6V''))] or (((label_eq ''8~ '' suntil (((input_eq [] impl ((((input_eq [Num B_3, Str ''>'', ((((((Num 92)))))),Num 2] aand (((label_eq v520bi aand input_eq []) aand (state_eq (Some 1) until (state_eq None until (((((output_eq [(None),None, None, None]) aand (((alw (label_eq ''<'' aand (state_eq None until (label_eq ''?}'')))) until (label_eq j__c impl (label_eq JHC_i)))))) suntil (output_eq [Some Cn__Ex, Some B__1, Some r9t] impl state_eq (Some 01))))))))) aand state_eq None) until (state_eq (Some 1) aand (((((((((((output_eq [] aand (label_eq ''('')) aand label_eq ''fAx'') or input_eq [Str O29]) suntil (input_eq [(Str ''*''),Str ZnI] suntil output_eq [(Some (Str ''_'')), (Some (Str ''#A'')), (None), None,Some (Str ''4''), Some (Num 31),None])) suntil (input_eq []))) until (state_eq (Some 9331304)))) impl (((label_eq g__Q4__z) or (input_eq [] suntil ((((label_eq Dv2) aand ((((state_eq (Some 5)) until (input_eq [(Str dH5), Str d__1, Str F_99,((Num C__65)),Str x51] or label_eq ''@''))) aand label_eq ''(''))) impl label_eq Dc5)))))) aand alw (label_eq Z_t)))))) until (((((((((((state_eq None suntil nxt (output_eq [])) or (label_eq v_a impl (((state_eq (Some 5) impl (output_eq [None,Some R_8___h, None] impl ((input_eq [(Num St_D)] suntil state_eq (Some 217)) until state_eq (Some 9)))) until state_eq (Some 3)) impl label_eq M___M))) until label_eq z__7h) until ((output_eq []) aand output_eq []))) suntil (state_eq None or output_eq []))) until input_eq []) suntil ((input_eq [Str j_2] aand (((state_eq None or (output_eq [])) suntil alw (output_eq [(Some (Num a_z)),None,None] suntil (label_eq ''('' until ((((input_eq [(Str ''0#J''), ((Num f8_3E)),(Str F_1x)]) impl output_eq []) or input_eq []) aand alw (output_eq [Some DQJ] impl nxt (input_eq [] impl state_eq None)))))) impl input_eq [])) or alw (input_eq [] suntil (label_eq E0_7))))) aand label_eq CFW)))) aand (output_eq [Some (Str C_r),((Some J73))])))) impl (output_eq [])) or ((((((input_eq [((((Str K_7))))] impl input_eq []) until output_eq []) suntil (((((label_eq ei9k or (((nxt (state_eq None impl input_eq []) suntil label_eq ''0'') impl ((state_eq (Some 4) or input_eq [Str '' ^'',Num 38, (((Str e_H)))]) impl state_eq (Some 4838))))) aand state_eq (Some 6)) suntil input_eq []) or (label_eq dgtZ until ((((((ev (input_eq []) suntil label_eq ''d'') until state_eq None) impl (input_eq []))) suntil (not ((((output_eq [(Some (Str ''6'')), (((Some (Str ''?'')))),Some (Num T66_k_1)] impl output_eq [Some v2pim, Some (Str ''gYS''),None,(Some (Str ''6'')),Some (Str e_u),((Some (Num 1))),Some (Str v8eP_119_i0)])) until (input_eq [Str Z9_O, Num 0437,Num 9] until input_eq [Str ''A'', (Num p_r),((Num 95))]))))))))))) suntil input_eq [(Num O13_E_l95h3_eC8), ((Num 8))]) aand output_eq [])))))))))) or state_eq (Some 176)) aand (input_eq [Str z_W, ((((Num TkA)))), Str C0GG8,Num 3]))) (watch k___V V4F8)" oops
lemma x4K: "state_eq (Some 35) (watch j_W s_7)" oops
lemma O_9: "output_eq [] (watch Z_8pL j9__1_p2)" oops
lemma V__5u: "(output_eq [Some t_2, None, Some D_9c]) (watch pNi_V R__2)" oops
lemma e_J2: "output_eq [(Some (Num U_9)),None, Some (Num 1283), (Some (Str g_e)),Some (Str P_6)] (watch L__k jDP)" oops
lemma c_x: "output_eq [] (watch p_A_0rTH7 Q2__4D)" oops
lemma X3L: "(label_eq '','' or output_eq []) (watch j__H eP6)" oops
lemma L_M: "(state_eq None or output_eq []) (watch nL_t Q_O)" oops
lemma F_4: "((input_eq [] impl output_eq []) until state_eq (Some 7)) (watch tE__65 A_n)" oops
lemma N___1: "(nxt (((alw (state_eq None until state_eq (Some 1))) or ((((((((((state_eq None) or ((((((input_eq [Str O_7t]) impl ((((label_eq ''!1?'' impl ((((input_eq [Str ''d''] suntil (input_eq [])) or input_eq []) aand (label_eq P0d or (label_eq ''W'' or output_eq [(Some K6n),Some T_o, None]))))) until label_eq ''(3'') aand (input_eq [] aand label_eq d_L)))) impl input_eq []) suntil not ((label_eq '' '' until (state_eq (Some 284))) aand output_eq [Some (Str cZ_j),None, (Some j_12)])) impl state_eq (Some 8)) suntil input_eq [(((Num S1Z3)))]))) impl (input_eq [] aand ((((state_eq (Some 9) aand (state_eq None until (((label_eq ''G}) '') or (input_eq [Str ''|'',(Num e___VX),(Str ''?a'')]))))) or state_eq None) suntil alw (((state_eq None impl state_eq (Some 68)) suntil (state_eq None until label_eq ''#4-'')))) aand label_eq ''{qI0'')))) aand (alw (output_eq [((((Some R07K))))] until (ev (((state_eq (Some 34) until input_eq [((Num M_5))]) aand ((((((((((label_eq Z1k suntil (((((output_eq [(Some (Str B_6))] or state_eq None) aand ((((input_eq [((((((((((Str PyT2))))))))))]) aand output_eq [(None),None,(None), Some (Str ''5''), Some Ra3, (None)]) aand (((output_eq [(None),None] aand input_eq []) until (((ev (input_eq []) suntil (input_eq [] until (((label_eq n_4t) aand (label_eq ''('' aand label_eq ''_''))))) or ((label_eq ''E/*!'') or (state_eq (Some 43544) until input_eq []))))))))) suntil input_eq [(Str u_B), (Str ''.e'')]) or (label_eq J375 aand (output_eq []))))) suntil (state_eq None aand (state_eq (Some 9) until ((label_eq ''{B'' aand (output_eq [] aand (output_eq [(Some (Num 923)),None] until output_eq []))) aand input_eq []))))) impl state_eq None) until (state_eq (Some 7) or (((((input_eq [Num 742, Num b_6, (Str M_H), Str LXE__rH, (((Num 0)))] aand input_eq [Str Cu1d,Num W11,(Str R4__c_ehN), ((Str ''.*'')),(Str p_pS)]) suntil (((output_eq [] suntil (output_eq [])) impl (output_eq []))))) aand ((state_eq (Some 1) aand output_eq [None, Some D91, Some z35,None, Some (Str MG0c4),None]) suntil (output_eq [] suntil input_eq []))))))) suntil state_eq (Some 92)) impl input_eq [(Str ''<'')]) or (label_eq ''('')))) suntil label_eq ''$'') suntil (output_eq [] until (state_eq (Some 1) until input_eq [Num I7c__7])))) impl (state_eq None)))) impl label_eq k_y) impl (label_eq ''x}''))))) until ((((((label_eq ''!:'') until input_eq [((Str q_T_9)),Num c_4j,Str U95]) or label_eq ''R){+@'') until (ev ((label_eq b_M34) or (input_eq [Num 99748, (Num 54)] impl (output_eq [None,(Some QHd),(Some (Num 9)), Some J___5, None])))))) impl state_eq None)) (watch mPj G_u2)" oops
lemma a_U: "input_eq [] (watch G_44 f_L)" oops
lemma z_6e: "output_eq [None,Some O_0H,Some IZ_2] (watch f_wY S33e7v77)" oops
lemma l2K: "(ev (input_eq [] impl state_eq (Some 8)) until input_eq [(Num F_P)]) (watch T_1z K1Vn)" oops
lemma Gxh_u26: "state_eq None (watch R_4_9 T9_7)" oops
lemma rS62: "(output_eq []) (watch w_9__08w p2p8p)" oops
lemma u_6: "input_eq [(Num 011), Str ''0e'', (Str ''$5'')] (watch P5_3 y__H)" oops
lemma ukYs: "output_eq [None,None,Some (Num 4865),(Some (Str ''6W-'')), (Some (Num 0))] (watch oLt S_z)" oops
lemma cDas: "(input_eq []) (watch V31 Mzn)" oops
lemma E_b: "input_eq [] (watch t_7 nx_9)" oops
lemma Yd_M: "((((label_eq t__00 aand state_eq (Some 3)) or state_eq (Some 07)) until ((state_eq None or input_eq [(Str a762),Str ''g'']) impl label_eq ''vs2''))) (watch t_5p vdh)" oops
lemma cs_5: "((label_eq oH7 suntil label_eq ''^w;'') suntil state_eq (Some 5)) (watch s_5 my___3)" oops
lemma I_NB: "(input_eq [(((Num T_2))), (Num 604556)] suntil input_eq [Num l_7,Num Z_8__FR, (Str U_2),Num N_9Y,Str g_5_1,(Num 9)]) (watch P2H Q_2)" oops
lemma fPW: "(((alw (state_eq None) impl (((((output_eq [(None),Some (Str U_1)]) until (input_eq [((((Num v_G)))), Str A_5,(((Str ''G''))),Str L_He] or input_eq [(Num O17), Num 4, (Str a5B), (((((Str Cp3))))),Str o_h,(Num 21)]))) impl (state_eq (Some 1) impl state_eq (Some 9))))) until (input_eq []))) (watch L__y M__G)" oops
lemma p_b_9: "(state_eq (Some 8235874) impl (state_eq (Some 0238) aand label_eq ''n'')) (watch P____6 k_i)" oops
lemma uI_L__j: "label_eq ''_'' (watch ay7 i_m)" oops
lemma sJt: "output_eq [] (watch R_9 D7_m)" oops
lemma A_2: "input_eq [Str ''?''] (watch D__k d0L_w)" oops
lemma K__V: "(input_eq [] until (label_eq fd9)) (watch UD2 r_i)" oops
lemma At83: "state_eq None (watch r_l5 e9_2)" oops
lemma k_s: "((input_eq [((((((Str l2K))))))]) or output_eq []) (watch Ma_8__1 DZn)" oops
lemma Cb3: "label_eq K_88 (watch M_4 e_q)" oops
lemma C_Hq: "(((((((label_eq ''#'' until output_eq [None, Some dQ4, Some (Str r_1),((None)), ((((None)))), (Some T___A_S8H),Some (Str ''M''), Some B_1,Some (Str ''1'')]) impl (ev (label_eq O_5O impl (input_eq [(((Num ot5G))), Str Ue4, ((((Str '').`o'')))), Str ''$'', Num I80] impl (label_eq ''%'')))))) or (input_eq [(((Str ''6'')))]))) suntil (input_eq []))) (watch t_f d6Q)" oops
lemma Bz1P_j: "(state_eq None suntil input_eq []) (watch spq i_4)" oops
lemma MH4: "input_eq [Str ''^'', (Str '',<''),(Num U_l2)] (watch A1UcE xeb)" oops
lemma i0_6: "((((((label_eq ''/'') impl (input_eq [(Str p_1), Num qMQ] impl (state_eq None suntil (input_eq [(Num Lv_r_j)] suntil (state_eq None until (output_eq [Some (Str z__3), Some (Str ''-''),(Some (Num 0))]))))))) impl input_eq [Num UE4]) or (output_eq [Some (Num 7)]))) (watch u1_06H_7 h_1)" oops
lemma f__G76: "input_eq [] (watch f_4 FCw)" oops
lemma Qv2x: "((ev ((((((state_eq None until input_eq []) impl (state_eq None))) until state_eq (Some 4)) aand (ev (output_eq [] until input_eq [((((Str ''/&''))))]) aand label_eq u8__3))) suntil state_eq None) until label_eq l76) (watch h0Q__H3F Ro__1_f5)" oops
lemma b_2: "label_eq ''0'' (watch J2O ES_7_q)" oops
lemma q__2: "(label_eq C_d) (watch v9___5 Kku)" oops
lemma N_3: "(label_eq Qxs until (state_eq (Some 1) until (label_eq Yrn1 suntil (state_eq (Some 0) or (output_eq [] or input_eq [Str ''#'', Num 51, ((((Num 8)))),((Num 647)), Num 4, ((Num 056)),(Str ''/GEW8'')]))))) (watch tW067 f_5Q)" oops
lemma v_S_p: "input_eq [(((((((((((((Str ''%''))))))))))))),(((Str uf7)))] (watch VR5__2 p68C)" oops
lemma rjyX: "(nxt (((state_eq None) aand (state_eq None)))) (watch K_po A__p5)" oops
lemma x_ad7: "(state_eq None aand label_eq ''1'') (watch o_p3 Z_E)" oops
lemma z__k: "(alw (label_eq fd_z_5) suntil state_eq None) (watch Z8r S7I)" oops
lemma kuGX50: "label_eq ''`'' (watch wPT_4 e_k)" oops
lemma qf_58q1_8R: "output_eq [] (watch Y6U wk_J)" oops
lemma IA2_5: "(input_eq [] until (state_eq (Some 0))) (watch S__6 U7__tY)" oops
lemma a988: "(input_eq []) (watch W_71 jql)" oops
lemma i4820: "input_eq [Num 48, (Str ''.''),(Str k_b4)] (watch Zx_H3t F_M)" oops
lemma m_H: "(((state_eq (Some 37)) impl ((input_eq [] suntil ((ev ((input_eq [Num 0,(((Num 389957))), Num k_OH3, Num y_L47,Str I_e, Str '':N'', (Str cTY_K)]) or input_eq [(((Str o3cL)))]) or ((state_eq None aand state_eq (Some 3)) until state_eq None)) aand output_eq [None, None])) until (output_eq [None,Some i_91, Some VH_S, Some (Str '':D^-);=''),None, None, Some A_6])))) (watch GR__W u56)" oops
lemma U8a: "(input_eq [] until (((output_eq [] aand output_eq [])) aand input_eq [])) (watch K_w_7 W__3)" oops
lemma h_7: "(label_eq bW2) (watch T_7 w05)" oops
lemma Nf__e: "(((input_eq []) or (output_eq [Some iXQ,None, None] until (label_eq y_7 suntil (label_eq B_J until (output_eq [])))))) (watch I08_2 TG7)" oops
lemma h_8: "input_eq [Num 1] (watch ge5J w93)" oops
lemma ABc7: "(input_eq []) (watch p_3 lr_h2n5_1)" oops
lemma VB0: "(((label_eq Y0I suntil (((state_eq None until (input_eq [Str d_R])) or (state_eq None aand ((((output_eq []) impl nxt (((output_eq [Some Z_1])) suntil input_eq [])) suntil (((input_eq []) suntil input_eq []) suntil ((state_eq None) aand state_eq None)))))))) until (alw ((state_eq None) aand (output_eq [])) until (((state_eq None) aand (input_eq [] until state_eq None)))))) (watch O___l2 R_52)" oops
lemma RQmR: "label_eq K_O (watch R9k m37)" oops
lemma cy_8: "output_eq [Some ZQ3, None, (None),Some (Num w_A), Some P_N] (watch K_O h_6N)" oops
lemma pzV: "(label_eq l__e suntil (((label_eq ''k'' impl state_eq (Some 617)) suntil ((((label_eq ''72}+'') until ((((((ev (input_eq [(((Str DV7F))),Num KrV, (Str c_C)] aand state_eq None)) until label_eq e8e) until (((input_eq [] until state_eq (Some 474)) impl (input_eq []))))) or ((label_eq '':'') or label_eq E73))))) or label_eq LpB)))) (watch l4_6_7 I_0)" oops
lemma fT_Q: "label_eq B55 (watch v97 XX5)" oops
lemma T_Xr: "label_eq ''~4}'' (watch Y_____78 VS_R)" oops
lemma V_0: "(label_eq ''{'') (watch Id9 w_5)" oops
lemma K0___8: "(input_eq [Str l__9_1,Str z_1__q] until label_eq ''@42'') (watch nUx z8_Fb_4)" oops
lemma tW_2__9: "(((((label_eq ''5(=<<'' suntil (output_eq [((Some g9_99)), None,(Some N39_G),Some (Num D_i_5)] impl state_eq (Some 7))) impl (nxt ((state_eq (Some 5)) impl label_eq g38) until state_eq None)) or (nxt (state_eq (Some 9) until ((output_eq [None] suntil (output_eq [] suntil nxt (output_eq [Some (Str S98)] aand ev ((((label_eq Z__0) impl output_eq []) until ((((input_eq [] impl ((label_eq ''i'') suntil (state_eq None or label_eq P2B))) suntil label_eq ''%'') until (input_eq [] impl ((((output_eq [Some (Num 0),(Some q_3_7O), Some Pmt_6, Some (Str i_YDD)]) or state_eq (Some 85375)) or (input_eq []))))))))))) until label_eq ld6))))) or input_eq []) (watch Q46 d7I)" oops
lemma X_p: "label_eq a_W (watch Zh9 I_h)" oops
lemma O7Z: "(label_eq I5_8 impl not (label_eq a43__hy suntil input_eq [])) (watch V_s7 L__9)" oops
lemma seQ8: "label_eq ''1^'' (watch L079 u_6b)" oops
lemma J_E: "((label_eq ''^{)7'') impl input_eq []) (watch u_c lm_0)" oops
lemma N_990J_6F2: "label_eq vwJ_7s (watch D__l qZ_t)" oops
lemma N__i: "state_eq (Some 7) (watch e6M wc__C)" oops
lemma Z81: "(output_eq [(Some (Str t__kn)), Some a__4y,(None)]) (watch K1__1 W6_P)" oops
lemma q__R_8: "((((label_eq ''V&'' until state_eq (Some 876)) aand (((((label_eq ''$6J#pU+'' aand output_eq [Some I1A, (Some (Str '';'')), Some (Str I23), Some (Num Ysd),(None), Some G_4, Some (Str cFj),None,(Some bL__9)]) until input_eq []) until (state_eq None))) until label_eq j_p))) impl input_eq []) (watch uJS Q_0)" oops
lemma tzL_U: "(label_eq ''.*<'' impl (((label_eq ''~)s'') aand label_eq s_E) aand nxt (nxt (alw (state_eq (Some 8) suntil output_eq [])) until label_eq ''F_5''))) (watch V_s YPU)" oops
lemma NiR: "((output_eq [] suntil output_eq []) impl output_eq [Some (Str WnA), Some x_6, Some (Num W5_I)]) (watch hwm_o u_c)" oops
lemma r__O: "input_eq [] (watch B_44 V_06)" oops
lemma Q_x: "(((state_eq (Some 68)) suntil ((state_eq None aand label_eq w40) suntil (output_eq [])))) (watch R_1 T1_g)" oops
lemma mG09: "((((state_eq None impl (((state_eq None) impl (output_eq [])))) or (output_eq [] or not (output_eq [((Some (Str ''6'')))])))) until alw (((label_eq s___B until (state_eq (Some 5))) suntil state_eq None) or label_eq ''^%'')) (watch KK7 z09__2)" oops
lemma Hz7: "label_eq J_Q (watch pJ_0Gu_Y L__G3)" oops
lemma P53: "((((ev (((state_eq None suntil input_eq []) impl (input_eq [Str '','']))) until (input_eq [((Num ME4_1_x1)),Str q4_51] or input_eq [])) or (input_eq [((Str ''.& M'')), Num r____7p] until (((output_eq []) impl label_eq ''J'') suntil (input_eq [Num V_r] or output_eq [Some g_4tN,None,Some (Str p__h)]))))) aand label_eq ''*6.'') (watch x_J Kg6)" oops
lemma ql1: "((((alw (state_eq (Some 5477) impl label_eq i1_NY2_2)) aand not (input_eq [] or label_eq '')'')) until label_eq yiNp_Z5) aand output_eq []) (watch Y_5___Y u_0Z)" oops
lemma R_u: "(label_eq T34) (watch X_3 r_s)" oops
lemma U_R: "output_eq [None,None,Some x_j_52] (watch IU2 q_2)" oops
lemma Xa1: "input_eq [((Str ''<'')),Num 198] (watch Q5_h L42)" oops
lemma C_FVx9q3j: "(input_eq []) (watch L_y9 G_F_PeD)" oops
lemma m__6B: "state_eq None (watch P47 K_vJ)" oops
lemma X_n: "(input_eq [] until (output_eq [])) (watch y_R1 Fm1)" oops
lemma z_y7AKD: "output_eq [None, (None), (Some z4__4x5_u),((Some (Str ''9?'')))] (watch q8C F_V)" oops
lemma C_3: "(input_eq [] suntil ((((((ev (state_eq None impl (output_eq [Some WS8I, (Some (Str uJy)), None,Some w9q,Some (Str ''y>$'')] aand state_eq None)) until input_eq [(Str K_P),Str ''|_{~>~'', Str ''11-'']) suntil state_eq (Some 0604)) suntil state_eq None) until (output_eq [(None),((Some (Str O11))),((((Some (Num 8))))),Some (Str ''{-''),Some (Str ''VK''), Some (Str Q_s), (Some haC),None] impl (state_eq None)))))) (watch I_J ybH)" oops
lemma M_3WL: "(((((label_eq ''K86'') until (input_eq []))) suntil (((((input_eq [] until (state_eq (Some 05) impl (label_eq ''~u,''))) until label_eq ''5'') aand (input_eq [] impl label_eq ''~39>''))) aand label_eq ''<''))) (watch V2oQ aM101)" oops
lemma d0D9Yo: "label_eq J17 (watch f__o A84q)" oops
lemma y5g: "((input_eq []) aand output_eq []) (watch Sdsy__8Uz L_w)" oops
lemma M_3: "label_eq ''a'' (watch a_7 p_I)" oops
lemma bX6a: "input_eq [] (watch BHL b4W)" oops
lemma SF6: "(label_eq j_d suntil state_eq (Some 1)) (watch Y_0 BLK)" oops
lemma x__2: "(state_eq (Some 263) suntil not (label_eq ''>5/='' suntil label_eq p_3___6J)) (watch gs484a55__y2 u_k)" oops
lemma r_x: "label_eq M_n___0X (watch UCc t05x)" oops
lemma j_5: "output_eq [] (watch Y0S7 e_8_8N)" oops
lemma z7S: "((nxt (((((state_eq (Some 284)) impl (output_eq [] impl (((output_eq [Some I_j] aand (nxt (input_eq [(Num 8), (Num V_P8_1),(Str ''O'')] or output_eq [(Some D_9_7)]) aand state_eq (Some 77))) impl ((state_eq (Some 1) suntil input_eq []) or label_eq ''_!}''))))) or input_eq []) impl (state_eq None or (output_eq [] impl output_eq [None, (Some w_0)])))) impl output_eq []) suntil (input_eq [(((Str U__1)))] aand ((output_eq [] or input_eq [(Num 26), (Str FaN),(Str l09), ((Num L_8)),Num 8, Num bw12, (((((Str R__UXH))))),(Str mUb5), Num L_bH]) or state_eq (Some 87)))) (watch P8_63____I VN_1)" oops
lemma OK4: "input_eq [] (watch p_1 jEM)" oops
lemma b__2_W: "input_eq [] (watch F_H3 a39O)" oops
lemma h8_E6: "(output_eq [] until state_eq None) (watch Q_b E1658)" oops
lemma mXE_a7: "(state_eq None aand output_eq []) (watch Wp_11 s8t)" oops
lemma Q_C: "(input_eq [Str ''-n'']) (watch Tj3_5 S9g)" oops
lemma uGr: "(((input_eq [(Str Zv_66O), ((Num 6))] or (alw (label_eq z___h0) impl ((((label_eq L_zI aand (label_eq ''8>('')) or (((((output_eq []) suntil output_eq [None, None, Some (Str i_L), Some z9_f]) aand nxt (alw (((input_eq [(Str J_J4),Num 7661,Str Yc65] suntil alw (output_eq [None, (Some (Num oGQe)),None,None,(None), (None)])) aand input_eq []) impl state_eq (Some 30)) until output_eq [])) suntil (((state_eq (Some 235) or (((output_eq [] suntil (input_eq [] impl label_eq kM_b)) impl (output_eq [None])))) impl (((label_eq T__rr) suntil (label_eq M_w or input_eq [])))))))) aand (state_eq (Some 19) suntil (state_eq None suntil ((input_eq [] aand output_eq [(Some (Str Q_p__7)),Some (Str ''&''),Some O57,None]) or input_eq []))))))) suntil (output_eq [] or ((label_eq u_A) aand label_eq ''~'')))) (watch y__a nOZ)" oops
lemma h4_t__0: "((output_eq [] until input_eq []) aand alw (label_eq G_04C or label_eq f_4)) (watch B_5 O_5___E)" oops
lemma L__8: "(input_eq [Str ''j !90@'']) (watch A4K_6 Q_b1)" oops
lemma R14: "label_eq ''7'' (watch SxL4 l_r)" oops
lemma v18: "input_eq [] (watch xB7 l_zk)" oops
lemma O2_U: "(output_eq []) (watch c_sDX6 r_e)" oops
lemma s29__1: "(label_eq hZ0) (watch y__v e05)" oops
lemma D__1: "state_eq None (watch Z_4 L_I)" oops
lemma Z_o8_8: "(((alw ((input_eq []) suntil input_eq [])) or (input_eq [Num I_m, (((Num F__D))), Str QKs] aand output_eq [Some (Str Ph_h), Some (Str G73),((Some Zw0)), None]))) (watch l_G O__p_27)" oops
lemma VSg: "(input_eq [Str ''=''] until input_eq []) (watch N__0 t_5J)" oops
lemma B__W: "output_eq [] (watch X_9 cg0ik_3)" oops
lemma d4b: "state_eq (Some 3) (watch G92 xw6_8X)" oops
lemma w60: "alw (state_eq (Some 3) impl ((label_eq ''89'' aand ((label_eq ''?'' until ((((((not ((((state_eq None aand ((((input_eq []) or input_eq []) impl (alw ((((alw (state_eq (Some 8213) or (state_eq None suntil (state_eq None or (label_eq ''=J`L!''))))) suntil (input_eq [] suntil (((((((nxt (input_eq [Str u_Y, (Str ''|''), Str ''+}18''] aand (input_eq [])) suntil (nxt (state_eq None) suntil (state_eq None aand (label_eq u_m aand input_eq [Str S__u, ((Str uJ_M6)),Str Y1_0S,Str ''{'',(Str abD),(((Str ''.3'')))])))) impl (((((input_eq [(Num 1), (Str ''%''), Num 8, ((Str ''/'')), Num 08,Str dqo] or (input_eq [Str ''j<''] suntil (((((label_eq jES or input_eq []) or (label_eq R_4i)))) aand (((state_eq (Some 7) suntil not (input_eq [] aand (input_eq [((Num D2f)), Str ''`:'']))) aand output_eq []) suntil (state_eq None or (((((((((((output_eq []) suntil (label_eq C60 or not (state_eq None impl label_eq Tg_4)))) impl (output_eq [] or ((((input_eq []) until input_eq []) aand (((label_eq X208 suntil ev (((state_eq (Some 3)) suntil ((input_eq [(((Num qk1))),((Num f___13))]) impl output_eq [Some RD_Y,Some e6_L3, Some mM9,Some (Num N1X)])))) impl (((((((output_eq [] suntil ((label_eq '':Y>Q'') aand output_eq [])) impl ((alw (label_eq '')'') impl state_eq (Some 14281362)) until label_eq P_9H)) aand input_eq []) impl ev (output_eq [Some m_3, Some jQ8,Some (Str ''~?''), ((Some (Num C__S)))] impl state_eq None)) suntil state_eq (Some 409)) until (state_eq None)))))))))) until (((((input_eq [Num 249, (Num 8)] until output_eq [Some d_6]) suntil label_eq p0y) impl (output_eq []))) or (((state_eq None) suntil (state_eq None)))))) aand (input_eq [Str ''I}P.34'',((((((((((Str i_25)))))))))),(((Str nKs)))]))) suntil input_eq []) suntil input_eq [(((((Str vWWu))))),(Num 2),Num o6___b, Num WpG])))))) impl ((output_eq [None] or (input_eq [] or input_eq [(((((Str ESn1))))),((Num 691)),(((Str ''@''))),Num a_3,(Str ''4'')])) aand ((((input_eq [Str bU7] suntil (output_eq [((Some (Num B_q))),Some (Str ''.'')] impl ((state_eq (Some 8)) until input_eq []))) until (((((((((((input_eq [])) impl ((output_eq [] suntil (((state_eq None) suntil (label_eq g_C1)))) impl (output_eq [] until (label_eq C7_2 or output_eq []))))) or (((input_eq [] or label_eq V___2) impl input_eq []) aand output_eq [Some o0_1S_7]))) impl (((((input_eq [Str ''-.980'', (Str ''_@Q6O'')]) until input_eq [Str T3F, Str ''-'',Num oj_7]) suntil state_eq None) impl (input_eq [(Str e_r)]))))) impl input_eq [(Num 8), (Num 4),Num z_R0__8_4__s,Str ''6'',((Num 6)),Num j_V, ((Str ''~P''))]) until (output_eq [Some O__i]))))) aand input_eq [])))) or (input_eq [] impl ((output_eq [None]) aand state_eq (Some 9324))))))) or (output_eq [] impl (((state_eq (Some 5) suntil ((output_eq [] suntil input_eq []) aand state_eq None)) aand (((output_eq [Some rn5] or output_eq []) aand state_eq (Some 11913)) impl ((input_eq [Str WL4,Num 68,((Num 2)),Str ''y'']) aand output_eq []))) until ev ((state_eq None until ((input_eq [Str J_R,((Str ''m''))] impl ((output_eq [Some (Num V_8_0Ml), Some e27_D, Some (Str f_r),Some (Str ''c#a''),None, Some t_6]) or input_eq [(Str ''o'')])))) impl output_eq []))))) until output_eq [Some (Str ''`r''),(Some O02)]) until label_eq Y2dX)))) impl input_eq [(Str gK7),Num IJ7__O]) until label_eq q7t)))) until (input_eq []))) suntil state_eq (Some 2344)) until (label_eq X_8 until (output_eq [] impl nxt (state_eq (Some 1) or (state_eq None))))) aand output_eq []) impl input_eq []) suntil input_eq [Num y_DR,Num 6,((Num G5b4)),Num e_6]) or (((state_eq None) impl (not (input_eq [] aand state_eq (Some 50)) impl (output_eq [Some (Num 17216), Some (Num 33), (Some S69), None,Some (Str ''0@XU'')]))))))) or label_eq j29)) or (((((((ev ((((state_eq None) or (label_eq x_88gm impl alw (((((input_eq [((Str ''qQ4'')),(((Str ''O9''))), (Num i35), ((((((Num 7))))))] aand label_eq F_kqw2) until ((((nxt (label_eq eca impl nxt (state_eq (Some 86) aand ((((((label_eq gP3__OR_2U) until (state_eq (Some 2)))) until (alw (((nxt (state_eq None until output_eq [])) aand (state_eq None impl (label_eq rT32 impl (input_eq []))))) impl (label_eq x0__C_y)))) aand state_eq None))) impl (label_eq u85)) impl ((not (nxt ((output_eq [] suntil (label_eq IT8)) until input_eq []) until label_eq j___1O) until (label_eq ''-'' until (ev (input_eq []) aand state_eq None))) suntil output_eq [Some xz7, None,Some (Str b_5),None, Some Hhh_n,Some AT85k, Some (Num 7), (Some VO5)])) until (((((input_eq [(Str a32)] aand label_eq cu8) or ((input_eq [(((((Str ''8^'')))))] suntil output_eq []) or (input_eq [] or output_eq [None,None])))) or (output_eq [Some r___7] until input_eq [(Num 4579)]))))))) or label_eq P0S1) or state_eq None)))) or label_eq Z8nYj)) impl input_eq []) suntil (alw (label_eq ''&''))) impl (nxt (input_eq [])))) until (((((input_eq [(Str J_78__W),(Num v_0), (Num R_s),(Str rXV)] or ((((output_eq [] aand (label_eq V3__7)) suntil state_eq None) impl (label_eq aAtC)))) suntil input_eq [])) suntil (((((input_eq []) suntil (alw (state_eq (Some 25489))))) or input_eq []) suntil label_eq '';''))))))) (watch MOn q_g)" oops
lemma w__9: "(input_eq [Str '' #'', Num g_2_9kG,Str ''eo^?n'',Str t_h,Str oe8]) (watch S___F w3u)" oops
lemma FRb_5: "input_eq [] (watch r__1 A_5)" oops
lemma Fk48: "label_eq ''<'' (watch n_6 c_2_x_7)" oops
lemma P_2: "output_eq [] (watch rW0_FD6 sEC)" oops
lemma o__L: "((output_eq []) suntil input_eq [Num t1w]) (watch L2e tHj)" oops
lemma J31: "output_eq [Some L_07___9] (watch J_1 nZ____Dl)" oops
lemma xjv7: "state_eq (Some 2694) (watch p_N r_2o_C)" oops
lemma x0d0: "(label_eq a_x until ((state_eq None) until output_eq [Some (Str ''s>''),None])) (watch N1_J Dh_8_0P2c_N0)" oops
lemma M___6: "(input_eq [Num 63, Num H_N, Num u6__3, Num 8, Str ''_O''] aand label_eq Q_u) (watch BYt I_1)" oops
lemma M4_9l: "(output_eq [] impl state_eq None) (watch S__2O d_v)" oops
lemma N92: "(((input_eq [] or ((input_eq []) aand state_eq None)) aand (label_eq G1v until (output_eq [None, ((Some B__O9_9)), Some (Str ''#''), Some (Num y_c)] until (output_eq [None, (None)]))))) (watch joZ Z8p)" oops
lemma v0j: "output_eq [(Some (Num 0)), None] (watch TW1q H_B)" oops
lemma v__1: "(state_eq None) (watch M___5 v3_0)" oops
lemma XZt: "state_eq None (watch P9S Y_6)" oops
lemma W3Oj: "state_eq (Some 2) (watch Z_0 N_0_w_19)" oops
lemma d_2: "output_eq [((None))] (watch g_7 Z7_7)" oops
lemma x__V: "output_eq [((Some (Num 889))),Some (Num 4),Some (Num 93),Some Ru3f0,Some jnz9, None] (watch QT3 a_8_L)" oops
lemma v16: "label_eq ''?'' (watch g_0 nE1)" oops
lemma fT8: "(((label_eq ''Z%-7'' aand state_eq (Some 284951)) aand (label_eq I_1 until ((((((output_eq [] until ((((input_eq [Num 1] impl state_eq None) or (input_eq []))) aand label_eq Z_j)) aand (state_eq (Some 08353) aand (label_eq ''8'' until (input_eq [] or state_eq (Some 88)))))) or state_eq None) or (output_eq [])))))) (watch P_s f6_G)" oops
lemma Z_0: "output_eq [] (watch y_9 hd_9lRK)" oops
lemma h__8e: "state_eq (Some 3046) (watch c2L_7 c___G)" oops
lemma Jm1: "ev (((input_eq [(Num 1), Num P___f_y, Num Nd7, Str ''9'', (Str pT_1), ((Str g__z))]) or (((input_eq [Num gHd, ((Num d9K7))] impl state_eq None) impl state_eq None) until input_eq [((((Str ''^'')))), (Str d_J), Num 6]))) (watch S_02n f3Z)" oops
lemma Q80: "output_eq [Some s_3U] (watch U____2 an2)" oops
lemma Dx6: "label_eq T4_3 (watch FX4_3 GYp)" oops
lemma h82: "state_eq None (watch l2_f MYUr)" oops
lemma z_9k: "output_eq [Some hz5x7,None, None] (watch m_m Q__2)" oops
lemma b_1: "label_eq ''{'' (watch W_1 L_ca5)" oops
lemma W_9: "label_eq Mc_12_dv_g (watch h_O ml_K_xu)" oops
lemma q6f: "input_eq [] (watch b3__h0Z7 N___T_6)" oops
lemma kt_9: "((((label_eq ''>,E'' or (input_eq [((Num s_e)),Num 74, (((Str s_6g)))] impl input_eq [])) or (label_eq ''(''))) until label_eq X__68) (watch w7w5 Td_w_U)" oops
lemma h_7_7H: "output_eq [] (watch q_w Mv___g)" oops
lemma I1t: "(output_eq []) (watch S2Z a7I)" oops
lemma b7y1: "(output_eq [] suntil ((((input_eq [Num 3,(Str MYj), Num u21q5,Str TUa]) impl (((output_eq [] until (state_eq None)) suntil (state_eq None)))) or (((((((output_eq [Some (Str ''I9^'')] aand ((label_eq OCn aand state_eq None) aand output_eq []))) or (state_eq (Some 5)))) until label_eq y45) until (((ev ((input_eq [] or not (output_eq [Some i_6, (((((None)))))] impl output_eq [None,Some (Str b_h76)])) suntil ev (alw (output_eq [None] until ((output_eq []) impl label_eq ''='')))) impl (((state_eq (Some 51) impl nxt ((output_eq [(None), Some S_dI,Some b0__4,None,Some (Str d_C)] or label_eq t0T) suntil output_eq [None])) or alw (state_eq (Some 45) or input_eq [Num CC_5_4])) aand output_eq [])) or ((output_eq [Some y28bh,Some v_2]) or label_eq ''#'')))))))) (watch t__nGY y_o)" oops
lemma s__Lt: "output_eq [] (watch g_u e_7)" oops
lemma F_4: "state_eq None (watch lLF O__1)" oops
lemma E__18: "(output_eq [] aand alw (label_eq ''E'' suntil (input_eq [] impl (((output_eq [] until ((input_eq []) until not (input_eq [] until input_eq [Num 9643]))) until ((output_eq [Some x_9, (Some (Num y_i)), (None)] or (((((((alw (output_eq [Some (Num Y_J),Some Z03___f])) impl (((state_eq None aand input_eq [((Str w8_H)),Str ''{'',Num 205,(((((((Num 0))))))),((Num n3_0)), Num 7,((Str m_A)),((Num 7))]) or ((label_eq ir_2 impl (label_eq oY3)) suntil label_eq ''0*37''))))) suntil not (label_eq ''_'' or state_eq None)) aand output_eq [Some (Str ''w4'')]) impl (input_eq [] suntil alw (state_eq None impl ev ((((output_eq [] or (ev (((ev (input_eq [])) until (label_eq ''G'' or (ev (output_eq [] aand (((label_eq V_19) suntil (output_eq [] until (label_eq C870 until (((input_eq [(Str E__t), (Num J_3),Num 58,Num 9]) or (state_eq None suntil (((label_eq Q0e_8) impl (not (state_eq (Some 63))))))))))))) suntil (((((((output_eq [] aand (input_eq [] until output_eq [(Some K_j),None,((Some j_19_1dm)),(Some l__J5),Some (Num Od5)])) suntil state_eq None) until label_eq ''4'') or ((input_eq [Num 0, (Str H___W),(Str B_o5)] impl (label_eq Jd3d1 impl (((output_eq [] or state_eq None) or ((((((label_eq ''x'' impl (output_eq [(Some (Str m__w)),Some (Num k_s),Some (Str ''%''),Some (Num m___Xx), Some (Num 2)] aand (input_eq []))) until input_eq []) impl (label_eq T1_o_9 or alw (((output_eq [Some (Num S_3)]) impl (((output_eq [(None),Some F_w,Some (Str ''3''),((Some (Num U_Z0u)))] or (input_eq [] impl (((output_eq [Some M_pk_xL,Some I__K,Some a_1_T]) until (state_eq (Some 3) aand output_eq [Some o_9C,Some N_4xz,Some (Str H42gsk)]))))) aand ((label_eq t90G_7 until output_eq []) aand output_eq [])))))))) suntil label_eq x_7) until label_eq ''O''))))) impl output_eq []))) impl input_eq []) impl alw (state_eq (Some 8) or (((state_eq (Some 6)) until (((((label_eq U_MfK) suntil ((label_eq ''#'' suntil state_eq None) until ((((label_eq ''P'') impl (output_eq [None]))) until nxt (((((((((output_eq [] or input_eq [(Str ''s3'')]) impl state_eq (Some 2)) until (((state_eq None until (state_eq None)) until ev ((((((((((((((((((label_eq ''r>'' or input_eq [Str '','']) aand state_eq (Some 8)) or (state_eq (Some 3) suntil label_eq D_4))) or ((output_eq [(Some C_C), Some (Str ''$>''),((Some R__sBif)),Some WFO] impl (state_eq None aand label_eq '',,'')) aand label_eq ''!'')) or label_eq vRl_d) aand ((label_eq ''&&'' or input_eq []) suntil input_eq [Str ''?B<'',(Num X_j5)]))) suntil label_eq Q__6) suntil label_eq k_4) aand (output_eq [(Some L2S)])) or ((label_eq E_V suntil input_eq []) until not (output_eq [None])))) or input_eq [(Str K72)]) impl ((state_eq None until output_eq [Some (Num 2)]) or input_eq [Num d3w8,Str ''#+'', ((Num 23)),Num z5_kH, Num 2, (Str '':9''),Num 18,Str ''Ve'', Str v_w]))) suntil (state_eq (Some 4) suntil (nxt (output_eq [Some (Num b_8O), (((Some FHgB)))]) impl (((output_eq []) aand (state_eq None or input_eq [])))))))) aand state_eq (Some 5)))) suntil label_eq KtA) suntil alw (((output_eq [Some m_L_Q,None, Some M23c,(((None)))] aand ((label_eq ''u0'' suntil label_eq GzZ___4) aand state_eq (Some 0))) aand ((((ev (state_eq (Some 3) impl input_eq [Num R_9]) suntil output_eq [Some i_3])) aand (input_eq [] aand (label_eq L_4))))))) until (((((output_eq [] until output_eq [None]) until output_eq []) suntil ((label_eq ''7'' until ev (input_eq [(Str elw), Str ''Mc+k'', (((((((((((((Str f4_Zm)))))))))))))])) suntil (((state_eq (Some 24) aand label_eq ''n'') or (label_eq Y6O_5 suntil state_eq (Some 4)))))) until ((output_eq [((Some b_V_5_9))]) or state_eq (Some 47)))))) impl not (label_eq b39_75))))))) or input_eq []))))))))))) until (input_eq [(Num J6_8_I),Str q__71F, (((Num h_U)))]))))))))) suntil output_eq [Some Zs____4, (None), Some A8___n,(Some B__N)])))))) (watch G1x B_a)" oops
lemma B_2: "label_eq lZP (watch G_6C____4E h_Y)" oops
lemma kBF: "(nxt ((label_eq '',('' aand label_eq D_E) or input_eq [Str h6a, (Str ''W''), ((Str n63)), Str ''2'',(Str '')''), (((Num 9)))])) (watch F_1 y_n)" oops
lemma e5_w: "(output_eq []) (watch Y_8 Re7)" oops
lemma p2_W2: "(((((not (((state_eq (Some 7)) impl output_eq [])) impl (((output_eq [] aand ((input_eq [Num 8, ((Str I__55K))]) or (state_eq None aand ev ((((((ev (input_eq [Num o4s_75]) impl output_eq [Some e__c, Some zC2, Some (Str ''NfC'')]) suntil label_eq Oa3X) impl (((((output_eq [] suntil ((state_eq None) until output_eq [])) impl nxt (input_eq [Str u_o,(Num n_R1_2)] aand (output_eq [None, Some r__Y,((Some (Num T_Z)))] suntil (state_eq (Some 1) suntil ((not (label_eq m_t impl (ev (((((alw (output_eq [(None)] impl ((state_eq None or (output_eq [Some V_sOPJ1H] suntil (nxt (output_eq [(None),Some (Str '':a''),None,None] impl (((input_eq [] or output_eq []) impl input_eq [((Str Nbb)), Num Z2Y6]) suntil input_eq [])) aand (label_eq bl3)))) suntil state_eq None)) aand (output_eq [(Some i_38_7), None,Some Y_y])) aand (alw (label_eq ''=|*.{=w'' aand (input_eq [] or (state_eq None))) suntil ((label_eq ''+'' aand label_eq P__888_y) impl state_eq (Some 7))))) aand output_eq []) aand (label_eq ''1;'' or label_eq ''+tc4'')) aand state_eq (Some 7)))) or ev (input_eq [Str g3c, (((((Num L46))))), Num 58,(Num 2),((Num Y__w___717)),((((Num 12985))))] or label_eq ''1$'')))))) suntil (((state_eq None) suntil state_eq (Some 2)) suntil input_eq [((Str c38)),(Str ''62'')]))) until input_eq []))) aand (((output_eq [Some F8e] or ((ev (input_eq []) until state_eq None) suntil label_eq D_Q)) impl (state_eq None until output_eq [])))))))) aand (label_eq ''.'')))) until input_eq [((Num e_6f5)),(((((Num 9))))),(Num 78702), Str ''0'', Str g_5,Num GP6,Str d_8, Num b_I]) impl (state_eq (Some 81) aand (state_eq None or label_eq g_7))) impl ((((output_eq [(Some (Str j_Y)),Some (Str ''/$''), None] suntil state_eq None) impl (output_eq [((None)),(Some U_w), Some v_4]))) or alw (((((label_eq ''<'') until output_eq [None, Some RcT,None])) suntil ((((state_eq (Some 4)) or (state_eq (Some 39) impl label_eq W5_0264)) or ((input_eq []) or label_eq X33)))))))) (watch C_Zy r52b)" oops
lemma aa9: "(state_eq None until ev (((label_eq K_79) impl (((((output_eq [Some y_6]) impl ((output_eq [Some m9m2, Some (Num 6),Some (Num v_HD), Some (Num 831)]) until output_eq [])) until output_eq [(Some i_8),Some oF0,Some (Str RP17),None,Some (Str ''~''),(None)]) impl (output_eq [] until (input_eq [(((Str '')''))), (((Str Sl___Pw))), (Str A_MH), Str ''1'',Num kZ4T,Num 5, ((Str c__3))]))))))) (watch JAR Sx9)" oops
lemma X3P: "(state_eq (Some 0)) (watch q_oU G__T)" oops
lemma r_W_t_N: "(output_eq [Some Al_A] aand ((((label_eq Z9K53 aand input_eq []) impl (state_eq (Some 506)))) impl label_eq nH_F)) (watch R_9 DR3)" oops
lemma P_1: "(state_eq (Some 837) suntil ((not (((output_eq [] aand (state_eq None impl ((label_eq c_l impl ((input_eq [(((Num y6u0))),(Str H_6)] suntil nxt (state_eq None)) impl state_eq None)) suntil state_eq (Some 85)))) or label_eq ''!-~'') aand (input_eq []))) aand (state_eq (Some 1)))) (watch L21P___G e3_y8)" oops
lemma jmb: "label_eq K6j (watch fF_8 g__0)" oops
lemma E5M: "(state_eq None) (watch K4_F xEhq)" oops
lemma j_b: "(input_eq [((Num 97)), Num 0]) (watch Y3lM Z4_a)" oops
lemma I_m4: "(((output_eq [] suntil ev (alw (((not ((input_eq [] aand (label_eq S_36))) aand state_eq None) aand (state_eq None or output_eq []))) or (((input_eq [(((Num A48))), Num QGA, Num 4]) suntil (nxt ((output_eq [Some S_D,Some E__9____3,None, (Some zpc),Some s9_3] or (output_eq [Some u7___8])) suntil (input_eq [(((((Num H__9)))))]))))))) until label_eq ''4k'') suntil output_eq [Some (Num 6)]) (watch E1_Y S_x8)" oops
lemma Z__7_5: "label_eq ''O'' (watch X____a J_N)" oops
lemma Ma_P: "(((((((((((state_eq None impl (label_eq k6xd suntil (output_eq [Some (Num 866)]))) impl ((((((state_eq None aand (state_eq None or (state_eq (Some 6)))) or ((output_eq [Some m7L,((((Some (Num x_y))))), Some (Str bQ__R_p3),Some z0__G, Some F0__K, None, Some zz0] aand ((((output_eq [Some (Str kU_c),None,None, Some f_nd, None,Some (Num 1),None, (((None))),Some (Str ''43'')] suntil ((output_eq [None, (((Some wt_9))),None, None, Some Ne1] or output_eq [Some (Num 1), Some T_o, Some V__2,Some A_1,Some (Num 33), Some (Str u7___2Sj3__5),Some u_B1,Some (Num N_9),Some (Num Gxv)]) aand (state_eq (Some 2) or (state_eq (Some 3729))))) aand nxt ((((input_eq []) until (input_eq [] until output_eq []))) impl (input_eq [] impl input_eq [Str ''%'']))) suntil ((input_eq [] or (output_eq [] aand ((output_eq [] impl label_eq ''~'') aand input_eq []))))) suntil ((label_eq C__Z or not ((((label_eq ''^4'') aand (state_eq (Some 6) or state_eq (Some 2)))) aand (((output_eq []) suntil input_eq [(((Num 16))),(Num 18)]) or nxt ((label_eq Lk_N or label_eq fY2C) aand output_eq [])))) until ((((output_eq [] or input_eq [(Num 1),((((((((((Num m_F_54q_j_g))))))))))]) until (state_eq (Some 44)))) or state_eq None)))) aand nxt (input_eq [])))) or output_eq []) suntil (input_eq [Num Hc3, (Num 3), ((Num W_8)),Num Z948, Num s2G87] suntil (input_eq [] until alw (state_eq (Some 79)))))))) aand (state_eq None or ((output_eq [] suntil (state_eq (Some 92) until nxt (label_eq B_1 or alw ((((nxt (state_eq (Some 398)) aand (state_eq None impl state_eq (Some 72))) aand ((state_eq None aand ((label_eq z6T aand (((((((state_eq None) aand (label_eq f2__c suntil state_eq (Some 18)))) until (((state_eq (Some 560) or alw (output_eq [Some LrG] suntil label_eq ''2'')) aand (state_eq (Some 8)))))) aand (state_eq (Some 4) suntil state_eq None)))) impl state_eq (Some 8402))) suntil input_eq [(Str ''8''),((((Num s__Y)))), (Num W_8),(Str ''3''), Str o_G]))))))) suntil label_eq W_KM7)))) or label_eq o__Z8_2) impl label_eq ''9'') suntil (ev ((((state_eq (Some 89) suntil (label_eq M__5 impl label_eq i3C)) until state_eq None) suntil (((((((state_eq None) suntil label_eq r__09) until label_eq ''/)<'') aand output_eq [Some vP_8, None,None])) aand (state_eq (Some 79) or label_eq F_1))))) aand nxt (input_eq [((Str ''r'')), Num u_2850,(Str ''<''), Str ''~):/D)V'', (Num L_o_2), Str ''5n''])))) or state_eq (Some 1)) until label_eq A_w) (watch YQsu__6 IJ_5)" oops
lemma A__oI_m: "label_eq ''<`R'' (watch n2U xT__9)" oops
lemma G84: "(alw (output_eq [])) (watch qg__46 F_5)" oops
lemma u___1: "(((((label_eq ''8'') or ((input_eq [] until input_eq []) impl ((state_eq (Some 5) until (((((nxt (output_eq []) aand state_eq None) impl (((((alw (output_eq [] until output_eq [Some LX5]))) suntil output_eq []) aand ((label_eq ''89'' aand (input_eq [] impl label_eq ''{('')) suntil (state_eq (Some 67))))))) impl (input_eq [Str ''@q'',Num 31] suntil (input_eq [Str ''a8<1'', Str M__E,Num 595, (Num E_71),Str zWY] impl ((state_eq None) until (state_eq None or (((label_eq D_____x) aand (input_eq [Num v__4] aand label_eq S__t)))))))))) until ((state_eq None suntil state_eq None) suntil label_eq ''sBS''))))) until (((((state_eq (Some 13) aand state_eq (Some 80)) suntil (state_eq None aand label_eq ''#''))) aand (alw (output_eq [] suntil (state_eq None impl (((state_eq None suntil (((input_eq [] impl input_eq []) until label_eq ''`d'') impl label_eq CG3)) suntil (output_eq [] until label_eq w_w))))) or ((((label_eq ''3'' impl (input_eq [Num 3, (((Num m__co)))] impl (state_eq (Some 6) impl ev (((state_eq (Some 001) impl (state_eq (Some 3) impl (ev ((input_eq [(((Str Q_8))), (Num VR6),(Str ''4F'')] aand output_eq []) until input_eq [Num 0,Str ''_''])))) impl (input_eq [((Str ''@'')),(((Str i28))), Str m_c, Num 1])))))) aand (label_eq n8F_H9)) aand (state_eq None)))))))) (watch vN__j_hm f_3v)" oops
lemma T_0: "output_eq [] (watch D4_5 P7N)" oops
lemma d_o: "(state_eq (Some 0)) (watch QP6 IpG)" oops
lemma b___7: "ev (((nxt (input_eq []) aand ((((output_eq [Some (Num 7),Some S_2,Some x12] aand (label_eq D_87)) aand (((input_eq [(Str '':'')] impl ((input_eq [] or ((input_eq [Num k_3k, Str S_4,Num 8,(Num 92)]) suntil label_eq ''OJh'')) or input_eq [])) aand (input_eq [Num R48] aand label_eq '',4?''))))) aand (output_eq []))) or (label_eq W_xp suntil input_eq []))) (watch o5__7 J_3)" oops
lemma C__8_q: "state_eq None (watch Z__1 AR3f)" oops
lemma Y198: "(input_eq [Num 08443958, Num F_3] or label_eq ''s4'') (watch a_Ls w__7)" oops
lemma W_____4: "state_eq None (watch Z_F mzs)" oops
lemma vR_52: "(alw (((output_eq [] impl output_eq [(Some (Num 8)),Some d54,Some (Num 839),(Some (Num H2t)), Some (Str ''<:%''), Some U03,(None), (Some (Num 04))]) suntil state_eq None) aand label_eq P_G439) aand label_eq D___4) (watch s4D Wn_I7i)" oops
lemma G_O: "input_eq [] (watch C8f B_39)" oops
lemma Om__5: "label_eq U_f (watch La6 m_A__4_4)" oops
lemma q_k: "output_eq [] (watch c_6 H17X)" oops
lemma G_3_3: "(((label_eq HJ_4 impl (input_eq [])) aand (label_eq ''M5:2_'' impl state_eq (Some 3)))) (watch RL4K X_U)" oops
lemma M_1_6: "state_eq (Some 9) (watch l__3 zM_w)" oops
lemma d_i: "input_eq [((Str ''`'')),(((Num 7))),Num Q14,Num i_9,((((((Num 03)))))),Num s7_4y] (watch R___Y B__6_R)" oops
lemma r08e: "(state_eq None aand (((input_eq []) impl ((input_eq [] impl label_eq ''8'') impl state_eq None)))) (watch s600 r0E)" oops
lemma B_x: "(label_eq h3_T) (watch o42 JCR)" oops
lemma P_7: "label_eq AEG (watch V_o j__0)" oops
lemma z28S: "((input_eq [(Num 236),Str ''.'', ((Num u4_i))] until state_eq (Some 33)) suntil state_eq (Some 3)) (watch f9_8 O19k)" oops
lemma p_m: "label_eq c1_s (watch k_P6 w___H)" oops
lemma v___56: "((input_eq [] impl (label_eq R_Ay or state_eq (Some 9))) or label_eq ''1'') (watch i3K_l7 U_3)" oops
lemma f2_V4: "(nxt (state_eq (Some 708) until input_eq []) suntil input_eq []) (watch z82e G__4)" oops
lemma d_0: "(input_eq [] until output_eq [None, (Some Q6_8)]) (watch zZ_6 x__9)" oops
lemma k__1_VG: "(state_eq (Some 0)) (watch e752 Q3Y)" oops
lemma R__19j: "(((output_eq [None]) aand ((label_eq ''-'') until input_eq [Num X5c__332, Str lh_1,Str L0__0, (((Str y3W)))]))) (watch F_i o98)" oops
lemma U57___6: "output_eq [Some (Num v_7),Some N__T,((Some (Str ''<G$`'')))] (watch M8q j___b)" oops
lemma N_5: "input_eq [] (watch q76 F_8)" oops
lemma qi4: "label_eq w_3_7C (watch Nn_5C_0 M_5)" oops
lemma n__8_F: "input_eq [((((((Str ''Q a9''))))))] (watch i_Q b____O7)" oops
lemma r62: "(input_eq [Str ''3/(1;&'',Str W_T9, Str se__B, ((Str ''(*7^'')),Num V__63,((((Num o_4))))] until (output_eq [None] aand output_eq [])) (watch f2qk f_o)" oops
lemma z0b: "output_eq [] (watch Uac w__w4)" oops
lemma v5x: "label_eq j__3E (watch s0_5 Gr___2)" oops
lemma z_S: "(((((label_eq '') r*%{/'') suntil (label_eq ''!''))) impl (label_eq I_67 impl (state_eq None until label_eq r_t__m)))) (watch D9___44 y_4_2)" oops
lemma a_I: "input_eq [(Num 92)] (watch T32G R_8GW)" oops
lemma N4_3: "(output_eq [] aand state_eq (Some 941)) (watch Ylk J4e)" oops
lemma c_V: "((input_eq []) suntil input_eq []) (watch n5__1 i1_4)" oops
lemma w_1r: "state_eq None (watch e834 a_Q)" oops
lemma RUZ_p: "(output_eq []) (watch T_6 N_z)" oops
lemma Y__b: "ev (state_eq (Some 626) aand label_eq Nr_01) (watch ao___1 N_15e)" oops
lemma E5dA: "(((output_eq [((Some h_h)), Some U2S,Some te__3, Some L_N, (None), Some (Str Rp_6)] until (not (state_eq None) aand (((((output_eq [] impl output_eq []) impl ((((input_eq [((((Num nq__6_4_C))))] suntil ((((state_eq (Some 12)) until (not (label_eq N3_s until ev (((((((((input_eq [] aand label_eq H1486____83) suntil (((((label_eq C8_r suntil ((input_eq [(((Num x__C))), Str Z7___s, Str ''51?'', (((Num 7)))]) suntil ((state_eq (Some 3) until alw (((((output_eq [None]) suntil (label_eq zAl))) until label_eq C_Y) or nxt (output_eq [None] impl (state_eq (Some 09))))) suntil alw (output_eq [])))) aand output_eq [(Some (Num 8)),None]) suntil input_eq [((((((Str Q_h)))))),Num 23,((Num k___Q)), Str l_4]) impl output_eq [Some (Str ''/:''),(Some (Num f_4_62)),(None)]) impl output_eq []))) suntil (state_eq (Some 3)))) until (((nxt (state_eq None) until output_eq [Some (Str Q1_45), None, Some (Str ''!'')]) impl ((((nxt (input_eq [] suntil input_eq [(Num r82)]) suntil (input_eq [] suntil (input_eq [(Num 71)]))) until (state_eq None or (((input_eq [Str ''N+9S'',(Str J_3)] or (output_eq [(Some b_8), (Some N__66),(None),((None)),None, (((None))), (None)])) aand state_eq None) until label_eq ''}''))) aand label_eq ''}'') impl ((label_eq M44) aand label_eq ''7H='')))))) aand (label_eq y_a)))) until (output_eq [] suntil state_eq None)))) suntil state_eq (Some 2050))) until input_eq [(Num p_H)]) until (((((((output_eq [Some (Num 3)] aand (label_eq ''}''))) suntil (state_eq (Some 88)))) until nxt (((label_eq ''689^>'' or (((((output_eq []) or ((output_eq []) aand input_eq []))) or (output_eq [] impl label_eq ''/'')))) impl (output_eq [Some (Str ''^9`aO>P'')] or output_eq [])) or label_eq o1l)) impl (((input_eq [] or (((state_eq (Some 6) suntil state_eq None) until state_eq None) or state_eq (Some 2))) aand (label_eq ''|)#''))))))))) suntil (input_eq [Num 8,((Str ''I'')), (Str C_3)] impl (output_eq [Some l__86, Some (Num d__mC)])))))) suntil ((state_eq (Some 7) until (((state_eq None) suntil (output_eq [(Some (Num dJG)),None,Some (Str z9rG)])))) impl state_eq None))) (watch zJ4T r3j)" oops
lemma C_n: "((output_eq [None]) suntil input_eq [(Num K44)]) (watch O__D L_8)" oops
lemma N_8: "((((input_eq [Num 56,(Str ''f_0'')] suntil (input_eq [((((Num l__yv)))),((Str f__54)),Str svh___Z] impl (label_eq ''O~'' or input_eq []))) or (((((nxt (output_eq []) impl ((((label_eq ''%'') aand ((((input_eq [Str V_3, (((((Num K_a)))))] until ((((((input_eq [Str A__D, (Str ''$'')]) or output_eq [None, (Some (Str ''L'')),((Some (Str ''q''))), (Some (Num 3918)), None, ((Some a_0p)),Some (Num 4)]) impl label_eq RZ_1c_yF) or (input_eq [Str '':Y{''] or (label_eq J_8 or (label_eq ''7>|-$=''))))) impl output_eq [])) aand label_eq h_73) suntil ((((((((label_eq j_x or (state_eq None suntil (nxt ((((state_eq None) or output_eq [Some P_3Ez,(None)]) suntil (state_eq (Some 6) or output_eq [Some Z0_C]))) impl label_eq a6_d))) suntil output_eq [None, None, None, Some (Num B_4_X__3),Some vk_9]) suntil output_eq [None]) suntil (state_eq None))) suntil label_eq '';9U.2'') aand (((((output_eq [] aand label_eq ''(,'') aand (label_eq ''!'' suntil input_eq []))) suntil (((state_eq None impl state_eq None) suntil label_eq ''v/'') aand (label_eq uf_E4)))))))))) or state_eq (Some 912265))) until (((((label_eq ''Id'') aand (output_eq []))) impl (label_eq ''fI'' impl ((input_eq [(Str ''3=''),Num 4,(((Str ''+'')))] suntil state_eq (Some 01)) until output_eq [])))))) until (label_eq ''*'' until alw ((label_eq ''p~'' suntil ((((((((((((((input_eq []) or (((output_eq [Some (Num 7),None,None,None,Some (Num 00)] suntil (not (((state_eq (Some 7050) suntil output_eq []) or (not (input_eq [] aand label_eq Qw_1) suntil state_eq (Some 04)))))) impl input_eq []) impl output_eq []))) impl (((((input_eq [Str '')'', ((((Str f_3)))),(Str a_u),Str ''1'']) until label_eq v_rs_8) or state_eq None) suntil (state_eq None until (((((((((((not (input_eq []) or output_eq [None]) suntil (state_eq None suntil label_eq fBF))) or alw (label_eq wo4 or label_eq u_1)) or input_eq []) suntil (input_eq []))) suntil (output_eq [None] impl state_eq (Some 13)))) or (((input_eq []) suntil (((output_eq [] aand (output_eq [] or (output_eq []))) impl label_eq q3p4) impl state_eq None)))))))))) impl ((input_eq [Num 735] until (label_eq ''<$'')) or ((((output_eq [Some g2w,Some (Num GAW), Some e__k]) aand (label_eq KiCs aand ((state_eq None aand not ((input_eq [Str ''O''] until input_eq []) or (output_eq [] suntil label_eq ''f''))) impl state_eq (Some 9))))) until output_eq [None,Some tjU2,(Some U_J_0), Some (Num K7F)])))) aand output_eq []) until not (output_eq [])) or (((input_eq [((((((Str o_1)))))),Num Z_D,(((((Str b__7_7)))))] impl nxt (input_eq [])) impl (state_eq None impl nxt (output_eq [Some Ga_0, (Some (Str ''p''))])))))) or state_eq (Some 84)) suntil (((output_eq [] until output_eq []) or (label_eq u1__r2)))))) aand state_eq (Some 51))))))) aand (((label_eq i_C until (state_eq None))) or (input_eq [(Num 4)]))) (watch E__6 h_85)" oops
lemma h9vP: "(state_eq None) (watch Z___xh rkj8)" oops
lemma yA_7d: "((((((label_eq u_4 until alw (output_eq [])) aand (label_eq ''-'' suntil (alw (((((input_eq [] aand output_eq [Some (Num p_4), Some v32, Some yd9]) suntil input_eq []) suntil ((output_eq [] impl (output_eq [(None)])) suntil (nxt (((((label_eq l0__K impl label_eq ''G'') impl (state_eq None suntil (((output_eq [Some a39, None] until label_eq ''>p'') aand (output_eq [Some (Str r9N2)] suntil (output_eq []))))))) until (((state_eq None impl ((((((state_eq (Some 0) impl (((((output_eq [] or (state_eq None aand state_eq None)) impl (label_eq ''{9'' impl (label_eq e__g until input_eq [(Str '')''),Str ''1'',(Str ''}2#$$i'')])))) impl (label_eq ''#'' suntil output_eq [])))) impl ((((output_eq [] aand (((label_eq ''0'' or (input_eq [Num 558] until (state_eq (Some 77) suntil state_eq (Some 76)))) suntil state_eq (Some 0)) suntil ((alw ((((output_eq [((Some (Str e4_c))),Some P_2,Some m_Q,(Some (Str Iw4fO4))] aand (((((((((state_eq (Some 563)) aand (output_eq [None, Some (Str h31),Some s__o, Some (Num 1993), Some M_mG, Some (Str ''z$''), None,(Some (Num T4r))] suntil (((input_eq [Num 5] until (label_eq '')'')) or (output_eq [] suntil (label_eq ''>s''))))))) aand state_eq None) impl input_eq [Num 77,((Str ''_|5'')), Str t_3,(((Str ''^''))), Str Q_C]) impl input_eq []) impl state_eq (Some 160)) until (output_eq [] suntil (state_eq None until input_eq []))))) aand output_eq [None, (None)]) suntil (state_eq (Some 0) impl (output_eq [None, Some (Str ''0J'')])))) until input_eq [Str ''0'', Str Qs_2, Str j__82]) impl (output_eq [(Some (Num R_T7)),(Some jSc)] aand (((input_eq [] suntil (not ((input_eq []) or state_eq None))) suntil (((label_eq x_r) or (input_eq [Str Q_1_Q]))))))))) aand input_eq []) until (state_eq (Some 8)))))) suntil (label_eq i252E))) suntil output_eq [Some (Num W_3),None])) impl ((label_eq '','') until ((state_eq (Some 5243603)) until label_eq '':1Ea!N-#'')))))) impl (((((output_eq [] suntil (((((state_eq (Some 25) suntil (((((input_eq [(Num r__3)])) suntil label_eq u_4) until ((((alw (input_eq [] until input_eq []) suntil state_eq None) or (state_eq (Some 7) suntil ((input_eq [Num hL_y,Str ''@|9~'', Str ''4.'', ((Str ''.9?''))] impl (label_eq k_7)) impl input_eq [(Num 3519105)])))) suntil output_eq [])))) until (output_eq [None,None] until output_eq [None, None, (Some OTn1)]))) suntil ((((label_eq ''t^'') suntil output_eq []) until (input_eq [])))))) suntil (nxt (((output_eq [Some (Num R_9),Some (Num 81), (Some i_Y)])) impl input_eq []) impl (label_eq f35 aand output_eq [])))) aand ((((((label_eq ''!'') suntil (output_eq [])))) or input_eq []) until label_eq d_on_1))))))) or state_eq None)))))) or ((output_eq []) suntil state_eq (Some 514))) aand label_eq Z1I) (watch Xo4 Oq7)" oops
lemma hwR: "(label_eq ''|=-'') (watch SS9_4__D WEQ)" oops
lemma Th1: "label_eq a_0 (watch pA7 w__3)" oops
lemma i_7: "state_eq None (watch t__3 n__6)" oops
lemma pr5: "state_eq None (watch IT35 v_7)" oops
lemma R_u: "((output_eq [])) (watch M_9 vtWKBK)" oops
lemma L_1: "output_eq [] (watch gB_7S a9X)" oops
lemma m_56: "output_eq [] (watch Dbk Gr_u5)" oops
lemma a___d36: "nxt (((label_eq e59))) (watch kP_3 D2w)" oops
lemma eGr3: "(((((input_eq []) suntil (state_eq None impl (((label_eq n_Ayj until (state_eq (Some 6970813) aand nxt (label_eq q9_2 until (output_eq [])))) until (input_eq [] or state_eq (Some 72))))))) aand (output_eq []))) (watch F_P s__5h_0)" oops
lemma J_m: "label_eq ''^'' (watch J_4 z__m)" oops
lemma R_3: "input_eq [Str ''K'', Str ''H{1'', Num d_6] (watch z72 S_2EZ)" oops
lemma ccT: "label_eq ''J'' (watch h7y_P D_0)" oops
lemma uMDp4: "(output_eq [None, (None), None] until state_eq (Some 7)) (watch P_O c1Uk)" oops
lemma m__10: "input_eq [Num 841,Num 9,Str ''3>''] (watch T__7 oYu)" oops
lemma N_2: "(label_eq nu559) (watch Ml6 G_1)" oops
lemma J_0v6: "state_eq (Some 4128) (watch a1N v3P)" oops
lemma v7__U: "state_eq (Some 0) (watch K_9 e_G)" oops
lemma XT_5y: "((output_eq [] until output_eq [Some (Num KUJb4), Some Y_459, (Some w_69), Some c2s_B, None]) suntil (output_eq [] or (input_eq [] or (((((ev ((input_eq [(((Num p__5))),(Str ''A''), Num K4B, Str uE_q,Str uQN_X9, Str QBs]) until nxt ((label_eq h____5 until ((((output_eq [None]) aand (((((state_eq None) suntil (((input_eq [] or output_eq []) until (output_eq []))))) or (state_eq (Some 9) aand state_eq (Some 7))) impl (state_eq (Some 1) or (label_eq E5_e impl (((((input_eq [(Str ''6''),(Str q_0), (Str gf__6), ((((Num 8)))), (((Num 2710))), Num J3_j]) impl label_eq ''g'') aand (((input_eq [((Str ''u''))] or output_eq [Some L8w, Some Jr7Q]) or (state_eq None)))) aand (not (label_eq kI86 suntil label_eq u71))))))))) until state_eq None)) suntil input_eq [Num 1999, Num 8,((Str n2__R1)), ((Str h4_hV)), Num 8])) suntil input_eq [Num u_L, ((Num 19)),((Str e868)),(Num 9), Num 34,Str X54, Num 8785,Str c_n, (Num 634)]) suntil (label_eq kG5 or input_eq []))) until output_eq [Some (Num b_N),Some (Num e_4)]))))) (watch ZTn p_N3w)" oops
lemma o8__P: "input_eq [Str ''3'',Num 6, ((Num 49)),(Num 037)] (watch q0Q9_a c_T_5)" oops
lemma p_r: "((input_eq [Str ''$}'', Str r_2, (Num z76)] aand (((state_eq None impl label_eq e__9) impl (((((output_eq [Some F_Z] suntil (output_eq [] suntil (label_eq a8_2p until (input_eq [] aand (((((((input_eq [Num v_6_42,Str gA_v] suntil label_eq q__X) aand (((input_eq [] impl output_eq []) or ((state_eq None) suntil input_eq []))))) suntil (not (((((state_eq None suntil (output_eq [] until (state_eq (Some 3437) until input_eq []))) or ((input_eq [((Str ''x*'')),((Num 420))]) impl state_eq (Some 11351)))) suntil (label_eq ''m''))) aand (state_eq None)))) aand (output_eq [Some fXF,(Some RCS),Some YN_8,None,Some l_bl_4]))))))) until (input_eq [] aand state_eq (Some 45)))) impl (((output_eq [] until (input_eq [Num pDM5,Num 3,(Num V4__sn__t), (Str U_79)])) suntil ((output_eq [] impl output_eq []) aand output_eq [])))) aand state_eq (Some 719))))) or input_eq []) (watch e__5 Y_2K_RG5)" oops
lemma x9___2_1: "(alw (state_eq (Some 8) suntil (label_eq S_K aand input_eq [Str ''.'']))) (watch l__h c_1D)" oops
lemma n40: "(label_eq ''+5 ='') (watch f_2 m__7)" oops
lemma V_L0: "input_eq [(Str u1yP),(Num 0)] (watch M04Q D2c)" oops
lemma X__r: "(((output_eq [Some (Num 38)] or (label_eq p_5xz)) until ((input_eq [] suntil output_eq [Some (Num b_1), (Some (Num 74))]) impl label_eq t__BZJ))) (watch aq__8x P_8Y)" oops
lemma s8H0: "nxt (label_eq y__k suntil output_eq [(Some od__s),None, Some a___o,None]) (watch T0u K__M)" oops
lemma K0_DN2_2: "((label_eq ''Gf'' until (((input_eq [Str j29,(Num zJ__7),(Str OX7),((Str NF7)), Num d8R__p] suntil state_eq (Some 34)) suntil state_eq None) or label_eq ''D'')) impl state_eq (Some 5)) (watch j_8 BMz)" oops
lemma F__P: "(((alw (label_eq BLB_n impl (state_eq None until input_eq [(Num r_f)]))) until (((output_eq [] suntil state_eq (Some 85)) suntil (output_eq [] suntil state_eq None)) until output_eq []))) (watch xw____2 X2g)" oops
lemma z__j: "output_eq [] (watch a_0 S_i)" oops
lemma e_qm: "input_eq [] (watch R___K w_H)" oops
lemma P__A__9M: "(state_eq None impl (input_eq [((Str ''pQ&'')), ((Num r70)),((Num 1)), ((Str b5_N)),Num 642] suntil (input_eq [((Str N_B))]))) (watch hy3k B_e)" oops
lemma P__1: "state_eq None (watch t_0 S___3)" oops
lemma m__6: "output_eq [] (watch l790 M_33LV)" oops
lemma i7z: "(input_eq [Num E89]) (watch Q17 Kaso)" oops
lemma E_5: "output_eq [] (watch x_6 GA640_p)" oops
lemma K__U: "(label_eq Y_23_z_9__8 impl state_eq None) (watch VP_3U R_04)" oops
lemma Tt_w: "output_eq [(None),Some K_0,((Some (Num 2))),Some lLn] (watch c_13 O_2R)" oops
lemma a0N: "(label_eq p_Z until state_eq None) (watch A_N B_K)" oops
lemma s53: "label_eq iyr (watch k_v dsD)" oops
lemma j_728: "state_eq (Some 5) (watch no03_C QiB)" oops
lemma TNl: "output_eq [] (watch b_1 O_5)" oops
lemma P_2: "((((state_eq None or output_eq []) or label_eq ''B'') or ((((output_eq [Some l_5I,(Some N_4), (Some (Num j11)),Some (Str '':'')] suntil ((((not ((state_eq (Some 9)) or alw (output_eq [Some (Num S__r9)] or input_eq []))) suntil output_eq [Some L__8]) suntil ((label_eq q_6i_0) or input_eq [(((Num 77))), Num V__6A])))) aand label_eq N_8) aand label_eq O1j) until output_eq []))) (watch e_l M2X8)" oops
lemma f_5: "(((input_eq [(Num 9),Num 69009] or ((output_eq [] or (state_eq (Some 225) or (((((output_eq [Some (Str I__3),Some jm_D,Some (Num 7)] aand ((((label_eq A__4kj or state_eq (Some 48)) or (input_eq [Num Z_w, Str ''!''] or state_eq (Some 3)))) until output_eq [])) impl (state_eq None impl output_eq [Some (Num 700),Some zrb]))) aand (state_eq None until state_eq None))))) impl label_eq ''++'')) or ((label_eq ''4'') impl label_eq xK68))) (watch d__O0 q__0)" oops
lemma c__a: "output_eq [Some (Str ''s''), (None),(None)] (watch Vs_C V17)" oops
lemma r__z1: "((((output_eq []) until (output_eq [None, (((None)))] suntil (label_eq ''Q>:1C''))) or (((((state_eq (Some 0) aand input_eq []) aand (input_eq [Str d93, Str ''?'', (Num 34),Str x_V] suntil output_eq [None, None]))) until ((label_eq ''3e2^+'') suntil input_eq []))))) (watch UPt p_5)" oops
lemma lf6_6: "(((input_eq [(Str Y____j_I),(Num g1U)] until input_eq [Str Lc8, Num g_5, Num 02, Str FE_m_E, ((Str Y5_0_______15e))]) or (state_eq None until state_eq None))) (watch G_s w5s)" oops
lemma M__z: "label_eq ''2'' (watch q_6 oO__U)" oops
lemma H_2: "label_eq b__0 (watch f1_x2B IK_V6)" oops
lemma j__0: "state_eq None (watch GB1 H_z5)" oops
lemma DLQ: "output_eq [] (watch e___W k__T)" oops
lemma X_PY7: "(((label_eq ''tRbw'' aand input_eq []) suntil state_eq None) until (input_eq [])) (watch G_h Kl_A)" oops
lemma Do1: "output_eq [] (watch N7__l8 s36)" oops
lemma E_U: "(label_eq g1UF until output_eq [None]) (watch Ql_2 N_I)" oops
lemma r0n0_F: "state_eq None (watch pJ6 J_6)" oops
lemma Q__e: "state_eq None (watch F63_e___0 hhSC)" oops
lemma a_bn: "label_eq ''_6Xq$'' (watch Fy_JH_d Le6)" oops
lemma jNN: "((label_eq WwO aand (output_eq [Some (Num 324448), Some (Str ''^''),None, (Some (Num n_5)), Some (Str H__E1),Some R69] or input_eq [])) suntil input_eq [Str '',&d'',Num 874,(Str h5_OnN)]) (watch A8_2 V_57)" oops
lemma U_wqz8: "(state_eq None or label_eq ''|'') (watch Z93X2 Z1C)" oops
lemma VW9: "(input_eq [] or input_eq []) (watch ho3 A___F)" oops
lemma q___K_2fw: "((input_eq []) aand state_eq None) (watch y__G y_a_mO)" oops
lemma R_tgD: "((input_eq [Str i_L] until ((output_eq [(Some (Num B27__u)),None, Some (Str Z88),None,Some (Str ''f^'')]) or state_eq (Some 8183))) or (state_eq None)) (watch I_9 W9X)" oops
lemma f_0: "state_eq (Some 4) (watch Jw7 qd3)" oops
lemma F_0k: "output_eq [Some mNd,Some (Str G_XJ)] (watch F7_40 Jv7)" oops
lemma B5_3: "not (state_eq None) (watch ei_JS b89)" oops
lemma E4_U: "ev ((label_eq N__g5) or state_eq (Some 6383)) (watch W_h a_j)" oops
lemma B_2: "(output_eq [None, None, None,Some (Str ''5>''), None,Some JV4, Some E_c6,Some (Num S119)] aand (label_eq '';n$?356'' suntil input_eq [Num 84])) (watch K0_Y8_l t_u)" oops
lemma o_2: "output_eq [Some D__r2, (((None))),Some m_A,Some (Num ly_R), Some h_X, None, Some B__K0_8, None, Some PW57___dI] (watch Y7_3 G_3)" oops
lemma hi_B: "input_eq [] (watch Yi3 k6_x)" oops
lemma N_1: "state_eq None (watch s__C S9_2)" oops
lemma H_6: "(state_eq None) (watch nYlu_2 B_8)" oops
lemma H49c: "(input_eq [] or output_eq [(Some (Num 1))]) (watch JfG88 L__S)" oops
lemma U_F1: "(input_eq [(Num HoGy),Str X_2B7, Num b7__j] until (((input_eq [] suntil ((state_eq (Some 638) impl (input_eq [Str ''C''])) suntil output_eq [Some (Str s_p), Some Qu2N,(Some s_g_Y),Some R___ktF,Some (Str ''e1''),None])) aand (output_eq [None])))) (watch G_67X1 aa_t)" oops
lemma T_B_3: "not (((((((state_eq None) until (nxt (((input_eq [] until (state_eq None impl ((state_eq None) or not (state_eq None)))) until output_eq [Some SHM, Some (Str ''0z6s%@'')]) aand state_eq None) suntil (ev (input_eq [] or output_eq []) until label_eq x__Ph)))) impl state_eq None) aand (((((((input_eq []) suntil label_eq ''_@'') suntil (((output_eq []) suntil (((((label_eq CK5) suntil (((output_eq []) impl (input_eq [(Num 3),Num QwW0,(((Num U__1))),(Str Z_4), Str V_3, (Str I_3), Str W_______C9, ((((Num 3)))),Num 911, Str d__5] or (state_eq (Some 9))))))) suntil (output_eq [(None)] suntil (((output_eq [Some (Str ''0D''),Some J_E]) aand (input_eq [] impl state_eq None)))))))))) aand output_eq [None]) impl label_eq o26p69) until label_eq ''S'')) aand (input_eq [(((Str R__6_V_4J)))] suntil input_eq []))) (watch H_j_5 y1576)" oops
lemma m__Q5: "output_eq [] (watch e_y n_3)" oops
lemma oL43: "label_eq D_5 (watch AXK Vp9)" oops
lemma z_F: "input_eq [Str ''0'', (Str ''5T'')] (watch kNXT D4m)" oops
lemma E_0: "(label_eq ''/6'') (watch cJD_J L_3)" oops
lemma l_6: "((label_eq S37) suntil state_eq (Some 2)) (watch Wu9 hS_D)" oops
lemma LY_s: "output_eq [] (watch Q_3V H__0)" oops
lemma F36: "(state_eq (Some 71075)) (watch p1N P_bf3)" oops
lemma h_6: "state_eq (Some 00) (watch C_t_h F_94)" oops
lemma w4_L: "input_eq [Num x__40_R, Str ''<19''] (watch Y_P G0_3)" oops
lemma UiE: "(state_eq None suntil input_eq []) (watch x2a GM6_C)" oops
lemma aBW_3: "input_eq [Num w_5] (watch Y1__M G_C)" oops
lemma x_1: "input_eq [Str ''~S5''] (watch s_5 SA2)" oops
lemma yr__2: "state_eq None (watch zju E__f8)" oops
lemma Y__8: "label_eq G_c (watch h_u I_7__9)" oops
lemma T_3: "input_eq [] (watch so__9 h___3_6)" oops
lemma T0bD: "output_eq [] (watch Y_o0 z4x2)" oops
lemma E_p: "not (output_eq []) (watch Q_5 S_9e)" oops
lemma M_w: "state_eq (Some 66) (watch U_e5 Y83S)" oops
lemma i_W_j: "state_eq None (watch Q1x gHH_9)" oops
lemma R_no: "state_eq None (watch D0_P a_vK4)" oops
lemma U8w: "(state_eq None) (watch T_d fu1V9)" oops
lemma ct_L: "(output_eq [None,Some u_1] impl label_eq ''7'') (watch yy4 tx2)" oops
lemma x_9: "(label_eq hSR_7 impl (((input_eq []) aand (state_eq (Some 404) suntil (output_eq [] until nxt (state_eq (Some 5))))))) (watch fv__c w_38)" oops
lemma jq2: "(label_eq u_7n suntil (input_eq [(Num 8),(Num Z_7),Num G_2, Num 4733, ((((Num 6))))] until (output_eq [Some (Num 5)] suntil state_eq None))) (watch f52 W3q___6)" oops
lemma s72V: "input_eq [] (watch x____5 o_I)" oops
lemma U_6O: "(output_eq [Some (Num 6), ((Some Q07))] suntil ((((state_eq None impl label_eq Ns554) impl (input_eq [(Str ''w+''),Num P_h,(Str ''5''),(Str C8_2m), Num cG2]))) or alw ((state_eq (Some 0) impl ((state_eq None impl state_eq (Some 2)) until (output_eq [(None),((Some (Str ''3''))),Some d_r, (None)]))) until output_eq [None,Some u0C, Some (Num M01),Some D_0_s, None, Some O_1,(((Some (Str Q_S))))]))) (watch Lh9 wgvB9)" oops
lemma pi0: "(input_eq [] or (input_eq [] impl (state_eq (Some 5)))) (watch R_7 Tv5)" oops
lemma x52: "(label_eq ''D@*'' impl (state_eq None or (alw (state_eq (Some 1) until ((((alw (nxt (state_eq None))) or nxt (((((label_eq B_y aand (output_eq [])) aand ((((((input_eq [(Num N_6HY3z)]) until state_eq None) until state_eq (Some 5)) or (((input_eq [Str ''&'']) impl (state_eq (Some 0) or ((((input_eq [])) or (input_eq [] or (input_eq []))))))))) until ((output_eq [Some S_0, Some e_9]) suntil label_eq '';27'')))) impl (((((((output_eq []) impl ((((((not ((output_eq [(None), None] until (input_eq [Num 8] impl ((output_eq [] impl (((input_eq [] suntil state_eq (Some 7)) impl (input_eq [Str ''{0''])))) suntil input_eq [Str BSm7X, Str B_6,Str u_y_p]))) until input_eq [(Num U___Lr), ((Num v__8)),Num 22, (Str k_4_2),(Num s5_8), (((Str K_E))), (Str ''z''),(Num V_6)])) impl state_eq None) or input_eq [(Str X_j), ((Str xc_o)),Str k1A, Num 27, (Str '')0'')]) impl (state_eq None impl (((output_eq [None]) or ((((ev (input_eq [] aand output_eq [Some O_Q,Some P__4__Y3,Some (Str ''0''), Some (Num m_65)])) or output_eq [(Some (Str ''$'')),None, Some Li_5]) suntil ((state_eq None) suntil input_eq [])))))))) or (ev (((((((input_eq []) or (input_eq [] until nxt (output_eq [Some F_5,Some (Num O_p),Some (Str ''$7)''),Some (Num 4), Some O_l, None] impl (input_eq [Num A_8,((((Num z31)))), Num F__m, (Str ''5'')]))))) or ((label_eq ''p61'' or input_eq []) aand label_eq ''H''))) aand (state_eq (Some 550)))))))) aand (input_eq [((Num N__2)), (((((Num 0))))),Str E_L,(Str ''.W<F'')]))) impl (input_eq [] suntil input_eq [((((Str r_3)))), Num NS3, Str wZdC, ((Str ''5'')), ((((Str t_l))))])))))) suntil (state_eq (Some 8) suntil input_eq []))))))) (watch D4__4 NMw)" oops
lemma TL_p: "label_eq T__k39N (watch B_n b_L)" oops
lemma P92: "label_eq ''4$Q'' (watch fCT_4 x89)" oops
lemma v917: "label_eq ''/'' (watch n__4 ORi)" oops
lemma p4y___B4: "output_eq [] (watch U_8_7 T_1)" oops
lemma oOn: "input_eq [Str AtW,((Num C1p))] (watch U_TD n_B)" oops
lemma d__Vu: "(label_eq pq__5 until ((((label_eq a_v) aand label_eq J508) until output_eq [Some (Num 71)]))) (watch y5p D_j)" oops
lemma z_N: "(((label_eq ''R'') or (ev (input_eq [Num ww2,Str ''N'', Num 5,(Num 6),Num 18,(Num 6),Str ''qT/'',(Str e03)] or ((output_eq [None, Some eP_i5, Some (Num 15)] suntil ev (label_eq Lc____z)) until input_eq []))))) (watch r__a O__2)" oops
lemma OK_9: "(alw (((((output_eq []) or state_eq None) or input_eq [((Num J_p_s)), (Str ZT3), Num 97]) or (((input_eq [Str ''~'',((Num s3Q)), (Str M_8R),((Num 7)), Num 4] impl output_eq [Some x__r, None]) impl state_eq None) until label_eq q72A)))) (watch vn_c R_9)" oops
lemma Hl86w: "output_eq [] (watch w_y G_C)" oops
lemma q_3N: "(input_eq []) (watch F7m F_1)" oops
lemma o_mN: "((((input_eq [] until label_eq ''4'')) or (((((((((label_eq T6__U57 until state_eq (Some 47777)) until output_eq []) until (((label_eq ''l'' or label_eq kQ03) aand output_eq [Some (Num 0377)]) or state_eq (Some 8)))) until ((input_eq []) until input_eq []))) aand (output_eq [] suntil label_eq ''){''))) suntil (((label_eq ''!697'') or (label_eq e_s impl (output_eq [(Some tI7), ((Some F6gA_x9)), Some (Num 67),Some C_8, Some (Num 3)] aand alw (label_eq cq6 aand (label_eq ''w'' impl (state_eq None aand (((((((((output_eq [Some (Str bsy),Some (Num b5l), (None),Some (Str ''|'')] until input_eq [((Str T__u)), Num pwzG, (((((((((Str x6_c)))))))))])) impl (label_eq t_y))) or (label_eq ''#'' suntil output_eq []))) suntil (state_eq None impl state_eq (Some 04)))) suntil output_eq [None]))))))))))) (watch q____c z_3)" oops
lemma u_t: "label_eq S_e6 (watch E_l tc0)" oops
lemma w82: "input_eq [((Str sa__F0)),(Str ''|''),((((((((Str ''#(0+'')))))))), ((((((Num 22))))))] (watch o_t vdK)" oops
lemma n11: "(((output_eq [] impl (state_eq (Some 264272) or (input_eq [] impl (((((output_eq [] aand (input_eq [(Str ''&''),(Num jNV), (Num AtX_0_GQ), Num j1D,Num i_V])) aand ((((((input_eq [] until ((label_eq ''z'') impl input_eq [Str E___L, ((Str ''`''))])) or output_eq [(Some (Str z4G)), None]) or ((input_eq [(Str rszt2), Num Z_3, Str d_N, (Str i6z_X4),((Num f6H))] or state_eq None) or ((input_eq []) aand label_eq w_93)))) aand (not ((state_eq (Some 85) or label_eq wda_8) until label_eq C_4) suntil input_eq [((((Num 880))))]))))) or (output_eq [] impl output_eq [Some k_0,Some (Str Q_R),None, Some (Num t_k),(None), Some (Num N_60), Some F_D])))))) aand label_eq ''%'') until state_eq (Some 9)) (watch PT71 h_4__6)" oops
lemma h_9_8U9: "label_eq ''N?'' (watch a5e LBy)" oops
lemma aXf: "label_eq g3__8 (watch f_8 T_L)" oops
lemma F_f: "(input_eq [(((((Num 343))))),Str ''b${+'',((Str hq5))] aand input_eq []) (watch d_z e0c)" oops
lemma k_r: "(state_eq None or ((label_eq '')Z'' or (state_eq (Some 1) suntil (label_eq ''?''))) aand state_eq None)) (watch v_8 A9_J)" oops
lemma n__a: "(label_eq xx0) (watch H__L P_UG)" oops
lemma M44: "((nxt (state_eq (Some 74288))) impl state_eq (Some 542)) (watch j1v__16 G_8)" oops
lemma xT8: "(label_eq ''Q&7'' or state_eq None) (watch b_6 i_3u)" oops
lemma d_2: "(state_eq (Some 879)) (watch r_7 wF59)" oops
lemma y9_5: "(state_eq None impl (((((input_eq [] aand (((((label_eq n_1_GJ) suntil (label_eq ''-%''))) impl (label_eq ''-'')))) impl input_eq []) impl input_eq []) aand (input_eq [Str ''Duc+'',Str ''=''] or alw (((state_eq None aand (input_eq [] suntil (output_eq [] until ((state_eq (Some 334) aand ((input_eq [Num n72, (Str ''9%_''), ((Str L_M)), ((Str h_P)),((Str T780)),((Str p_K__0__X))]) impl state_eq None)) impl nxt (input_eq [] aand label_eq Yv___R))))) suntil (output_eq [Some (Num 092), Some I06_3,None,(Some k_2)] until (((((output_eq [] impl label_eq ''>*7'') or (((output_eq [] impl ((((state_eq (Some 14) suntil (((state_eq (Some 2) impl state_eq (Some 162)) or (((state_eq None) suntil (label_eq t_v or (input_eq [Str U8_5b] aand output_eq [(None)]))))))) aand (state_eq None impl (alw (input_eq [Num 3] suntil (((((ev (output_eq [])) suntil output_eq []) or output_eq [None, (None)]) aand output_eq []))) aand input_eq [Num 23, ((Str ''9'')), Str ''$%2y'', ((Num hfW8))])))))) or ((((((state_eq None suntil ((input_eq []) impl output_eq [])) until (state_eq (Some 10) suntil ((nxt ((not ((((label_eq '';-'' or input_eq [Str ''7'',(Str d_53),(Num 1)]) impl ((((state_eq (Some 1) suntil (((((state_eq None) until not (label_eq ''(3'' impl (input_eq [Str ''{'', ((((Str X_Cb)))),Str ''>'', Num 4] suntil (state_eq None impl (state_eq (Some 0) suntil ev (((state_eq None) suntil input_eq [Str ZQW,((Str ''.V6_'')),Str ''|Y0y'',(Num po4), ((Str Y89))]) suntil label_eq ''TK'')))))) or output_eq [Some (Str aM___h)]) suntil (((state_eq None impl state_eq None) impl label_eq ''d#}'') impl output_eq [])))) impl input_eq [(Num 8)]) or (input_eq [Str Dk3,Str I99, (Num 4)]))))) aand ((output_eq [Some (Str ''7-8(;'')]) until ev ((((output_eq [((None)),Some L_9_z_7] until state_eq None) aand (((((input_eq [] suntil ((((state_eq None) or label_eq ''9'') aand output_eq []) impl state_eq None))) suntil (((label_eq Q_u_5 impl (state_eq (Some 00))) aand (output_eq [])))))))) suntil state_eq None)))) until output_eq []) until state_eq None))))) or (((((((input_eq [(((Num o_E))),((Str ''^8''))] impl ((((input_eq [Str J1_2] impl output_eq [None]) suntil (label_eq ''498''))) until alw (output_eq []))) or (label_eq ''5#''))) or ((((label_eq jEpYV) impl state_eq None) aand (state_eq None))))) until ((label_eq k_7) until output_eq [])))) or (label_eq ''Z''))))))) impl (ev (input_eq []) or label_eq s_d)))))))))) (watch v8____P BJ7_8)" oops
lemma v34: "(label_eq ''E'' aand state_eq None) (watch ev9__v o__i)" oops
lemma M_9: "((input_eq []) suntil (((((((((((((state_eq (Some 81) suntil label_eq s5B) aand state_eq None) until (input_eq [] or not (label_eq ''G'' impl (label_eq ''h/'' impl (label_eq ''4'' or state_eq None)))))) impl label_eq f_7) suntil input_eq [((((Num 5563))))]) or (output_eq [Some (Num v_e),None, (((Some em__g))), Some rl7]))) impl (input_eq [(Str ''2'')] impl ((output_eq [(Some J_8),Some m1t,Some (Num v7__1_6),(((None))),(Some (Num H90)), Some V50] until (state_eq None impl (output_eq [Some l_3,None] until (label_eq e7_1 impl output_eq [None, Some w_Q, Some v_8_P,None, None,(Some (Str ''A}'')), Some bvV])))) or input_eq [Num FQ8,Str HS_0]))))) impl output_eq [(None),None, None,(None),Some E8C]) until (input_eq [] suntil state_eq (Some 468)))) (watch m__CR6h92e_6_2c N0__8)" oops
lemma n0f: "(input_eq [] impl (state_eq (Some 04) impl (label_eq ''7;''))) (watch j9_5 X_I__4_3)" oops
lemma z_y: "((label_eq ''7'') suntil input_eq []) (watch R_q s53)" oops
lemma u3_A75: "input_eq [] (watch A8_0 SFt)" oops
lemma j__8: "output_eq [] (watch V_4b_7 TLy)" oops
lemma r_V: "(state_eq (Some 8) suntil alw (output_eq [])) (watch Q_4_1 S_Y)" oops
lemma T2_c: "state_eq None (watch B2__5 X__00)" oops
lemma Y44: "(label_eq I6k) (watch u_l2 f__c)" oops
lemma S__1xC: "(output_eq [] or input_eq [Str z_y, Str ''|~'',Str Q15_Li,Str ''<'']) (watch vp39 dAf)" oops
lemma L_P: "state_eq (Some 3) (watch x___j S_B)" oops
lemma uV6: "(input_eq []) (watch p_7 u713)" oops
lemma St8: "((label_eq ''y<'' or ((input_eq [((Str S9D)),Str Os5, (Num w_rX_y), (Str ''1w~c'')]) or ev (((output_eq [Some (Num V_4),(Some q__0),None,Some Ml_Y, ((Some f_0))])) suntil input_eq []))) or input_eq [Str ''|3/-'', Str u2i,(((Num tmR))),(Str uMR),(Num 7), Num 3]) (watch s_x xD__7)" oops
lemma g7_5: "(label_eq ''p'') (watch vfx X9_KD)" oops
lemma U_U83: "(state_eq (Some 6) aand output_eq []) (watch lw__l r8F)" oops
lemma N__4: "state_eq None (watch b7u_x0GE69 q_1)" oops
lemma m_W: "(label_eq Q65 impl label_eq ''w9D'') (watch e_6 xq065)" oops
lemma Oi0: "nxt (label_eq AKUD) (watch B_2 Z_1)" oops
lemma gzp: "state_eq (Some 28) (watch R_oO Rrd)" oops
lemma L_T: "state_eq (Some 935) (watch Z_1C2 F_Y)" oops
lemma G_L: "(input_eq []) (watch Pd559___3 V___5)" oops
lemma e_U_36: "(input_eq [] aand state_eq (Some 73)) (watch HFM Z_9)" oops
lemma V79: "(((label_eq x68 until state_eq (Some 01817706)) or (state_eq (Some 026) impl label_eq t_x))) (watch T6W F___g)" oops
lemma n_Wr: "state_eq (Some 8) (watch j_8Q V_5)" oops
lemma Iy2: "state_eq None (watch Y_Q b9_ha)" oops
lemma G_2C: "ev (state_eq (Some 422) until (((state_eq None or input_eq []) or (nxt (((((label_eq ''#'' or (state_eq None impl ((((((label_eq ''#'' impl output_eq []) suntil (state_eq None suntil output_eq []))) suntil label_eq P_b_4N) aand (((label_eq ''2'' suntil input_eq []) suntil state_eq None) suntil state_eq (Some 396452)))))) until label_eq ''E'') until (input_eq [] or input_eq [(Num 1)]))) or (input_eq [Num 2, ((((Num 58))))])) or output_eq [(Some w98)])))) (watch KT0 g_2__p)" oops
lemma Jy_6: "(ev (state_eq None or (label_eq ''z;6m4''))) (watch p_n g_2)" oops
lemma K__h: "not ((state_eq (Some 54)) aand input_eq [(Num 3),(Num 50073)]) (watch W_4 c_2)" oops
lemma S2E: "(label_eq P5X impl output_eq []) (watch R_5 C1F8)" oops
lemma l_S: "(((((((output_eq [(Some M_91_G_0),Some A06] aand (label_eq ''` '' until not (((output_eq [] or (state_eq None)) suntil (output_eq [Some I6O, (Some Pjd4_8), Some (Str o_l)] impl (input_eq [(Str ''{''),Num 07]))) impl state_eq None))) aand output_eq [Some H_7,Some (Str G5____x6_s967L)]) impl alw (((input_eq [] impl input_eq []) or input_eq [Str M_88]) aand state_eq None)) suntil ((input_eq [Num dm_7] until (label_eq ''.'' impl (output_eq []))) suntil output_eq []))) or ((output_eq [] suntil state_eq None) or state_eq (Some 1)))) (watch e_w P5J)" oops
lemma o66_7: "input_eq [] (watch W_3 iBl)" oops
lemma N33_w: "(output_eq [] impl input_eq [(((Num 73))),Num x0N, Str G__Z7]) (watch g_5 d18)" oops
lemma a_9: "output_eq [] (watch Pr9 a_cx4Z043_zS)" oops
lemma uc_d: "(ev (input_eq [(((Str ''c0@1''))), (((((Num 946))))),Num 90502] until (label_eq qH1 or input_eq [(Str q9_4W),Num Fp___84, Str a_6,(Str ''*(_''),Str ''*8N9=q_'',(Num 67),((Str ''(:O'')), Str ''%)'', (Str ''<>''),Num kN_5])) aand (((input_eq [] impl (state_eq (Some 1) aand input_eq [(Num 6),Str u_m94])) aand (((((input_eq [(Num 3)] until output_eq []) impl output_eq [(Some s__0), Some (Num 437)]) aand ((label_eq E_f until input_eq []) or state_eq (Some 4)))) suntil label_eq '')='')))) (watch M_v x6s_F)" oops
lemma Z2__75: "label_eq Q_D (watch ckI aRL)" oops
lemma q_4: "((input_eq [] or output_eq [])) (watch j_5k P0_4)" oops
lemma tJT5: "input_eq [Str u_T_64, (Num 711), (Str x_17), (Num 1), ((Str ''?L87Q`5'')),Str ''c'', Num Tjh, Str S_6] (watch X_7 w_0)" oops
lemma Pl_3: "output_eq [] (watch A28 i__6)" oops
lemma o__L: "((((((label_eq Vd36 until input_eq [Str m9m,Num p_6_5,(Str ''EMz''), (Num p_93),((Str ''/;'')), (Num 9),(((((Num b3_F))))),Str '' '']) aand label_eq '')'') impl (output_eq [Some U9_B, None]))) until (state_eq None aand label_eq Za2)) until state_eq (Some 313)) (watch O_a tF1_4)" oops
lemma sBnq: "output_eq [None,Some g1N,(Some G_E), None,Some (Num s_R7), (Some L04), None] (watch FOo nH5)" oops
lemma X__2: "(input_eq [(Num 605),Num 239,Str ''^9'',(Num u_5)]) (watch z_7 DD4A_t)" oops
lemma hYD: "(label_eq ''<'') (watch w6X2 N72)" oops
lemma zV8: "(state_eq (Some 7) aand state_eq (Some 0784)) (watch N_85 l_d_5B_3)" oops
lemma f_4: "(((((label_eq ''!'' or (output_eq [])) impl output_eq [((((Some (Str ''6_jG''))))), Some (Str ''&'')]) suntil label_eq ''v%r'') or (input_eq [((Str ''-''))] suntil (((((label_eq A6_f suntil ((state_eq None or output_eq []) or output_eq [Some J5L])) aand label_eq ''fI'') until label_eq v_qk) aand (input_eq [(Str i_b), (((Str ''p'')))])))))) (watch p_s P_n)" oops
lemma D_1: "label_eq C_2 (watch a5G q_9)" oops
lemma F9_A: "((input_eq []) or not (label_eq z_2 aand state_eq None)) (watch eD7 w_60b_N)" oops
lemma M29: "(output_eq [] suntil (label_eq ''27#'' suntil output_eq [(None),None, Some X_K])) (watch E3_6 J_mx)" oops
lemma h_9MZ_4: "input_eq [] (watch f2_N H0I)" oops
lemma W54: "(((label_eq f74R) impl output_eq [Some v45, Some t69]) or label_eq ''0}.{?1=m'') (watch Bd0 B5m)" oops
lemma w230: "(((input_eq [(Num 7)] suntil label_eq P_f) impl (input_eq []))) (watch opG2 Fa494)" oops
lemma q8_O: "output_eq [Some K_f] (watch znf j_15)" oops
lemma VgQG: "(((((((((output_eq []) suntil ((output_eq []) aand output_eq [])) suntil input_eq [Str ''?'']) until (output_eq []))) aand ((state_eq (Some 1) aand output_eq []) suntil alw (input_eq [(Num V2_4)])))) suntil (input_eq [Str y_I_3, Num W_I_dC5u5]))) (watch H_9 R__6)" oops
lemma R50t: "((((input_eq [((Str ''`$&'')),Str ''q*'']) until ((state_eq (Some 4) impl (alw (state_eq None suntil ((state_eq (Some 3) until state_eq None) aand output_eq [])) aand ((input_eq [] impl (state_eq None or (state_eq (Some 07) until (((output_eq [] suntil input_eq []) or (input_eq [])))))) until (label_eq d_0V until label_eq H8XF)))) aand not (label_eq Q3i suntil state_eq (Some 46))))) suntil input_eq [Str ''t'']) (watch ATa MD_2)" oops
lemma s__y: "state_eq None (watch F4x wd_9)" oops
lemma b_9: "output_eq [Some T_5T,Some E_8, None, None, None] (watch h4f DJ2)" oops
lemma fhc_0: "output_eq [(Some j0M_Z), Some j6O,Some k8n] (watch Kd_e3 N5V)" oops
lemma X__8: "((state_eq (Some 49)) until label_eq c__8) (watch z__x O_Z2)" oops
lemma IM2: "((input_eq [] impl input_eq []) suntil alw ((output_eq [] until alw (label_eq ''%Y'' until (output_eq [((((Some N___7)))),None,None]))) suntil label_eq Wi1)) (watch x7N_W rDw)" oops
lemma sGN: "input_eq [] (watch i__X M___x2)" oops
lemma R_Q: "(label_eq l91 aand (alw ((((((state_eq None or not (input_eq [])) until (((((label_eq ''$'' suntil (state_eq None or (output_eq [] impl output_eq [Some WIs2,Some huaF,Some (Num 6),Some (Str e_P)]))) impl (((label_eq L9_7wq2 or ((label_eq ''3'' until (input_eq [])) until state_eq (Some 8))) aand (((((output_eq [Some m__y20,None, None] impl label_eq R_87) impl label_eq y___71L) until (((((output_eq [Some (Str ''|(''),Some m_CW]) aand (((((((((input_eq [(Str ''%6'')] until label_eq r39) until (state_eq (Some 4) until input_eq []))) aand (label_eq G_b aand ((state_eq None aand output_eq []) until label_eq ''+:>3%'')))) until ((input_eq [Str o54,((Num Z__K)), Num 0,Str ''3'', Num 4] until input_eq []) until output_eq [None,Some (Str ''^''), Some (Str ''6b''), Some Aye, Some (Num OB_6C), None,Some (Num 1), Some (Num hrk),None,Some (Num 6)]))) suntil label_eq ''5'') or ev (label_eq ''?'')))) until (not (output_eq [None] aand (label_eq ''<?*8Gp'' or label_eq Md_M_7)) suntil (input_eq [Str ''(<,'',Str ''l'',Num 512] impl (label_eq ''?'' suntil state_eq (Some 86))))))))))))) or ((((ev (((label_eq ''8'' impl output_eq [Some K_3]) or (output_eq []))) until (input_eq [Str I_i,((Num 95))] impl (((state_eq (Some 96)) until input_eq [(Str ''5+'')]) suntil input_eq [Str ''257`-:'', (Num kbk)]))) impl ((output_eq [Some N___2E0]) aand label_eq ''m''))) suntil (output_eq [Some Z_l,Some (Str j_v), ((None)),Some (Str ''N5%9''),Some A1P,(Some (Num 4541)), Some (Num 79), Some i__0] impl ((output_eq []) or state_eq None))))))) suntil (state_eq None))) or state_eq (Some 0)))) (watch o__v XUaF)" oops
lemma R0p5: "input_eq [(Str w_n), (((Str ''$7@.!6/(''))),(Str pn6)] (watch f_h aAE)" oops
lemma I_8: "label_eq K_Y (watch N20 VYD)" oops
lemma Q_F: "(output_eq [Some O5NM8, Some d_6,(None)] aand ((((output_eq [(((Some G_9_O)))] aand (((output_eq [None, Some x6p] aand ((label_eq ''->'' or output_eq [None,Some (Str M_9),Some ay_04]) impl state_eq None)) impl state_eq (Some 5272)) impl (((label_eq z85) suntil (output_eq [])) or output_eq []))) or state_eq (Some 10)) impl (((((((((label_eq ''@0'') aand (((input_eq [(((((Str G4Y)))))] until (input_eq [] impl ((output_eq [] impl input_eq [(Str '')''), Str ''%'',Num O_4e4,Num 549840,Str DFJ,(Num 6438)]) aand (((((not ((state_eq None) or label_eq ''_'')) aand state_eq (Some 04)) aand output_eq []) suntil (((output_eq [Some (Str ''*~''),None]) aand (output_eq [None, (None), (None)])))))))) impl state_eq (Some 14411)) aand input_eq [Str ''qp'', Num 6474,Num 38,Num ck__3])) until (state_eq None))) until (ev (((state_eq None or (((label_eq ''|S}'') aand (state_eq None)))) impl (input_eq [(Num y_i), Str ''{nP9)Q/'', (((Str i75)))] or (nxt (input_eq []) impl (((ev (label_eq '' :'' or (state_eq None))) until (label_eq W__Z suntil (input_eq [] impl state_eq (Some 28))))))))) aand (state_eq None)))) until (label_eq WZ2 suntil ((label_eq F_8K or input_eq [(Num nqu), Str Tt8, ((Str ''2'')), ((Str ''<'')), (Num QD3)]) or label_eq ''> '')))) or label_eq M_0)))) (watch C_79 d39)" oops
lemma x_2Kg: "output_eq [Some (Str W_7),Some oAX,Some (Num 3),None,None] (watch G_9 P35)" oops
lemma P16: "output_eq [] (watch PRW G9R)" oops
lemma D92: "input_eq [(Str P__oZ), Str LA8, (Num U__Q),(Str '')a''),(Str L_0)] (watch X9__1 f_4)" oops
lemma haZ: "(state_eq None) (watch m__U I_0)" oops
lemma A55: "state_eq None (watch q___54 p_Io_7)" oops
lemma o__g: "(((label_eq YwDd) impl output_eq [((((Some x____4)))),None]) aand output_eq [Some (Num 768)]) (watch p_1 o_17)" oops
lemma v__9: "(output_eq [Some (Num C_Jwz)] aand (state_eq (Some 407728414) or label_eq ''^e'')) (watch N5__0 XTi_3y)" oops
lemma Gj8: "(output_eq [(Some K___8),Some (Str ''}L''), (Some (Str ''%T;'')), Some (Num 6)] or (state_eq (Some 0) suntil (label_eq ''b''))) (watch r5I tXPu)" oops
lemma c_9__g: "(state_eq None) (watch z_8 yqj)" oops
lemma C_d: "output_eq [] (watch I28 p2Kle)" oops
lemma z35: "output_eq [] (watch D48 cA0)" oops
lemma I_K: "input_eq [(((Str ''6'')))] (watch k_5 z84)" oops
lemma z6z: "(state_eq (Some 71) aand input_eq [((((Str B_0)))),Str ''h'', Num 8,(Str V_af), Num w9_3_V,Str ''^'', (Num P__3)]) (watch Q_N M9d)" oops
lemma P9b: "((output_eq [(Some (Str ''.''))] aand (state_eq (Some 7) suntil (((output_eq [] until output_eq []) aand (input_eq [Str v_9q]))))) suntil ev (ev (label_eq '';''))) (watch Y7z X_6w)" oops
lemma ae__8: "(output_eq [] aand input_eq [(Num 6), (Str ''/='')]) (watch h_9X Q_3)" oops
lemma E____1: "state_eq (Some 38) (watch y_I Y9r__6)" oops
lemma C90: "ev (input_eq [] impl (ev (output_eq [] impl output_eq [Some adK, (Some CQf)]) until ((((((state_eq (Some 1)) suntil (input_eq []))) or (input_eq [Num 3]))) or output_eq [((Some C_5)), None, Some GgJ_F0]))) (watch j82_O1N L3F)" oops
lemma y__0: "label_eq ''3'' (watch A5U r_j_X)" oops
lemma h_63_2: "(((input_eq [(Num 7), (Str ''9''), (Num xR8), Str o8D] impl output_eq [None, Some j_w, (Some a_26)]) aand state_eq (Some 75)) aand input_eq []) (watch q_j xZ_77)" oops
lemma P5r: "(input_eq [(Str B11), (Str ''m'')]) (watch a__Lqr GfL__3PD)" oops
lemma Z_355: "label_eq ''>}'' (watch z__k l_f)" oops
lemma j_s: "(state_eq (Some 3) impl alw (input_eq [] until (state_eq (Some 18) until input_eq []))) (watch ka_d f__1)" oops
lemma E_0O: "(input_eq [Str l_luT]) (watch g_5 qS2_J54w)" oops
lemma W28: "((input_eq []) suntil (state_eq (Some 3))) (watch Q3T ZE__t)" oops
lemma x_V: "input_eq [Num W_T4H, (((Num 67))),Str ''b'', (Str Ucs), (Str ''Xr''),Num 96818,Num e_K, Num 80] (watch H_x a_6)" oops
lemma h_a: "(ev ((((output_eq [] suntil label_eq o_91) aand (input_eq [] aand (((input_eq [Num 1,((Num V_6)),(Str n_Q_P23)]) or ((output_eq [Some (Str z__U), None]) until input_eq [])) suntil state_eq (Some 025258))))) aand label_eq ''x,'')) (watch F_Q M_x9ht)" oops
lemma E9N: "(input_eq [Str W_u,Str ''3'',((Str U39)), (Num x_v),(((((Num 175))))), Str ''80'', Str '':''] impl (input_eq [((((Num 8)))),Str ''07''] until label_eq B_9C)) (watch eZ8 a54)" oops
lemma t_B: "((((output_eq [((None))]) until (((((nxt (((output_eq [Some (Str y_G8), Some u_2] until label_eq E2s) suntil (input_eq [] impl (output_eq [None, (Some (Str ''=''))] until (output_eq []))))) aand (ev ((label_eq hbjn or (((output_eq [Some Ge785e, ((Some (Str d_a))), (Some Z6R)] suntil (label_eq qj_t aand (((input_eq [] impl (state_eq None suntil output_eq [None, Some (Num 71),Some (Num 8), Some (Str '')Nn{'')])) aand (input_eq [((Str X230)),Num jyR9] aand input_eq [Num 26, (Num w66)]))))) until (label_eq j__9o9 aand input_eq [((((Num j2r)))),Num jni])))) or (((label_eq ''r'') impl (input_eq [] until alw ((state_eq None impl state_eq None)))))) suntil (((input_eq []) suntil (input_eq [(Str l9_J)] or ((output_eq [] suntil label_eq gSP) impl (output_eq [] suntil (ev (state_eq (Some 6) until (input_eq [] impl label_eq g7oM)) or ((output_eq [] until output_eq [((None))]) impl state_eq None))))))))) until (output_eq []))) impl (((alw (((((((((((label_eq U_ch suntil label_eq ''Z?'') aand input_eq []) impl (label_eq '';'' suntil output_eq [Some rnc, Some O_9, Some x_31]))) until (label_eq IFO aand (output_eq [Some (Str ''@'')])))) suntil label_eq ''{P'') aand label_eq x68) aand (((state_eq None) until (nxt (((label_eq ''8'' suntil ((((label_eq p_3m impl output_eq []) aand (label_eq G_E_13 impl label_eq q_2))) until alw ((((((output_eq []) until state_eq (Some 3)) suntil ((((((output_eq [(Some a_o),Some (Num I_3), Some B_4]) impl (output_eq [] until (((output_eq []) aand state_eq (Some 93842)) or state_eq (Some 8))))) aand (label_eq ''+92'' until label_eq ''Up''))) aand label_eq J_E6))) until (((input_eq [] until (((output_eq [None, (Some (Num ea_852)),Some u_0,(None)]) or ((((output_eq [(Some (Str ''@'')), Some i_55,(Some (Num 425)), (Some I82),(((Some DgG))),Some (Num tVH), Some u62__u, (Some vW6),((Some b9q7)),Some (Num 7)] suntil state_eq (Some 62)) or output_eq []) until (((not (label_eq ''q'' impl (state_eq None)) aand input_eq []) aand input_eq []) or (state_eq None))))))) suntil (((input_eq []) impl state_eq None) suntil output_eq [Some S_z]))))))) aand (state_eq (Some 36) or state_eq (Some 2)))) until label_eq P6J)) until (label_eq J_T3M or input_eq []))) aand ((((((((label_eq z_B_1v) aand (output_eq [None] suntil output_eq [Some (Str ''(0''),Some M79,None,(Some w_b), (Some b2k),Some (Str ''3c''), Some B5R, Some Y55]))) suntil output_eq []) aand (((state_eq None) or ((((((state_eq (Some 66) suntil state_eq (Some 729)) aand state_eq (Some 50)) aand output_eq []) until ((output_eq [] or label_eq ''j>.'') aand label_eq U71))) aand output_eq [None]))))) impl (state_eq None or label_eq '' x''))))) suntil state_eq None) impl (input_eq [] impl input_eq [])))) until label_eq ''~(''))) until state_eq (Some 5)) (watch Lhq A__ET)" oops
lemma k_3: "state_eq (Some 99) (watch r1RGa D_F3)" oops
lemma a_12: "state_eq None (watch nl_a W5___5)" oops
lemma S_3_U6_6: "(output_eq [(None),((Some (Str ''-,9''))),None,Some (Num 3), Some EpB, (None),(Some (Num K__rH_6l)), None] impl label_eq ''0'') (watch w3P s___79)" oops
lemma y30: "(input_eq [((Str ''7'')),Str ''|'', (Str ''9<3|Q6''), (Str HW9R),((((Num r_Y)))), Num 852]) (watch lg36 a_A)" oops
lemma k4__g: "(input_eq []) (watch S9_V uX9_r_y)" oops
lemma Vxh: "state_eq (Some 8) (watch R_L tU5)" oops
lemma R_d: "input_eq [Num 361,Str V_1] (watch t_9 o_l)" oops
lemma s__M: "((output_eq [] or (output_eq [(((None))), ((Some (Str WmH)))] or ((((state_eq (Some 209) suntil ((output_eq []) or output_eq [])) or label_eq B__3) until input_eq [(Num E_Q),Num y__0,Str B__J, Num uj30, (((Str e_5))),(Num 801),(Str ''L 96'')]) or output_eq [Some (Num l_g), (((None))), (Some (Str wtx4)), Some (Num U_K8g_9)]))) until input_eq [Num r_e, Num y__5, (((((Num 345))))), (Num 2)]) (watch O_6 P_Z)" oops
lemma H___n6: "output_eq [Some (Num 13)] (watch a_9 Z_8O)" oops
lemma LKV: "output_eq [Some (Num a7___7KS), Some (Str ''!R5'')] (watch n__s J5u___D_8)" oops
lemma D3H: "state_eq None (watch k__7X L_w)" oops
lemma Nv85: "state_eq None (watch hb_7d M2_8)" oops
lemma b694: "input_eq [] (watch qo3 Ms__C)" oops
lemma b_C: "(input_eq [((Str X_Cy)),Num 45,Num 9,Str k_d9, Str D9B, Str Lb8] or not (((nxt (state_eq None until ((((label_eq ''RM'' impl (input_eq [] aand ((state_eq (Some 31)) suntil input_eq [(Num 318),((((Str c_8s))))]))) or output_eq [(Some (Str '',+4'')), (None), (Some WZ0)]) suntil (label_eq ''0'' suntil ((((not (input_eq [Str T_N, Str L8yd, (((Num 1))), (Num pZ3), (Num G_Y)])) suntil label_eq ''%02'') until ((input_eq [] or (state_eq None aand input_eq [((((Str JA7)))), Num EL2])) or input_eq [])))))))) aand state_eq None) or label_eq ''910'')) (watch r_4 G_k4)" oops
lemma U3M: "(state_eq None or (((input_eq [] aand state_eq None) aand output_eq []) impl label_eq ''1o1'')) (watch l_l n___i_0)" oops
lemma N__o: "input_eq [Str H__Z] (watch Iqm N_9)" oops
lemma z__6: "(((label_eq v_30 suntil label_eq en3) suntil (not ((output_eq [] or output_eq []) or output_eq [])))) (watch j3i g_3)" oops
lemma q_1: "(state_eq (Some 52) impl state_eq (Some 886)) (watch tW6C Yv_5t)" oops
lemma J7_83: "output_eq [] (watch M_H n_8)" oops
lemma v_7: "((((state_eq None until state_eq None) until nxt (input_eq [] until output_eq [((None)),(None)])) until ((((input_eq [((Str '':'')),(((((Str ''7''))))), Str b_8] until ((((label_eq A__B or input_eq [Num 9, Str ''-$2'', ((Num AaZ__51))]) aand ((alw (((label_eq ''L'') or (state_eq None suntil (input_eq [] aand (state_eq (Some 26)))))) suntil input_eq [Num 9, Str E__8X,Num S_00,(Str '' '')]) suntil input_eq [(Str C_8),((((Num s70o))))]))) until input_eq [((Num nr_9))])) aand input_eq []) or (input_eq [(((Num 31)))] or (label_eq ''!'')))))) (watch dU3_02 n_6)" oops
lemma P__4: "(((((((((output_eq [] or ((output_eq [(Some (Str ''?''))]) or state_eq (Some 021))) or input_eq []) suntil (label_eq ''@'' impl output_eq [Some (Num 3),(((None))), Some (Num u_9)]))) suntil (((output_eq [None, None,None, None]) until label_eq ''h9_'') aand input_eq []))) aand nxt (input_eq [((Str vPa))] aand ((((input_eq [(Str '')|^0''), Str g_J]) suntil ((((((((output_eq [] or output_eq [Some t_0, ((Some B__7)),Some h_1]) or (state_eq None aand label_eq UN_n))) until (((input_eq [] suntil state_eq None) impl ((label_eq ''?X'') impl input_eq [Num y_t,Num H_4,(((Num f74))), Str ''5'', ((Str ''7q3'')),Num 4467,((((((Num k_5))))))]))))) until output_eq [(Some (Str ''.0yB7j'')), None]) suntil (state_eq (Some 8) or ((input_eq [Str V6_2,((Str j973))] impl label_eq Z_i))))))) impl output_eq []))) impl (label_eq l_7))) (watch r2P l7Rz)" oops
lemma g075: "input_eq [Num 6] (watch fIm c7__T)" oops
lemma Oh34: "(((((output_eq [(None),Some (Num 011946), (None), (((None))), (Some Z__5r)] or ((input_eq [] impl alw ((label_eq ''@'') suntil input_eq [])) impl output_eq [])) until output_eq []) aand output_eq [None,Some LV_7M]) until (label_eq i_5 or label_eq '',3+''))) (watch Oou RC9)" oops
lemma CYk3: "output_eq [] (watch I_7 g_5)" oops
lemma z___Z: "(state_eq (Some 2)) (watch h38 k70)" oops
lemma a1_M: "output_eq [None,Some D_H,Some r_0] (watch a02 FKH)" oops
lemma L3dD: "(state_eq (Some 76) or ((output_eq [] or (((output_eq []) suntil (output_eq [(Some m95)])))) impl label_eq y_o)) (watch n_4 y_1)" oops
lemma t_7JX: "(input_eq []) (watch M_t k5z)" oops
lemma R__L_Y: "((label_eq ''('' aand input_eq []) aand label_eq ''r>@'') (watch f0_tC W9c)" oops
lemma b_2_2: "not ((label_eq D35 until (input_eq [])) aand state_eq None) (watch wy_70 B_K)" oops
lemma n_q: "input_eq [(Num Z8u), ((((Num 9))))] (watch N1z i70)" oops
lemma N9H6: "((input_eq [(Str ''9''), (Num 136)] aand (label_eq n__uE7b or output_eq [None,Some da1_7Z]))) (watch v_b c07)" oops
lemma mB7X: "input_eq [Num 7, (Str ob1_1)] (watch U_g yFYCj)" oops
lemma N_7: "(input_eq [] suntil (output_eq [Some (Str ''!7''), (Some (Str yo_0)),Some FaP____K_0462] impl output_eq [None, Some (Str ''9'')])) (watch g2p__h_9 ht0)" oops
lemma m_1Z: "(input_eq [Str ''{//9'', Num 04,Num 312, Str Md9]) (watch gr4 Q__o)" oops
lemma EQa: "nxt (output_eq [Some x__e]) (watch n0f H3v)" oops
lemma y__K664: "(output_eq [((Some (Str W_6))),None] impl input_eq []) (watch b8_6__V P__T)" oops
lemma K_X: "(output_eq [] aand state_eq (Some 25217)) (watch QzL C__H)" oops
lemma Rcg: "(input_eq [] aand (state_eq (Some 616) or (((output_eq [(None), (Some (Str X5__D)), Some (Num eY_7), (Some (Str hIH_2__V)),(Some n_1_r), Some mu2]) until state_eq None) suntil output_eq []))) (watch Pmc g_x95)" oops
lemma O_N: "state_eq None (watch TO5 Lq69)" oops
lemma nd_6: "(label_eq ''5 Y}?=9_'' impl (label_eq ''%'')) (watch A_2s_6 n__A)" oops
lemma x_2: "output_eq [Some g_r,None, Some (Num 635),None] (watch e_U Su7)" oops
lemma R_1: "((((((output_eq [] aand (output_eq [None,Some (Str or0),Some (Str ''*''), Some b2O] or state_eq None))) or (output_eq [None,Some Y___d,Some r4m, Some Kn_T__J] suntil (state_eq (Some 0) suntil input_eq [])))) aand ((output_eq [Some (Str ''<$V'')] suntil output_eq [(Some J__4__c),Some (Str ''~''), (Some (Str ''p''))]) until (((input_eq [Str e1__e0_M,(Str a__f),(((Str B_3)))]) aand input_eq []) or label_eq S_O110)))) (watch Ht____E L99)" oops
lemma h_n: "(((((state_eq (Some 04) aand input_eq [Num q_q,Str ''1'',Str ''4=+'',(Num 84)]) or ((ev (alw ((((label_eq ''%'' suntil ev (label_eq ''8'')) suntil state_eq (Some 6)) suntil ((((output_eq []) aand (state_eq None suntil (((label_eq '':'' impl state_eq (Some 4)) or ((((((nxt (label_eq ''Y'' or (label_eq W_h0 until output_eq [None, None, ((Some (Num 7))),Some (Str ''@''), (None), Some MpB, Some (Num 3847)])) suntil ((((input_eq [(Num g_wZ3),((Num 68)), Num fsm, Num 98] suntil (((label_eq ''7,'') suntil (input_eq [Str ''>2&_h: p`'',((((Str u90)))), Num F_8] or (label_eq z_5X until label_eq ''+$''))))) aand label_eq ''}}u'') aand (state_eq (Some 3) until label_eq ''8'')))) suntil label_eq R_a) aand ((not ((((((output_eq [] impl ev (state_eq None)) until label_eq e_RW) impl (((alw ((alw ((label_eq n90 or state_eq (Some 87)) aand label_eq ''5'') or input_eq []) aand input_eq [(Str ''!+''),((Num 7)), Num g_0]) impl (((input_eq [(((Str E29))),((Str R5L)), (Num g0jS), (((Num ta8)))]) aand (((nxt ((input_eq [Num H1_1pS0] or (nxt (state_eq None impl (output_eq [((None)), Some (Str j91_q1)] aand not ((not (output_eq [(None), Some d9X,Some (Str y__rI)] aand label_eq u1Q) until label_eq M__6) until ((input_eq []) aand label_eq h4k)))))) or input_eq []) until state_eq (Some 043)) aand (output_eq [] suntil (input_eq [] suntil ((nxt ((output_eq []) impl alw (output_eq [((Some j_7)), Some c34_m8, Some V4k,Some (Str eqz), Some (Num L_1), (None),(Some (Str E8nF))])) impl label_eq ''{P'') or label_eq F2s)))))))))))) suntil (input_eq []))) or state_eq None) suntil input_eq []))) aand state_eq None) impl state_eq None))))))))) or ev (((output_eq [None] or ((((((state_eq None) aand (((not ((state_eq None suntil state_eq (Some 2000)) aand state_eq None) until (state_eq (Some 2) suntil label_eq ''4('')) impl input_eq []) until output_eq [])))) impl ((not (((((input_eq [] suntil input_eq [Num s_k]) suntil output_eq []) until (((input_eq [(((((Str ''?-^@''))))), Str ''6*}'', ((Num 4)),Num 546, Num 0,Num Hx6,Num dDw] aand (((((label_eq ''L36'' or output_eq [((None)),None, Some (Num jw0), (Some p_1)]) suntil (label_eq E_3 until input_eq []))) until (((((((((input_eq [] or input_eq [])) until ((state_eq (Some 2) aand (((output_eq [] impl input_eq []) aand state_eq (Some 9183)) aand state_eq None)) aand input_eq []))) suntil output_eq [(((Some (Str ''8!'')))),(None)]) impl (output_eq [None,(Some (Str ''ys`:9 |''))] suntil label_eq ''-''))) until ((input_eq [Str z_2,((((Num 6)))),Str ''3'']) or label_eq y6r)))))) aand ((output_eq [] suntil state_eq (Some 12)) until alw (input_eq [(Str ''-''),(Num A6_8_5EH),(Str GX6)] or state_eq (Some 2))))))) until (label_eq ''R?'' impl (((state_eq (Some 0) or state_eq (Some 3)) suntil ((((state_eq None aand input_eq [Str j_K]) aand (input_eq [] or (((((input_eq []) aand (input_eq [Str AI_9, ((((((Num 581031)))))), Num a_W] until state_eq (Some 79)))) suntil (output_eq [(Some F__B74M),Some (Num 80), (None), Some (Str ''~}N44v''),Some L3x, (None)]))))))))))) or state_eq None) or state_eq None)))) aand (label_eq Gf7 aand label_eq ''Z&'')))) aand (state_eq None impl (input_eq [] aand input_eq []))) until output_eq []))) suntil (output_eq [(Some B1_qa), Some D_8, (((None))), Some (Num 1), (None)] aand state_eq (Some 3)))) (watch LX_g J_5)" oops
lemma d_r: "(state_eq (Some 70) suntil ((((((label_eq ''#'' until input_eq []) aand ((((((label_eq XC9 suntil ev (((state_eq None or (alw (output_eq [Some (Num 5249)] until output_eq [Some (Str ''Nn>'')]))) impl (ev ((((input_eq []) or ((input_eq [] suntil input_eq [Str D_T, (((Str ''*.5:_'')))]) until input_eq [Str i6_g]))) aand output_eq [Some tM19, None,((((Some D_m))))]) until (output_eq [(Some (Str x_1))]))))) aand label_eq ''l'') or input_eq []) or input_eq [Str ''h'',(Num ZRI)]) aand (output_eq [Some sc9,Some (Str ''7|'')])))) impl (input_eq [] or output_eq []))) aand ((input_eq [] until (((((ev (label_eq Z__H aand input_eq []) impl label_eq s_e) suntil (state_eq (Some 887132113) until (((((output_eq []) or input_eq []) or state_eq None) or (label_eq ''_'')))))) impl output_eq [Some (Str '' ''), ((None)), (Some (Str v__7E))]) suntil output_eq [])) aand input_eq [])))) (watch I____I9R9_3 zt__41_3)" oops
lemma MBj: "((output_eq [] impl label_eq ''_s'')) (watch I6_t1 S_J)" oops
lemma G___X: "((input_eq []) or state_eq None) (watch ngR h_u)" oops
lemma q_c: "label_eq ''24'' (watch ri66 He_3)" oops
lemma t_J: "state_eq (Some 2) (watch D_5 pZ4)" oops
lemma xZ__O: "input_eq [] (watch f_N o_2)" oops
lemma u89: "(output_eq [] impl input_eq [Num 8, Num K__03,Str ''l<)|'', Num 9,(Str G__e), Str Y_8, ((Str '','')),Str k__J]) (watch X_2 z_d)" oops
lemma Ji_0: "input_eq [Num k_R, Num X__r,Num 0,((Num 26))] (watch ta_3 bO___y)" oops
lemma J4_U3: "state_eq None (watch j_P_8 w99)" oops
lemma b63: "output_eq [] (watch X_0k E47_n)" oops
lemma n_89: "(((((((input_eq [] suntil ((((((((input_eq [Str bv80] impl output_eq [Some I_k,Some (Num d__u), Some (Str IX_r)]) until (state_eq (Some 04) suntil ev ((((label_eq j2_S until (not ((((label_eq O_m or (alw (((output_eq [] until state_eq (Some 1323)) or (((label_eq n40 aand state_eq (Some 2)) or (((input_eq [(Str f_e), (Str E0u8), Num xo12,(Str IS1),Num 9] impl input_eq [(Num 4), (((Str ''QN''))),(Str ''){'')]) impl ((label_eq EP2 aand (((nxt (input_eq []) aand label_eq ''*'') suntil (state_eq (Some 389) or label_eq s3z)))) impl ev (input_eq [Num mS0,Num co_l_y0, ((Num 6))])))))))) aand (((state_eq (Some 0)) or (input_eq [] or (output_eq [] suntil not ((output_eq [(None), None] or (state_eq None)) impl ((ev (not (output_eq [] or (output_eq [] or label_eq TXW))))))))))))) impl (input_eq [] aand label_eq ''|>''))) aand nxt ((input_eq [((((Num X_7P))))] impl label_eq ''/'') until output_eq [(Some (Str w____2))]))) impl (((alw (state_eq (Some 6862) or output_eq [])) impl ((input_eq [] until not ((state_eq None aand (not (input_eq [] impl input_eq []) until state_eq None)) or state_eq (Some 3))) suntil ((input_eq [] until state_eq (Some 0)) until (state_eq (Some 1) impl label_eq ''0''))))))) until (label_eq C___25 suntil output_eq [Some i_S])))) until (alw (nxt (input_eq []) impl (((input_eq [(Num 2), Num 72] impl (state_eq (Some 6) impl input_eq [])) until (label_eq ''!*?@'' impl label_eq T__3O)))) impl label_eq N_5))) until (label_eq ''A'' until input_eq []))) aand (label_eq ''2'' suntil input_eq [Num z_6, Str S7l_34,Str HTK,(Num 2)])))) suntil state_eq None) impl (input_eq [Num 31, Num q9a, Str ''0Z'', Str P9p]))) aand (state_eq (Some 2) until (state_eq None or (((((label_eq ''o'' or input_eq [])) until not (label_eq gY8__5 aand (((label_eq c253 until (input_eq [])) aand (not (((input_eq [] until ((label_eq ''v%'') aand alw (((((((((output_eq [None, Some N_5_3AC,((Some E_o7_Ya)),None]) or (output_eq [])) until label_eq ep2) impl (output_eq []))) aand (((input_eq [] suntil input_eq [Num n_9__5,(Str g_2), Str a9_29]) or (label_eq ER___B impl (((label_eq ''{U'') or input_eq []))))))) impl state_eq (Some 3)) aand input_eq [((Num 9))]))) or ((state_eq None aand (state_eq (Some 5) until input_eq [Num 846204, (((Num 41579)))])) impl (((((state_eq (Some 7252) or (label_eq t_2 suntil label_eq ''*'')) or (state_eq (Some 9) aand input_eq [Str ''$'']))) impl (label_eq u__B suntil (input_eq [Str ''{1'']))))))) aand output_eq [Some x_0, Some (Str q_i),((Some F___7)), Some (Str ''(s''),Some (Str ''x''), (Some (Str L_5)),((None))]))))) or state_eq None) until label_eq cg9z))))) aand output_eq []) (watch Ptp Gg5)" oops
lemma L19: "(label_eq lP2) (watch Vx___5 c__5)" oops
lemma W25: "state_eq (Some 0) (watch s_10_9 KnX)" oops
lemma Xhu: "label_eq ''d?'' (watch Y_5 Pf_A_V9)" oops
lemma SQt: "(output_eq [None,(Some (Str ''9X'')), (Some (Num 84)), Some (Num CE_3___P__D_U)]) (watch anDF j___2)" oops
lemma P1h_2w: "output_eq [Some (Num 1810)] (watch P2M A_Ap2x)" oops
lemma a_o: "(input_eq [] until (output_eq [Some (Str '',''),Some (Str k_6J2),Some JP_V] or (nxt ((label_eq bOn aand (((input_eq []) until (((output_eq [(Some h_LP), (Some n_3),None,(Some h_2K7)] until input_eq []) suntil ((label_eq H_43 or ((input_eq [((((Str BMf_53)))),Num 2,Num q_3]) impl label_eq V_4)) until output_eq []))))))) until output_eq [(Some (Str ''t'')), Some (Str x_85),(((((Some (Num s8y)))))),Some c_R,(None)]))) (watch lW_5Q05 c_e5)" oops
lemma Lry: "label_eq ''7'' (watch HLp di_V)" oops
lemma W8o: "(input_eq [(((((Str v7_7s_6))))),Str ''Z'', ((Num 0)), (Str T_d)] until ((label_eq ''*'' impl output_eq [Some F__5L, Some s9_9, Some (Num U__I)]) until output_eq [])) (watch O_4 h_h)" oops
lemma z_4: "ev (label_eq ''L!'') (watch K__g A7J)" oops
lemma o_2: "label_eq C_m (watch x__G3r Q__g)" oops
lemma Bm1: "((output_eq [None,Some rFgF]) impl state_eq None) (watch C_L3 zPu)" oops
lemma PJ072: "state_eq None (watch jo___v y_2)" oops
lemma U_G0: "(((label_eq ''d'' until (((state_eq (Some 4577) aand (state_eq (Some 0) or (not (((((((((((((label_eq P_01 or output_eq []) suntil (((((output_eq [] aand label_eq ''}V0'') impl ((label_eq ''!b5+t'' or (output_eq [Some (Num 053),(Some pk___2), (Some (Str ''p0''))] suntil input_eq [Num m__3_k_4,Num 0,(((Str c2QZu))), (Num 1), Num q2R,Str g_A]))))) suntil (((input_eq [] or input_eq [Num 4524495]) impl (not (((label_eq ''`'' until (label_eq Z6J__4vi impl label_eq ''?'')) suntil nxt (output_eq [])) suntil ((input_eq [] suntil (output_eq [(Some M__O)] impl state_eq None)) suntil nxt (state_eq None)))))))))) until (label_eq C_e__Qb aand input_eq []))) suntil input_eq [Num 0,(((Str p__O))),Num e_v, Str '':'',(((((Str d96)))))]) until (((((input_eq [(Num 6)]) or label_eq ''/'') until state_eq (Some 8)) until ((label_eq ''d4L'' aand (output_eq [])) or state_eq None))))) until label_eq '';'') until (((((input_eq [] suntil label_eq sQl___1) or (input_eq []))) impl (label_eq ''.l)B'')) impl input_eq [Num 0]))) or (state_eq None aand input_eq [])))))) until ((input_eq [] aand label_eq q_94) suntil (state_eq (Some 78)))))) impl state_eq (Some 06)) impl ev (input_eq [(((Num n_Z4))), ((Num F__P)), (Num 1)] until label_eq ''@'')) (watch OC_d RGv65)" oops
lemma j5yw: "output_eq [] (watch g_m6 x_D)" oops
lemma Q__7Gk: "input_eq [] (watch WoF RZS3)" oops
lemma ZO_g: "(output_eq [(Some H_22Y)] aand state_eq None) (watch j_a M_7)" oops
lemma b4Mi: "output_eq [] (watch Z_7 G_J)" oops
lemma c_1: "output_eq [Some sH9,Some (Num gN68w)] (watch q__i D4l3I_I3)" oops
lemma f_P: "state_eq (Some 71) (watch H3p T2d)" oops
lemma S_0: "state_eq None (watch wn0 f58gX)" oops
lemma z_J: "input_eq [((Str O_2)), ((((Str rTzv))))] (watch T______B_P a1o)" oops
lemma I_b: "(((label_eq T__2 or output_eq []) aand (state_eq None))) (watch mT3 B_w)" oops
lemma z__1__n: "input_eq [((Num 7)),((((Num o____G9)))),(Str ''-Z1''), Str d7aN] (watch z4__4 AfM)" oops
lemma Mg__7j: "((input_eq [] until (input_eq [(Str ''s'')] aand label_eq ''.'')) suntil (((input_eq [Num 6,((((Str M__0)))),(((((Str SDg))))), Num i2R_K] impl ev ((((state_eq None suntil (input_eq [] impl (label_eq ''B'' or nxt (input_eq [])))) until (label_eq sLO))) aand nxt (input_eq [(Str s_X__p), (((Num 0))), Num 8,((((Num 93794))))]))) or state_eq None) or (output_eq [Some C14,(((None)))] aand output_eq [Some (Num Z_y),(Some (Str y_3_t)),None,Some C_y, (None), Some D__4,None,None]))) (watch DQ_R v701am)" oops
lemma J_7U: "(alw (label_eq ''.'') suntil (alw (((not (not ((state_eq None suntil (((state_eq None) or ((output_eq [None] aand input_eq [(Num 3),Str ''6'']) impl output_eq [])))) until label_eq QBh))) or ((input_eq [] suntil output_eq [None,Some (Num 7), None, None,Some r_8C7, (None),None]) or not (((input_eq [] or label_eq ''`4X'') suntil (state_eq None until ((input_eq []) suntil output_eq []))))))))) (watch K_u6T8q__L Gn1)" oops
lemma U_p: "input_eq [Num 2693604,((Num 19)),Num 2] (watch v_e m81)" oops
lemma k7_5n: "label_eq ''F}'' (watch j_7 v_3)" oops
lemma L7_9o: "(output_eq [Some M_9_2,Some H_G,Some u_8]) (watch x_b fD_e8)" oops
lemma M_W: "input_eq [Str F_5O1, (Num V0Y_Y)] (watch o_D T_u_2_o3)" oops
lemma Y60: "input_eq [Num H_2] (watch x_Z96 r_AP)" oops
lemma tK_3: "label_eq ''Wg'' (watch V_b8 z_A)" oops
lemma A_M: "(input_eq [((((Str ICa8))))] or (label_eq i__fu or (input_eq [Num jO_8l, Str ''<%5_.''] suntil input_eq []))) (watch yZQ m__u)" oops
lemma R_6: "input_eq [((Str o96)), Str a4M8] (watch W_C L_H)" oops
lemma Y91r_j9: "(state_eq None suntil (input_eq [((Str l_5))] or (alw (label_eq i_1_q or (input_eq [((Str v35)), ((Str ''9'')), (Str ndu91), (((((Num a_E2)))))])) aand state_eq None))) (watch e__7 W369)" oops
lemma AW73: "(output_eq [Some x1_0, (Some (Str ''Y}4'')), None, (None)] or input_eq [(Str ''_''), Num M_r]) (watch d_a t_d)" oops
lemma A_F6: "output_eq [(None), None,(Some SrK), (Some kTV99),Some (Num e_p),(((None)))] (watch q_0 c_It)" oops
lemma R_wV7: "state_eq (Some 91) (watch C_s Fv1)" oops
lemma ey8: "(label_eq ''}'' until ((output_eq [] impl input_eq [Num CA_eT,Str ''`1'',Str a2z]))) (watch g_9S XYZ___f_F67q_Ji)" oops
lemma u_R: "(input_eq [] until ((((state_eq (Some 5) aand input_eq [Num 782]) impl state_eq None) until (input_eq [(((Num m97))),((Str ''U|;6 '')), ((Str ''f'')),(Num 5), (Str O_3_X_w), (Num Kld21),Num S_9C,(Str B_9)] suntil ((((state_eq None aand output_eq [Some (Str Z_9), Some t7F0W,Some c6M])) or (label_eq ''3.79%3'' suntil not (label_eq ''9D('')))))))) (watch sK3 I_3)" oops
lemma kh_f6fs0: "label_eq ''_'' (watch T_1 R6i)" oops
lemma I_O: "(state_eq (Some 0)) (watch R_2 wyQ)" oops
lemma Q_b: "(((((nxt (state_eq None) until (label_eq i_qc)) suntil output_eq []) aand output_eq []) impl (label_eq b_w until label_eq f_b6))) (watch pZ3 Y_2m0)" oops
lemma v_0: "state_eq (Some 7) (watch JK2 z8_Z0_x)" oops
lemma XK_P: "(((state_eq None) suntil output_eq []) until state_eq (Some 6)) (watch SQ9 dk_A)" oops
lemma t5_8: "label_eq F_e_d (watch c_2 YG__LU0)" oops
lemma F__O8: "((input_eq [Str W_X] until input_eq [(((Num 3))), (Num 5), Str u6__d]) impl state_eq (Some 8)) (watch M_43m d_f)" oops
lemma E_t: "((alw (label_eq Jo72J suntil (state_eq None suntil ((((state_eq None or (state_eq (Some 52) until input_eq [((Str ''6'')),Num 4])) until (((((((((input_eq [Num Iw9])) suntil output_eq []) until (((((((input_eq [] impl label_eq o_6) until label_eq ZH3__Th) suntil ((((output_eq [None]) suntil (label_eq G_Q or state_eq None))) impl label_eq ''8''))) or (output_eq []))) suntil label_eq d__N))) suntil (state_eq None impl (state_eq (Some 44) suntil (input_eq [] or (((((input_eq [] suntil label_eq N__T) suntil (output_eq [Some BX7,Some b_3]))) suntil ((label_eq b_93 until ((output_eq [] aand (label_eq ''|'')) aand label_eq Cg6)) aand output_eq [Some GP_82,(Some (Str ''a&''))])))))))) suntil (output_eq [Some (Num 6595),Some (Str ''6;!''), (Some u6X), (Some y_W), Some l_xj, (Some Fu4)] impl output_eq []))))) or state_eq (Some 4)))) or (state_eq (Some 777) aand input_eq [(((((Str ''!''))))), Str ''9*<'',Str R_J,(Str C_p), Num k18,Num rp33,((((Str ''8'')))), Str ''5'', Str b___4]))) (watch b59 N5O)" oops
lemma CO_D: "(output_eq []) (watch nd0_9_d HZ4_gA4MD_L__v)" oops
lemma Lg2: "(state_eq (Some 7)) (watch z_2 r5_a)" oops
lemma lZ_3a: "input_eq [] (watch SX0 P9i)" oops
lemma E_88O: "label_eq ''X`0'' (watch T3_3 N_1)" oops
lemma i__t: "output_eq [(None), None] (watch sIA8 t51vh)" oops
lemma v2__3: "output_eq [] (watch t_T y_k)" oops
lemma qNV: "(state_eq None or label_eq ''5N>26'') (watch k10C w__0)" oops
lemma I_65l6: "(((((output_eq [(None),Some (Str t_Jk),Some (Str ojI),(Some (Str S3__20))]) suntil (label_eq ''$-'' suntil state_eq (Some 47))) or (input_eq [] suntil state_eq (Some 6))) aand ((state_eq None suntil output_eq []) or output_eq []))) (watch L__4 J_7_C)" oops
lemma j4u: "(output_eq []) (watch W_9 SQ__0)" oops
lemma W__5: "(state_eq (Some 351)) (watch W052_C J5_0e)" oops
lemma qh2: "(((nxt (alw (label_eq ''C'')) aand (((((((label_eq ''&@6'' or (label_eq P0_3_3)) suntil (state_eq None))) aand (((input_eq [(Str i_2)] until output_eq []) impl (((state_eq None) or label_eq V_P) suntil label_eq w_pK1))))) impl input_eq []) until output_eq [None,Some Z_l_9, (None), None,Some nds])) aand label_eq u_m) impl label_eq ''.'') (watch V_o p5_M)" oops
lemma V_F: "((input_eq [] aand state_eq None) or output_eq [Some (Num i5U)]) (watch RF__U e_4)" oops
lemma D9T: "(label_eq ''0'' impl output_eq [Some uvhv8, Some (Str ''O''), Some (Num C__SWd), None]) (watch m3V w__y)" oops
lemma j_Km: "(((label_eq zeL) suntil (ev ((((label_eq t8_4o suntil output_eq []) or input_eq []) suntil (input_eq [((((Str O28)))), (Str ''<''),Num 6, Str v_b,((Str '':''))]))) or (label_eq ''H>B'' suntil (((input_eq [] impl output_eq [Some W_3, Some z2_m, None, None]) suntil (output_eq [] impl (label_eq ''B'' aand not (input_eq [Num 5, Str j_O, Str B__oC] until ((((((input_eq [])) or (state_eq (Some 020) impl state_eq (Some 3566)))) or state_eq (Some 13)) suntil (output_eq [] or state_eq None))))))))))) (watch z_hn t2_7)" oops
lemma q5K: "output_eq [] (watch X_u E___8)" oops
lemma x313: "(state_eq (Some 429030)) (watch tGA55 u17__5U)" oops
lemma O_Q: "((((((((input_eq [] impl ((output_eq [None]) or input_eq [])) aand output_eq [Some (Str ''%'')]) impl (not (label_eq i99Q or output_eq []) or state_eq None))) until (label_eq i_3I until (((input_eq [((Num D_0)), Num p_0,Num 8] impl label_eq ''D'') impl (label_eq CI1 impl (input_eq []))))))) aand ((((((ev ((nxt (((output_eq [] or label_eq ''G5'') until (((state_eq None) aand (nxt (output_eq [] suntil (label_eq ''!'' suntil (input_eq [Str ''3''] or ((nxt (((((((output_eq [] until output_eq [Some r83_0_X,((Some h72)),Some P1K, None, (Some s_4),Some (Str ''4-++=''), None,((Some f4f)),Some (Str ''-0''),Some p_P]) aand (label_eq D_2 or label_eq xv43)) or (((label_eq ''}Y'') until (((label_eq RM7 until state_eq None) until (state_eq (Some 976) or ((input_eq []) suntil output_eq []))) until state_eq None))))) until state_eq (Some 7)) impl (input_eq [Num 8, (Str d_9)] suntil ev (label_eq s_f impl state_eq (Some 8)))))) until input_eq [])))) aand (state_eq None aand ev (state_eq (Some 02) aand (state_eq None impl (((state_eq None impl output_eq []) impl (output_eq [])))))))))))) impl label_eq ''N'') impl (state_eq None aand (((input_eq [((((((((((Num 958)))))))))),Str rA0, (((Str x_6e4))), Num s_60]) aand (label_eq '')''))))) impl ((label_eq ''`'' or output_eq []) or state_eq None))) until output_eq [None]) aand ((((output_eq [(None)] aand label_eq ob_F___8) or (alw (output_eq [] until (output_eq []))))) or label_eq w_v))))) (watch RI1 C_2)" oops
lemma QVb: "((((((input_eq [(Str U_I_P5)]) aand (input_eq []))) impl (output_eq [] suntil ((((((input_eq [(((((Num Xu_11nP))))),((Str ''0'')),((((Str ''1 86`~'')))), (Num m_3E)] impl ((state_eq (Some 613298850) impl input_eq []) impl label_eq sctN0)) suntil (input_eq [Num k_9, Str GL4,Str ''/'', Num C31] aand (ev (((output_eq [])) impl output_eq []) suntil input_eq [Num 6,Str XVa2,(Str ''!'')]))) impl (label_eq v_c until label_eq ''`''))) or ((output_eq [] until label_eq l_0Hr) until ((state_eq None) suntil input_eq [])))))) or ((output_eq [] aand input_eq []) suntil state_eq (Some 2)))) (watch p_e L__s)" oops
lemma SuZ: "output_eq [] (watch f__s7 X__3)" oops
lemma L_6: "output_eq [] (watch o_R Q_6)" oops
lemma p__m: "input_eq [((Num 73)), ((Num 2))] (watch sDk U___8)" oops
lemma p__n: "(((state_eq None suntil state_eq (Some 5)) suntil (output_eq [Some (Str ''#C34''),(Some lnV), None] or label_eq h_d__m))) (watch I_7 V36I)" oops
lemma h_8: "((state_eq (Some 4) suntil alw (label_eq '' 3'')) impl state_eq None) (watch a625 GnJ3)" oops
lemma h81: "input_eq [((Num D94))] (watch w__50 n_3)" oops
lemma G__f: "(label_eq G4_2) (watch X_6 S4__9)" oops
lemma Q___4: "output_eq [Some (Str ''w*8''), (None),None] (watch rQM3 i1_p)" oops
lemma R_61: "(label_eq ''5'') (watch t94 p2BR)" oops
lemma T_a_7: "(label_eq ''.h.'' or (state_eq None aand input_eq [])) (watch suA g0m)" oops
lemma y_eF3w: "input_eq [] (watch n80 c_L)" oops
lemma M5_6: "state_eq (Some 03) (watch G_2 y__2)" oops
lemma I47: "(nxt ((((state_eq (Some 67) impl label_eq ro4) impl nxt (state_eq (Some 4))) until (ev (output_eq [Some Z4Z]) suntil input_eq [(Str K_B)])))) (watch SrfC9 Z_r)" oops
lemma zZ9: "((((((input_eq [(Num fK0), Str J_2]) suntil input_eq []) suntil ((((((output_eq [Some (Str k_0_3), (Some B3m), None, Some (Str S9_N1n3), Some (Num 9), Some s_a]) aand ((label_eq A_74) aand (((((state_eq (Some 359)) until label_eq k4pS) suntil output_eq []) until (label_eq E_5h or state_eq (Some 83))))))) aand (input_eq [] until label_eq M_2H)))))) until (input_eq [Str '';4/3'', (Str t_P)])) until (((input_eq [Str ''#'']) aand ((((label_eq ''7$'') impl input_eq []) suntil label_eq U_0D_y) impl ((output_eq [Some (Str o5s), None, (Some Cf_2_4Q), None,Some (Num k_h)] suntil ((((state_eq (Some 92) suntil (((((output_eq [(Some iqF), (Some c_6)] or (label_eq rQ8)) aand (state_eq (Some 81) or ((label_eq ''3'') or input_eq [(((((Num drx)))))])))) or (state_eq None)))) impl ((((input_eq [Num odx] until label_eq d0_l) impl state_eq (Some 48)) aand (input_eq []))))) suntil nxt (state_eq (Some 22) until (state_eq (Some 4) suntil output_eq [None, None])))) suntil label_eq Z_9))))) (watch t_0 v_G1)" oops
lemma G_FI: "((state_eq None or (state_eq None aand label_eq n77)) aand label_eq J_i) (watch i___2_O E6d_5)" oops
lemma L_f: "(((((((output_eq [Some (Str w400)]) impl (output_eq [] impl state_eq None))) aand ((((input_eq [] or (label_eq ''-/ #v4'' suntil (label_eq o0i_S14z7))) until (output_eq []))) suntil label_eq ''-''))) until output_eq []) aand label_eq ''>'') (watch sw4_17 Z2_M)" oops
lemma Q78: "state_eq (Some 6) (watch g_1 gji)" oops
lemma C7_6: "label_eq ''+5'' (watch ELo kdL)" oops
lemma P_0: "(input_eq [(((Num 79)))] aand (((output_eq [] suntil label_eq ''28'') until (label_eq ''/$%@ 3'' until (output_eq [Some M9i] until (((state_eq (Some 5) until (input_eq [] impl ((((((alw (((label_eq ''`'' aand (output_eq [] or state_eq (Some 1))) suntil (ev (input_eq [] impl (label_eq ''<e'')) or (output_eq [Some pB13,(Some (Num 72)), Some q_0] or input_eq [Str Y_n6o, Num W_1,Num k__k])))) until ev (output_eq [] or (((not ((((((output_eq [Some (Num SiY),(Some (Str v_G)),Some (Num z_G), Some WRJ, None,None,(None), None, None]) impl state_eq None) until output_eq []) until input_eq []) or (input_eq [Str h_6] or nxt (label_eq ''B'' until label_eq ''5'')))) aand label_eq ''}'') suntil (((input_eq [(Num 5),(Num BqS)] until (state_eq None suntil output_eq [None, Some vn8,(None),Some oE_9])) or (not ((((((state_eq (Some 28)) impl (output_eq [Some (Num D_4), Some (Str o_Z), Some Q_x, (None)] aand (state_eq None aand label_eq J9_h_0))) impl label_eq ''0CK'') aand ev ((((input_eq [(Num gfH)] impl state_eq None) aand (((state_eq None) impl output_eq [Some dU3]) impl label_eq ''{ ''))) aand label_eq ''/?#(3,@'')) suntil state_eq None) suntil input_eq [(((Str ''7,?''))), Num 128, Str ''3X 2'',Str '','',(((((Str ''_''))))),Num 5]))))))))) impl (label_eq zy_q or input_eq []))) impl ((state_eq (Some 5)) until output_eq [None, Some c_S,(Some JA__O),Some (Num p__J),Some y_t]))))) until ((label_eq V__6__s6) until output_eq [Some vO05j99,Some q_4, Some (Str ruu)])))))))) (watch G__3j xz0)" oops
lemma CWU: "label_eq ''A_'' (watch X__O W12)" oops
lemma H_5: "output_eq [] (watch W_2 L_F)" oops
lemma Qpt: "((((((((ev ((((((((label_eq C_6_xJ) suntil input_eq []) suntil (input_eq [] suntil ((((state_eq (Some 21)) aand label_eq ''!++qO6 I'') aand label_eq ''t= ''))))) aand ((((output_eq [None, (Some s4_5uC__0m),Some N383,Some q_1] impl ((output_eq []) until input_eq [Str b__Z, (Num 1)])) aand (label_eq ''!''))) impl label_eq euG))) suntil input_eq []) or state_eq None) suntil state_eq (Some 8016)) until (output_eq []))) until output_eq []) impl (input_eq [Num M99, ((((Num d_V4b))))] aand state_eq (Some 0)))) aand (label_eq ''v'' until not ((((((((((label_eq ''+'') suntil ((not (output_eq []) impl (ev (output_eq [] until ((state_eq None aand (state_eq (Some 86))) aand label_eq q0S)))) impl input_eq []))) until ((label_eq ''`A'' suntil (input_eq [Str EA60,Num w_sw] suntil output_eq [Some (Str d_0d9),(Some (Str N__y)),Some W_Z])) suntil input_eq [((Num 7)), ((((Num 0)))), (Str h_7kF1), ((((Str WN_9)))), (Num Q__9), (((Num th8p))), Str ''I'']))) aand output_eq [Some a10F, Some v_80,None, None, Some (Str M19_43)]) impl (alw (label_eq ''?^'' until output_eq [])))) aand (input_eq [Num 5, Str c__R_l4_2, (Str ''|'')])))))) (watch fc____k qG7)" oops
lemma vF2: "label_eq J_S (watch g5H Y_6)" oops
lemma R_7: "output_eq [None] (watch iGq hjY)" oops
lemma E6Y: "state_eq None (watch GbAR3 I_L)" oops
lemma D__S: "label_eq T_16 (watch Y__71___U8 E_1)" oops
lemma p34: "alw ((((((((ev (output_eq [] impl ((((state_eq None suntil (input_eq [(Str g__i77),Str Q_A,Str ''?'',(((Str d__V__W))), (Num 93), (Str ''i'')] aand (ev ((((state_eq None aand label_eq E7zB) or ((label_eq ng5 or label_eq gtH) suntil output_eq [None,Some (Str ''?_''),Some q___6__f]))) until input_eq [Str ''A'',((((Str x_M))))]) aand (input_eq [] or (state_eq (Some 8) or (((((((((label_eq eL_x aand (state_eq (Some 9461))) or (((((state_eq None or output_eq []) impl (state_eq (Some 5)))) impl ((output_eq []) impl nxt (state_eq (Some 316) or (((((state_eq None or input_eq []) suntil input_eq []) or label_eq E_O__6_1) aand (output_eq [] aand input_eq [Str ''_''])))))))) impl (output_eq [Some (Num fB__0Cz)] impl (output_eq [] aand (output_eq [None, (Some W_9_1)] or input_eq [(Num K22C), Str t_2]))))) until label_eq R___S) suntil ((state_eq (Some 19959)) impl output_eq [(Some (Str ''`''))]))) impl ((output_eq [(None)]) or label_eq ''7,~0'')))))))) suntil output_eq [None, None, Some (Num e_8_q),None, Some Lwo,None]) until (label_eq J_24 aand (((state_eq None) suntil ((output_eq [Some lYrI,Some m_3] suntil (label_eq ''Z_'' impl input_eq [])) or input_eq []))))))) or label_eq XW_oh8)) aand label_eq I__tU) or alw (label_eq ''{92J'' aand state_eq (Some 5))) impl (output_eq [] impl output_eq []))) suntil (output_eq [] impl alw (((label_eq ''6T'' or (state_eq None or (output_eq [Some (Str ''B'')] impl output_eq [((None))]))) aand label_eq ''7'') impl state_eq (Some 7))))) (watch a_4 R_S)" oops
lemma u2P: "input_eq [] (watch H_0 j8l3u_4_4)" oops
lemma k_6: "state_eq None (watch D_RF Iu_6)" oops
lemma u_0: "(output_eq [] until output_eq []) (watch E98 l_S)" oops
lemma gzW: "input_eq [Str ''@'', (((((Str ''&''))))), Num y__9,Str ''.'',(((Str kBE))),(Num 5), Num f_J] (watch M8cd_Q u___P_5)" oops
lemma S3_3: "(state_eq (Some 41) until (label_eq ''K'')) (watch ua6 Q72)" oops
lemma J_w: "state_eq (Some 4) (watch zZC o_27)" oops
lemma a_7: "ev (((((((state_eq (Some 26) impl (state_eq (Some 9))) suntil (input_eq [((Str d_77z)), ((((Num 5)))),Num 9]))) until input_eq []) aand state_eq (Some 53)) impl ((not (not (((output_eq []) until (((state_eq (Some 0) suntil state_eq None) suntil (label_eq N_X aand state_eq None))))) impl label_eq ''L(!e>408'') or state_eq None) or output_eq []))) (watch Ez__I a_U)" oops
lemma z____9: "ev ((label_eq V75e) or alw (((((not (state_eq (Some 3) suntil (label_eq V_3 impl ((((nxt (input_eq [] impl ((((output_eq [] until output_eq []) impl label_eq E01) aand output_eq [Some (Num 6),None,Some o__T]) suntil (input_eq [(Num 3), (((((Str ''_#`Yec'')))))] until input_eq [Str ''?'']))) aand ((input_eq []))) suntil (label_eq ''*7?4$'' aand (label_eq pG0_3)))) until (((state_eq None until (((nxt (state_eq None aand output_eq []) aand (input_eq [Num RKV6,Num 21, (Str s_p1), (Num J_6), Num 0, Num r_l,((((Num 53))))] or ((label_eq Q_26_7D until input_eq [Str M96]) aand state_eq None))) until (output_eq [] impl output_eq [])))) or input_eq [(Num u_P), Num 3,Num FJ_B, Str C82F, (Str x9i),((Num 2)),Num 4578416, ((Num 29)), Num z_5]) until label_eq ''>'')))) suntil (input_eq [Num 90,(Num 74), ((Str ''#'')),Num 25, (Num 2),Num 5] aand output_eq [])) until state_eq (Some 05)) aand state_eq (Some 534)) or label_eq y_U) aand state_eq (Some 147))) (watch IIk d_15)" oops
lemma r_X: "(input_eq [] suntil output_eq []) (watch x_g8Q V__j__o)" oops
lemma W9f5_O: "((((output_eq [Some s8x, Some j_1,Some (Num Q_t), None,(None)] until (label_eq H__77 until label_eq ''412,K>}N'')) suntil (state_eq None suntil output_eq [Some (Num n2_6),Some i_1m, Some u_1__U]))) aand label_eq ''a'') (watch DT7 jXt)" oops
lemma o_3: "state_eq None (watch y_8 S_M)" oops
lemma h4_7g: "input_eq [] (watch Oh7 DC6S9)" oops
lemma UI_4j: "((output_eq [] suntil (state_eq (Some 3) impl input_eq [(Str ''{I'')])) impl output_eq [None, (((Some o41P))), None,None]) (watch j75 hsR)" oops
lemma X7_18: "(((state_eq None) suntil (((input_eq [(Num S__2),Num a4i, Str ''}'', (Num 6)]) or (input_eq [Str ''|'',Str o__Z]))))) (watch lJ5 V_8)" oops
lemma S_V: "(input_eq [((Num a_G_5)),Str ''y?'',Str ''w_'', Str m_x] suntil ((((label_eq e_D impl (((state_eq (Some 285) or state_eq None) suntil (((label_eq w__9 or label_eq n0__V) until output_eq []) impl label_eq ''D'')))) impl (label_eq D_h_0 or output_eq [(Some (Num 618)), None, (None)])) suntil (state_eq None)))) (watch d__285 Y_F)" oops
lemma u3_46: "(state_eq None or (output_eq [] aand (state_eq (Some 72)))) (watch cvv N_6)" oops
lemma E_n: "output_eq [] (watch q_8 C65)" oops
lemma k_n: "((label_eq ''2`<'' or input_eq [((Str ''uj'')),(Str ''O''),(Str X_v)]) suntil ((input_eq [(((Str DyF))), ((Str ''7;'')),Str ''I2'',(Str ''o''),Str Dj4] impl label_eq H_38) impl label_eq ''*^9'')) (watch RkT__V K___Vs)" oops
lemma O8y: "(((alw ((((output_eq [((Some (Num Q54_j))), None,Some D5u, Some O_6,Some z__1x43, Some e8__60] suntil (label_eq wKv or label_eq ''&6'')) aand label_eq ''`*|5'') or (state_eq (Some 326) impl ((input_eq [Str PD0_y, ((((Str a2i)))),Num m__8,(((Num mH8))), Str u_7]) until alw (state_eq None or label_eq j_1E))))) until label_eq Bdo) until ((label_eq UH7_n) suntil label_eq '')''))) (watch yJE9 y__1)" oops
lemma r0J: "input_eq [Str ''f''] (watch P_0 g_1f)" oops
lemma R_X: "state_eq (Some 1) (watch N_T ea98z)" oops
lemma n_4: "(state_eq (Some 88) or ((input_eq [] suntil state_eq (Some 63)) aand label_eq ''r'')) (watch Z_9 c46)" oops
lemma E17: "(state_eq None) (watch H__4r N83)" oops
lemma o5_16__7: "state_eq None (watch aaT Q___7_2)" oops
lemma m_sr3: "label_eq ''((X0_'' (watch Z_N G88)" oops
lemma c7e: "label_eq ''-'' (watch e0l o_45)" oops
lemma O_Cx: "((input_eq [(Str Cw7), (((((Str I__f)))))] aand ((label_eq f__p until output_eq []) aand output_eq [None, Some (Str ''`%''), (None),Some St9,Some e__g,None,None])) or label_eq ''0'') (watch vSiY YK__l)" oops
lemma YTm: "(input_eq []) (watch L_j I_6b)" oops
lemma td4_S7: "state_eq (Some 806) (watch j013 R_Y)" oops
lemma i159_5: "(((state_eq None) until (input_eq []))) (watch Ab7_0XY0__S m__3)" oops
lemma G_T: "not (nxt (((input_eq [] aand state_eq (Some 76)) until ((output_eq [((None)),((None)), Some G0_1ba_I__i]) suntil state_eq (Some 67))) or (((((((input_eq [(Num 38),((Num 1627))] or (input_eq [])) until not (label_eq D1G or (input_eq []))) or (input_eq [] impl (state_eq (Some 4) impl input_eq [Num 42])))) until (input_eq [(Str '';'')]))) impl output_eq [Some Nx0])) aand ((label_eq ''2'' or (state_eq None impl (label_eq yg_y suntil input_eq []))) or (((output_eq [] until (input_eq [Num 793,(((((Num O__y2)))))])) until (input_eq [Str cHo]))))) (watch n_t B_0)" oops
lemma C____1: "((input_eq [(((Num m7_1)))]) aand output_eq [None]) (watch N55 tfE)" oops
lemma r_4: "(state_eq None impl input_eq [(((Num H_z))),Str ''0~'']) (watch y_Y09 T4p_s)" oops
lemma Y_N: "state_eq (Some 4691) (watch cL543 g__1)" oops
lemma Qq1: "(input_eq [Num 0409,(Num 077159),(Str ''SB''), Str ''JE0''] until label_eq ''N=|2'') (watch O__20I ACD)" oops
lemma s_h: "label_eq ''1'' (watch R4H605 zv99)" oops
lemma u5_e: "((state_eq None impl (output_eq [] impl ((state_eq None) or input_eq [Num q__0I]))) until state_eq (Some 7)) (watch I4___9 zh_0f)" oops
lemma f_8: "label_eq r__j_j (watch i045 H_Y)" oops
lemma P__2: "output_eq [] (watch rNq o__Q)" oops
lemma E6_0F: "alw (output_eq [None] until (((alw (output_eq [Some (Num 2)] or (ev (((label_eq '',6'' aand (ev (alw (((input_eq [] suntil (label_eq ''@nX'' until (output_eq [None] suntil ((label_eq ''0~c'' impl (alw ((label_eq gF__p_4) until state_eq None))) until state_eq (Some 8))))) aand (input_eq [Num T_5]))) impl state_eq (Some 7)) suntil (input_eq [Str Xu3, Num r8l1] impl (((((state_eq (Some 5) or state_eq None) impl (label_eq ''*'' aand state_eq (Some 773663)))) or ((not (input_eq [Str ''l'', Str ''4,({,''])) suntil ((output_eq [] impl label_eq S_NA) suntil state_eq None))))))) or label_eq H_s) impl label_eq pN__j5_4) until label_eq ''!'')) suntil output_eq [None, Some (Num 8338580), ((((Some (Str ''{'')))))]) until (label_eq A_0 until state_eq None)))) (watch cf__7 L_w)" oops
lemma Yf4: "(label_eq '',l'' suntil state_eq None) (watch F_2 e_9)" oops
lemma de_5: "label_eq kSh_9 (watch h21 x7_3t)" oops
lemma ZHL: "output_eq [(Some (Str hy3)), (Some F_4),Some (Num W_6), None, (Some b__ud)] (watch F9U b_t___1)" oops
lemma I2J: "label_eq r_O (watch e7j1 w__U)" oops
lemma A1_7: "(label_eq iEM or ((output_eq [Some (Str E_0_9)] aand (output_eq [] until label_eq ''_'')) impl (((output_eq [] or state_eq (Some 3)) until ((label_eq nPR impl (((output_eq [] until state_eq (Some 0869)) aand (((((((((((alw (output_eq [] impl input_eq [(((Num k07)))])) or (output_eq [((Some kT_z7)), (((Some GZr)))] impl output_eq []))) or state_eq None) or (label_eq p4980 or state_eq None))) or output_eq [Some (Str ''z9''), Some o_m]) or (output_eq [None, None,Some (Num G0gO)]))) suntil ((((output_eq [(Some C_g), Some bC3nx]) aand (state_eq (Some 010) suntil (output_eq [] suntil output_eq [Some u2_l,Some w_d,Some (Num zd1),Some (Num 0), None,Some lr__1, None, None,Some (Str V8B),Some (Num 9)])))) until ((((input_eq [((Num 7)),(Str i__1E)] aand (output_eq [] aand label_eq ''c0>0'')) until (state_eq None aand (((input_eq [Num JR_J, Str a_z,((Num pNV73))] aand ((label_eq '' '') aand output_eq [])))))) impl ((not (label_eq ''?|~S<`'' impl state_eq None) or ((input_eq []))) suntil state_eq None))))))))) until output_eq [None,(None)]))))) (watch T6_96 G5u)" oops
lemma My5: "(output_eq [] suntil (input_eq [])) (watch o_4 H_d)" oops
lemma RhIM: "alw (((output_eq [] suntil (label_eq ''{'' aand (label_eq ''I7G'' impl ((((label_eq Z_W_y until (state_eq None or ((((((state_eq (Some 55438) or (((state_eq None impl ev (state_eq (Some 3))) until state_eq None) until state_eq None)) until (((((ev ((input_eq [Str ''V^'',((Num G_x))] impl (input_eq [] until (input_eq [] or label_eq t_7))) impl alw ((((state_eq None aand (label_eq ''6'' aand (output_eq [(Some qRP)]))) until (((output_eq [Some (Num e__y), None, None] suntil state_eq None) until label_eq ''Y'') or not (((output_eq [] impl ((state_eq None))) until (input_eq [((Num p0x))]))))))))) aand input_eq []) impl (input_eq [((Str I_Z)), Num 0, Num a5e9,Num 2, Str l51_X,(Str ''8''), (((((Num WQ9_P)))))] or (state_eq None)))) until output_eq []))) until (label_eq ''Y4%O'' or output_eq [(None), Some (Num 5245), Some of6, None, Some B_8___B]))) until (label_eq ZR0)))) until ((state_eq None aand ev (((((((input_eq [Str lZ2_I,Str RX2,Str ''s.$,'', Str J14_N]) or (((output_eq [Some (Num 20),Some z_5, None, (None),Some YM00F,Some R_i] aand output_eq [(None), (Some (Str y0_G___5))]) impl (state_eq (Some 7) until input_eq []))))) impl state_eq None) or ((label_eq ''O'' or (((state_eq None) or label_eq G_4O))) or label_eq R_B1))) until (state_eq (Some 6)))) until alw (((((state_eq (Some 5736) until (((input_eq [Num e2d,Num 2, Str ''5'',Num k2X] or (output_eq [] or label_eq P8_T)) or (((label_eq x__3 aand (state_eq (Some 9) suntil input_eq [])) until (((label_eq ''&'' suntil input_eq [Str ''8+{-d'']) until (not (((not ((((label_eq ''0z'') suntil (output_eq [Some p_0, Some d704E,Some (Num 96)] until label_eq A_8_2))) until ev (output_eq [None] suntil input_eq [Str ''(#'']))) or (((input_eq [(Str ''8'')] aand input_eq [Num 98]) impl output_eq [None, (None)])))) impl label_eq ''0'')))))))) aand label_eq n_____f) impl (input_eq []))) aand label_eq '':*}gI'')))) until label_eq T__A0d)))) or (((not ((state_eq None aand label_eq ''%'') aand label_eq ''Gr'')) or (((output_eq []) impl (input_eq [(((((Num m_c))))), (((Num 9)))] suntil nxt (state_eq None)))))))) (watch GzZ__h o__6)" oops
lemma z_0: "label_eq eb_1 (watch T_8Q09 a_m)" oops
lemma J029: "((output_eq [Some Z___F]) impl ev (((state_eq None suntil (label_eq ''9%'')) aand (alw (input_eq [((Str ''D''))] until (state_eq None until state_eq None)) or (output_eq [Some (Str '':l'')] impl (((output_eq [] suntil output_eq []) until (state_eq (Some 0) or (output_eq []))))))))) (watch Wl5K EW5)" oops
lemma pw2_r: "(label_eq T2__3) (watch V_YC Ddy)" oops
lemma R__6: "((label_eq e_9) until state_eq (Some 483)) (watch R716 H4A)" oops
lemma C2AgD: "label_eq Mc_a (watch B_7 J_o)" oops
lemma y_f: "state_eq None (watch C____b s_8W5)" oops
lemma usd9: "state_eq (Some 3) (watch k73_4 O_63)" oops
lemma w_1G: "(((((((input_eq [((((Str ''$''))))]) until ((((((alw ((output_eq [None, Some H_p,None,Some (Str O_r), Some T_e, None,(((Some FJ6)))] aand (state_eq (Some 577503) suntil input_eq [])) suntil label_eq Lm2S96) aand (not (input_eq [Str ''}'']))) until (ev (output_eq [(None),(Some (Num 7)),Some (Num 632),(Some SGvI1), Some lP__02, (None), (((None))), Some (Str ''_3''),Some (Num g0y)] suntil state_eq (Some 8)) suntil (output_eq [Some LJ_8, Some (Num 53),(None), (Some c0_I),Some (Str ho1), Some s2q] impl ((label_eq f_2 suntil not (label_eq ''8<='')) suntil output_eq []))))) until input_eq []) aand (state_eq (Some 9) suntil label_eq F8e))))) suntil ev (state_eq (Some 93) or (state_eq None aand state_eq None)))) aand (state_eq (Some 0) suntil state_eq (Some 81604)))) (watch g_oi Hl6__8)" oops


end