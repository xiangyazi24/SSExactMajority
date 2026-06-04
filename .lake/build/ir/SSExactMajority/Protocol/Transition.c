// Lean compiler output
// Module: SSExactMajority.Protocol.Transition
// Imports: public import Init public meta import Init public import SSExactMajority.Defs.Protocol public import SSExactMajority.Protocol.State
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t lp_SSExactMajority_SSEM_instDecidableEqAnswer(uint8_t, uint8_t);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqRole(uint8_t, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqOpinion(uint8_t, uint8_t);
uint8_t lp_SSExactMajority_SSEM_agentOutput___redArg(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ceilHalf(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ceilHalf___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_opinionToAnswer(uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_opinionToAnswer___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap___redArg(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__decide(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__decide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__propagate(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__propagate___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__phase4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__phase4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Transition_0__SSEM_transitionPEM__prePhase4_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Transition_0__SSEM_transitionPEM__prePhase4_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Transition_0__SSEM_transitionPEM__prePhase4_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_outputPEM___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_outputPEM___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_outputPEM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_outputPEM___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_protocolPEM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ceilHalf(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_2_ = lean_unsigned_to_nat(1u);
v___x_3_ = lean_nat_add(v_n_1_, v___x_2_);
v___x_4_ = lean_nat_shiftr(v___x_3_, v___x_2_);
lean_dec(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ceilHalf___boxed(lean_object* v_n_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_SSExactMajority_SSEM_ceilHalf(v_n_5_);
lean_dec(v_n_5_);
return v_res_6_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_opinionToAnswer(uint8_t v_x_7_){
_start:
{
if (v_x_7_ == 0)
{
uint8_t v___x_8_; 
v___x_8_ = 2;
return v___x_8_;
}
else
{
uint8_t v___x_9_; 
v___x_9_ = 3;
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_opinionToAnswer___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_18__boxed_11_; uint8_t v_res_12_; lean_object* v_r_13_; 
v_x_18__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = lp_SSExactMajority_SSEM_opinionToAnswer(v_x_18__boxed_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4___redArg(lean_object* v_n_14_, lean_object* v_trank_15_, lean_object* v_rankDelta_16_, lean_object* v_s_u2080_17_, lean_object* v_s_u2081_18_){
_start:
{
lean_object* v___y_20_; lean_object* v___y_21_; uint8_t v___y_22_; uint8_t v___y_23_; uint8_t v___y_24_; lean_object* v___y_25_; lean_object* v___y_26_; lean_object* v___y_27_; uint8_t v___y_28_; uint8_t v___y_29_; uint8_t v___y_30_; lean_object* v___y_31_; lean_object* v___y_32_; lean_object* v___y_33_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v_fst_42_; lean_object* v_snd_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_220_; 
lean_inc_ref(v_s_u2081_18_);
lean_inc_ref(v_s_u2080_17_);
v___x_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_40_, 0, v_s_u2080_17_);
lean_ctor_set(v___x_40_, 1, v_s_u2081_18_);
v___x_41_ = lean_apply_1(v_rankDelta_16_, v___x_40_);
v_fst_42_ = lean_ctor_get(v___x_41_, 0);
v_snd_43_ = lean_ctor_get(v___x_41_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_220_ == 0)
{
v___x_45_ = v___x_41_;
v_isShared_46_ = v_isSharedCheck_220_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_snd_43_);
lean_inc(v_fst_42_);
lean_dec(v___x_41_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_220_;
goto v_resetjp_44_;
}
v___jp_19_:
{
uint8_t v___x_34_; 
v___x_34_ = lp_SSExactMajority_SSEM_instDecidableEqAnswer(v___y_28_, v___y_30_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; 
lean_dec(v___y_33_);
lean_dec(v___y_31_);
lean_dec(v___y_27_);
lean_dec(v___y_26_);
lean_dec(v___y_21_);
lean_dec(v___y_20_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v___y_25_);
lean_ctor_set(v___x_35_, 1, v___y_32_);
return v___x_35_;
}
else
{
if (v___y_24_ == 0)
{
if (v___x_34_ == 0)
{
lean_object* v___x_36_; 
lean_dec(v___y_33_);
lean_dec(v___y_31_);
lean_dec(v___y_27_);
lean_dec(v___y_26_);
lean_dec(v___y_21_);
lean_dec(v___y_20_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___y_25_);
lean_ctor_set(v___x_36_, 1, v___y_32_);
return v___x_36_;
}
else
{
lean_object* v___x_37_; lean_object* v___x_38_; 
lean_dec_ref(v___y_32_);
v___x_37_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_37_, 0, v___y_21_);
lean_ctor_set(v___x_37_, 1, v___y_26_);
lean_ctor_set(v___x_37_, 2, v___y_20_);
lean_ctor_set(v___x_37_, 3, v___y_33_);
lean_ctor_set(v___x_37_, 4, v___y_31_);
lean_ctor_set(v___x_37_, 5, v___y_27_);
lean_ctor_set_uint8(v___x_37_, sizeof(void*)*6, v___y_29_);
lean_ctor_set_uint8(v___x_37_, sizeof(void*)*6 + 1, v___y_23_);
lean_ctor_set_uint8(v___x_37_, sizeof(void*)*6 + 2, v___y_22_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___y_25_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
return v___x_38_;
}
}
else
{
lean_object* v___x_39_; 
lean_dec(v___y_33_);
lean_dec(v___y_31_);
lean_dec(v___y_27_);
lean_dec(v___y_26_);
lean_dec(v___y_21_);
lean_dec(v___y_20_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___y_25_);
lean_ctor_set(v___x_39_, 1, v___y_32_);
return v___x_39_;
}
}
}
v_resetjp_44_:
{
uint8_t v_role_47_; lean_object* v_rank_48_; uint8_t v_leader_49_; lean_object* v_resetcount_50_; lean_object* v_timer_51_; lean_object* v_children_52_; lean_object* v_errorcount_53_; lean_object* v_delaytimer_54_; uint8_t v___x_55_; lean_object* v___y_57_; lean_object* v___y_58_; uint8_t v___y_105_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_141_; lean_object* v___y_142_; lean_object* v___y_177_; uint8_t v___x_203_; 
v_role_47_ = lean_ctor_get_uint8(v_fst_42_, sizeof(void*)*6);
v_rank_48_ = lean_ctor_get(v_fst_42_, 0);
v_leader_49_ = lean_ctor_get_uint8(v_fst_42_, sizeof(void*)*6 + 1);
v_resetcount_50_ = lean_ctor_get(v_fst_42_, 1);
v_timer_51_ = lean_ctor_get(v_fst_42_, 2);
v_children_52_ = lean_ctor_get(v_fst_42_, 3);
v_errorcount_53_ = lean_ctor_get(v_fst_42_, 4);
v_delaytimer_54_ = lean_ctor_get(v_fst_42_, 5);
v___x_55_ = 0;
v___x_203_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_47_, v___x_55_);
if (v___x_203_ == 0)
{
v___y_177_ = v_fst_42_;
goto v___jp_176_;
}
else
{
uint8_t v_role_204_; uint8_t v___x_205_; 
v_role_204_ = lean_ctor_get_uint8(v_s_u2080_17_, sizeof(void*)*6);
v___x_205_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_204_, v___x_55_);
if (v___x_205_ == 0)
{
if (v___x_203_ == 0)
{
v___y_177_ = v_fst_42_;
goto v___jp_176_;
}
else
{
lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_213_; 
lean_inc(v_delaytimer_54_);
lean_inc(v_errorcount_53_);
lean_inc(v_children_52_);
lean_inc(v_timer_51_);
lean_inc(v_resetcount_50_);
lean_inc(v_rank_48_);
v_isSharedCheck_213_ = !lean_is_exclusive(v_fst_42_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; lean_object* v_unused_215_; lean_object* v_unused_216_; lean_object* v_unused_217_; lean_object* v_unused_218_; lean_object* v_unused_219_; 
v_unused_214_ = lean_ctor_get(v_fst_42_, 5);
lean_dec(v_unused_214_);
v_unused_215_ = lean_ctor_get(v_fst_42_, 4);
lean_dec(v_unused_215_);
v_unused_216_ = lean_ctor_get(v_fst_42_, 3);
lean_dec(v_unused_216_);
v_unused_217_ = lean_ctor_get(v_fst_42_, 2);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v_fst_42_, 1);
lean_dec(v_unused_218_);
v_unused_219_ = lean_ctor_get(v_fst_42_, 0);
lean_dec(v_unused_219_);
v___x_207_ = v_fst_42_;
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
else
{
lean_dec(v_fst_42_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
uint8_t v___x_209_; lean_object* v___x_211_; 
v___x_209_ = 0;
if (v_isShared_208_ == 0)
{
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_rank_48_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_resetcount_50_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_timer_51_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_children_52_);
lean_ctor_set(v_reuseFailAlloc_212_, 4, v_errorcount_53_);
lean_ctor_set(v_reuseFailAlloc_212_, 5, v_delaytimer_54_);
lean_ctor_set_uint8(v_reuseFailAlloc_212_, sizeof(void*)*6, v_role_47_);
lean_ctor_set_uint8(v_reuseFailAlloc_212_, sizeof(void*)*6 + 1, v_leader_49_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_ctor_set_uint8(v___x_211_, sizeof(void*)*6 + 2, v___x_209_);
v___y_177_ = v___x_211_;
goto v___jp_176_;
}
}
}
}
else
{
v___y_177_ = v_fst_42_;
goto v___jp_176_;
}
}
v___jp_56_:
{
uint8_t v_role_59_; lean_object* v_rank_60_; uint8_t v_leader_61_; lean_object* v_resetcount_62_; uint8_t v_answer_63_; lean_object* v_timer_64_; lean_object* v_children_65_; lean_object* v_errorcount_66_; lean_object* v_delaytimer_67_; uint8_t v___x_68_; 
v_role_59_ = lean_ctor_get_uint8(v___y_57_, sizeof(void*)*6);
v_rank_60_ = lean_ctor_get(v___y_57_, 0);
v_leader_61_ = lean_ctor_get_uint8(v___y_57_, sizeof(void*)*6 + 1);
v_resetcount_62_ = lean_ctor_get(v___y_57_, 1);
v_answer_63_ = lean_ctor_get_uint8(v___y_57_, sizeof(void*)*6 + 2);
v_timer_64_ = lean_ctor_get(v___y_57_, 2);
v_children_65_ = lean_ctor_get(v___y_57_, 3);
v_errorcount_66_ = lean_ctor_get(v___y_57_, 4);
v_delaytimer_67_ = lean_ctor_get(v___y_57_, 5);
v___x_68_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_59_, v___x_55_);
if (v___x_68_ == 0)
{
lean_object* v___x_70_; 
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 1, v___y_58_);
lean_ctor_set(v___x_45_, 0, v___y_57_);
v___x_70_ = v___x_45_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___y_57_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v___y_58_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
else
{
uint8_t v_role_72_; lean_object* v_rank_73_; uint8_t v_leader_74_; lean_object* v_resetcount_75_; uint8_t v_answer_76_; lean_object* v_timer_77_; lean_object* v_children_78_; lean_object* v_errorcount_79_; lean_object* v_delaytimer_80_; uint8_t v___x_81_; 
v_role_72_ = lean_ctor_get_uint8(v___y_58_, sizeof(void*)*6);
v_rank_73_ = lean_ctor_get(v___y_58_, 0);
v_leader_74_ = lean_ctor_get_uint8(v___y_58_, sizeof(void*)*6 + 1);
v_resetcount_75_ = lean_ctor_get(v___y_58_, 1);
v_answer_76_ = lean_ctor_get_uint8(v___y_58_, sizeof(void*)*6 + 2);
v_timer_77_ = lean_ctor_get(v___y_58_, 2);
v_children_78_ = lean_ctor_get(v___y_58_, 3);
v_errorcount_79_ = lean_ctor_get(v___y_58_, 4);
v_delaytimer_80_ = lean_ctor_get(v___y_58_, 5);
v___x_81_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_72_, v___x_55_);
if (v___x_81_ == 0)
{
lean_object* v___x_83_; 
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 1, v___y_58_);
lean_ctor_set(v___x_45_, 0, v___y_57_);
v___x_83_ = v___x_45_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___y_57_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v___y_58_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
else
{
uint8_t v___x_85_; uint8_t v___x_86_; 
v___x_85_ = 0;
v___x_86_ = lp_SSExactMajority_SSEM_instDecidableEqAnswer(v_answer_63_, v___x_85_);
if (v___x_86_ == 0)
{
lean_inc(v_delaytimer_80_);
lean_inc(v_errorcount_79_);
lean_inc(v_children_78_);
lean_inc(v_timer_77_);
lean_inc(v_resetcount_75_);
lean_inc(v_rank_73_);
lean_del_object(v___x_45_);
v___y_20_ = v_timer_77_;
v___y_21_ = v_rank_73_;
v___y_22_ = v_answer_63_;
v___y_23_ = v_leader_74_;
v___y_24_ = v___x_86_;
v___y_25_ = v___y_57_;
v___y_26_ = v_resetcount_75_;
v___y_27_ = v_delaytimer_80_;
v___y_28_ = v_answer_76_;
v___y_29_ = v_role_72_;
v___y_30_ = v___x_85_;
v___y_31_ = v_errorcount_79_;
v___y_32_ = v___y_58_;
v___y_33_ = v_children_78_;
goto v___jp_19_;
}
else
{
uint8_t v___x_87_; 
v___x_87_ = lp_SSExactMajority_SSEM_instDecidableEqAnswer(v_answer_76_, v___x_85_);
if (v___x_87_ == 0)
{
if (v___x_86_ == 0)
{
lean_inc(v_delaytimer_80_);
lean_inc(v_errorcount_79_);
lean_inc(v_children_78_);
lean_inc(v_timer_77_);
lean_inc(v_resetcount_75_);
lean_inc(v_rank_73_);
lean_del_object(v___x_45_);
v___y_20_ = v_timer_77_;
v___y_21_ = v_rank_73_;
v___y_22_ = v_answer_63_;
v___y_23_ = v_leader_74_;
v___y_24_ = v___x_86_;
v___y_25_ = v___y_57_;
v___y_26_ = v_resetcount_75_;
v___y_27_ = v_delaytimer_80_;
v___y_28_ = v_answer_76_;
v___y_29_ = v_role_72_;
v___y_30_ = v___x_85_;
v___y_31_ = v_errorcount_79_;
v___y_32_ = v___y_58_;
v___y_33_ = v_children_78_;
goto v___jp_19_;
}
else
{
lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_97_; 
lean_inc(v_delaytimer_67_);
lean_inc(v_errorcount_66_);
lean_inc(v_children_65_);
lean_inc(v_timer_64_);
lean_inc(v_resetcount_62_);
lean_inc(v_rank_60_);
v_isSharedCheck_97_ = !lean_is_exclusive(v___y_57_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; lean_object* v_unused_99_; lean_object* v_unused_100_; lean_object* v_unused_101_; lean_object* v_unused_102_; lean_object* v_unused_103_; 
v_unused_98_ = lean_ctor_get(v___y_57_, 5);
lean_dec(v_unused_98_);
v_unused_99_ = lean_ctor_get(v___y_57_, 4);
lean_dec(v_unused_99_);
v_unused_100_ = lean_ctor_get(v___y_57_, 3);
lean_dec(v_unused_100_);
v_unused_101_ = lean_ctor_get(v___y_57_, 2);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v___y_57_, 1);
lean_dec(v_unused_102_);
v_unused_103_ = lean_ctor_get(v___y_57_, 0);
lean_dec(v_unused_103_);
v___x_89_ = v___y_57_;
v_isShared_90_ = v_isSharedCheck_97_;
goto v_resetjp_88_;
}
else
{
lean_dec(v___y_57_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_97_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_rank_60_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_resetcount_62_);
lean_ctor_set(v_reuseFailAlloc_96_, 2, v_timer_64_);
lean_ctor_set(v_reuseFailAlloc_96_, 3, v_children_65_);
lean_ctor_set(v_reuseFailAlloc_96_, 4, v_errorcount_66_);
lean_ctor_set(v_reuseFailAlloc_96_, 5, v_delaytimer_67_);
lean_ctor_set_uint8(v_reuseFailAlloc_96_, sizeof(void*)*6, v_role_59_);
lean_ctor_set_uint8(v_reuseFailAlloc_96_, sizeof(void*)*6 + 1, v_leader_61_);
v___x_92_ = v_reuseFailAlloc_96_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_94_; 
lean_ctor_set_uint8(v___x_92_, sizeof(void*)*6 + 2, v_answer_76_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 1, v___y_58_);
lean_ctor_set(v___x_45_, 0, v___x_92_);
v___x_94_ = v___x_45_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___y_58_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
else
{
lean_inc(v_delaytimer_80_);
lean_inc(v_errorcount_79_);
lean_inc(v_children_78_);
lean_inc(v_timer_77_);
lean_inc(v_resetcount_75_);
lean_inc(v_rank_73_);
lean_del_object(v___x_45_);
v___y_20_ = v_timer_77_;
v___y_21_ = v_rank_73_;
v___y_22_ = v_answer_63_;
v___y_23_ = v_leader_74_;
v___y_24_ = v___x_86_;
v___y_25_ = v___y_57_;
v___y_26_ = v_resetcount_75_;
v___y_27_ = v_delaytimer_80_;
v___y_28_ = v_answer_76_;
v___y_29_ = v_role_72_;
v___y_30_ = v___x_85_;
v___y_31_ = v_errorcount_79_;
v___y_32_ = v___y_58_;
v___y_33_ = v_children_78_;
goto v___jp_19_;
}
}
}
}
}
v___jp_104_:
{
uint8_t v_role_108_; lean_object* v_rank_109_; uint8_t v_leader_110_; lean_object* v_resetcount_111_; uint8_t v_answer_112_; lean_object* v_children_113_; lean_object* v_errorcount_114_; lean_object* v_delaytimer_115_; uint8_t v___x_116_; 
v_role_108_ = lean_ctor_get_uint8(v___y_106_, sizeof(void*)*6);
v_rank_109_ = lean_ctor_get(v___y_106_, 0);
v_leader_110_ = lean_ctor_get_uint8(v___y_106_, sizeof(void*)*6 + 1);
v_resetcount_111_ = lean_ctor_get(v___y_106_, 1);
v_answer_112_ = lean_ctor_get_uint8(v___y_106_, sizeof(void*)*6 + 2);
v_children_113_ = lean_ctor_get(v___y_106_, 3);
v_errorcount_114_ = lean_ctor_get(v___y_106_, 4);
v_delaytimer_115_ = lean_ctor_get(v___y_106_, 5);
v___x_116_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_108_, v___y_105_);
if (v___x_116_ == 0)
{
lean_dec_ref(v_s_u2081_18_);
v___y_57_ = v___y_107_;
v___y_58_ = v___y_106_;
goto v___jp_56_;
}
else
{
uint8_t v_role_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_133_; 
v_role_117_ = lean_ctor_get_uint8(v_s_u2081_18_, sizeof(void*)*6);
v_isSharedCheck_133_ = !lean_is_exclusive(v_s_u2081_18_);
if (v_isSharedCheck_133_ == 0)
{
lean_object* v_unused_134_; lean_object* v_unused_135_; lean_object* v_unused_136_; lean_object* v_unused_137_; lean_object* v_unused_138_; lean_object* v_unused_139_; 
v_unused_134_ = lean_ctor_get(v_s_u2081_18_, 5);
lean_dec(v_unused_134_);
v_unused_135_ = lean_ctor_get(v_s_u2081_18_, 4);
lean_dec(v_unused_135_);
v_unused_136_ = lean_ctor_get(v_s_u2081_18_, 3);
lean_dec(v_unused_136_);
v_unused_137_ = lean_ctor_get(v_s_u2081_18_, 2);
lean_dec(v_unused_137_);
v_unused_138_ = lean_ctor_get(v_s_u2081_18_, 1);
lean_dec(v_unused_138_);
v_unused_139_ = lean_ctor_get(v_s_u2081_18_, 0);
lean_dec(v_unused_139_);
v___x_119_ = v_s_u2081_18_;
v_isShared_120_ = v_isSharedCheck_133_;
goto v_resetjp_118_;
}
else
{
lean_dec(v_s_u2081_18_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_133_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
uint8_t v___x_121_; 
v___x_121_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_117_, v___y_105_);
if (v___x_121_ == 0)
{
if (v___x_116_ == 0)
{
lean_del_object(v___x_119_);
v___y_57_ = v___y_107_;
v___y_58_ = v___y_106_;
goto v___jp_56_;
}
else
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = lean_nat_add(v_rank_109_, v___x_122_);
v___x_124_ = lp_SSExactMajority_SSEM_ceilHalf(v_n_14_);
v___x_125_ = lean_nat_dec_eq(v___x_123_, v___x_124_);
lean_dec(v___x_124_);
lean_dec(v___x_123_);
if (v___x_125_ == 0)
{
lean_del_object(v___x_119_);
v___y_57_ = v___y_107_;
v___y_58_ = v___y_106_;
goto v___jp_56_;
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
lean_inc(v_delaytimer_115_);
lean_inc(v_errorcount_114_);
lean_inc(v_children_113_);
lean_inc(v_resetcount_111_);
lean_inc(v_rank_109_);
lean_dec_ref(v___y_106_);
v___x_126_ = lean_unsigned_to_nat(7u);
v___x_127_ = lean_unsigned_to_nat(4u);
v___x_128_ = lean_nat_add(v_trank_15_, v___x_127_);
v___x_129_ = lean_nat_mul(v___x_126_, v___x_128_);
lean_dec(v___x_128_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 5, v_delaytimer_115_);
lean_ctor_set(v___x_119_, 4, v_errorcount_114_);
lean_ctor_set(v___x_119_, 3, v_children_113_);
lean_ctor_set(v___x_119_, 2, v___x_129_);
lean_ctor_set(v___x_119_, 1, v_resetcount_111_);
lean_ctor_set(v___x_119_, 0, v_rank_109_);
v___x_131_ = v___x_119_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_rank_109_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_resetcount_111_);
lean_ctor_set(v_reuseFailAlloc_132_, 2, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_132_, 3, v_children_113_);
lean_ctor_set(v_reuseFailAlloc_132_, 4, v_errorcount_114_);
lean_ctor_set(v_reuseFailAlloc_132_, 5, v_delaytimer_115_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*6, v_role_108_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*6 + 1, v_leader_110_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*6 + 2, v_answer_112_);
v___y_57_ = v___y_107_;
v___y_58_ = v___x_131_;
goto v___jp_56_;
}
}
}
}
else
{
lean_del_object(v___x_119_);
v___y_57_ = v___y_107_;
v___y_58_ = v___y_106_;
goto v___jp_56_;
}
}
}
}
v___jp_140_:
{
uint8_t v_role_143_; lean_object* v_rank_144_; uint8_t v_leader_145_; lean_object* v_resetcount_146_; uint8_t v_answer_147_; lean_object* v_children_148_; lean_object* v_errorcount_149_; lean_object* v_delaytimer_150_; uint8_t v___x_151_; uint8_t v___x_152_; 
v_role_143_ = lean_ctor_get_uint8(v___y_141_, sizeof(void*)*6);
v_rank_144_ = lean_ctor_get(v___y_141_, 0);
v_leader_145_ = lean_ctor_get_uint8(v___y_141_, sizeof(void*)*6 + 1);
v_resetcount_146_ = lean_ctor_get(v___y_141_, 1);
v_answer_147_ = lean_ctor_get_uint8(v___y_141_, sizeof(void*)*6 + 2);
v_children_148_ = lean_ctor_get(v___y_141_, 3);
v_errorcount_149_ = lean_ctor_get(v___y_141_, 4);
v_delaytimer_150_ = lean_ctor_get(v___y_141_, 5);
v___x_151_ = 1;
v___x_152_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_143_, v___x_151_);
if (v___x_152_ == 0)
{
lean_dec_ref(v_s_u2080_17_);
v___y_105_ = v___x_151_;
v___y_106_ = v___y_142_;
v___y_107_ = v___y_141_;
goto v___jp_104_;
}
else
{
uint8_t v_role_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_169_; 
v_role_153_ = lean_ctor_get_uint8(v_s_u2080_17_, sizeof(void*)*6);
v_isSharedCheck_169_ = !lean_is_exclusive(v_s_u2080_17_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; lean_object* v_unused_171_; lean_object* v_unused_172_; lean_object* v_unused_173_; lean_object* v_unused_174_; lean_object* v_unused_175_; 
v_unused_170_ = lean_ctor_get(v_s_u2080_17_, 5);
lean_dec(v_unused_170_);
v_unused_171_ = lean_ctor_get(v_s_u2080_17_, 4);
lean_dec(v_unused_171_);
v_unused_172_ = lean_ctor_get(v_s_u2080_17_, 3);
lean_dec(v_unused_172_);
v_unused_173_ = lean_ctor_get(v_s_u2080_17_, 2);
lean_dec(v_unused_173_);
v_unused_174_ = lean_ctor_get(v_s_u2080_17_, 1);
lean_dec(v_unused_174_);
v_unused_175_ = lean_ctor_get(v_s_u2080_17_, 0);
lean_dec(v_unused_175_);
v___x_155_ = v_s_u2080_17_;
v_isShared_156_ = v_isSharedCheck_169_;
goto v_resetjp_154_;
}
else
{
lean_dec(v_s_u2080_17_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_169_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
uint8_t v___x_157_; 
v___x_157_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_153_, v___x_151_);
if (v___x_157_ == 0)
{
if (v___x_152_ == 0)
{
lean_del_object(v___x_155_);
v___y_105_ = v___x_151_;
v___y_106_ = v___y_142_;
v___y_107_ = v___y_141_;
goto v___jp_104_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_158_ = lean_unsigned_to_nat(1u);
v___x_159_ = lean_nat_add(v_rank_144_, v___x_158_);
v___x_160_ = lp_SSExactMajority_SSEM_ceilHalf(v_n_14_);
v___x_161_ = lean_nat_dec_eq(v___x_159_, v___x_160_);
lean_dec(v___x_160_);
lean_dec(v___x_159_);
if (v___x_161_ == 0)
{
lean_del_object(v___x_155_);
v___y_105_ = v___x_151_;
v___y_106_ = v___y_142_;
v___y_107_ = v___y_141_;
goto v___jp_104_;
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
lean_inc(v_delaytimer_150_);
lean_inc(v_errorcount_149_);
lean_inc(v_children_148_);
lean_inc(v_resetcount_146_);
lean_inc(v_rank_144_);
lean_dec_ref(v___y_141_);
v___x_162_ = lean_unsigned_to_nat(7u);
v___x_163_ = lean_unsigned_to_nat(4u);
v___x_164_ = lean_nat_add(v_trank_15_, v___x_163_);
v___x_165_ = lean_nat_mul(v___x_162_, v___x_164_);
lean_dec(v___x_164_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 5, v_delaytimer_150_);
lean_ctor_set(v___x_155_, 4, v_errorcount_149_);
lean_ctor_set(v___x_155_, 3, v_children_148_);
lean_ctor_set(v___x_155_, 2, v___x_165_);
lean_ctor_set(v___x_155_, 1, v_resetcount_146_);
lean_ctor_set(v___x_155_, 0, v_rank_144_);
v___x_167_ = v___x_155_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_rank_144_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_resetcount_146_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_168_, 3, v_children_148_);
lean_ctor_set(v_reuseFailAlloc_168_, 4, v_errorcount_149_);
lean_ctor_set(v_reuseFailAlloc_168_, 5, v_delaytimer_150_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*6, v_role_143_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*6 + 1, v_leader_145_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*6 + 2, v_answer_147_);
v___y_105_ = v___x_151_;
v___y_106_ = v___y_142_;
v___y_107_ = v___x_167_;
goto v___jp_104_;
}
}
}
}
else
{
lean_del_object(v___x_155_);
v___y_105_ = v___x_151_;
v___y_106_ = v___y_142_;
v___y_107_ = v___y_141_;
goto v___jp_104_;
}
}
}
}
v___jp_176_:
{
uint8_t v_role_178_; lean_object* v_rank_179_; uint8_t v_leader_180_; lean_object* v_resetcount_181_; lean_object* v_timer_182_; lean_object* v_children_183_; lean_object* v_errorcount_184_; lean_object* v_delaytimer_185_; uint8_t v___x_186_; 
v_role_178_ = lean_ctor_get_uint8(v_snd_43_, sizeof(void*)*6);
v_rank_179_ = lean_ctor_get(v_snd_43_, 0);
v_leader_180_ = lean_ctor_get_uint8(v_snd_43_, sizeof(void*)*6 + 1);
v_resetcount_181_ = lean_ctor_get(v_snd_43_, 1);
v_timer_182_ = lean_ctor_get(v_snd_43_, 2);
v_children_183_ = lean_ctor_get(v_snd_43_, 3);
v_errorcount_184_ = lean_ctor_get(v_snd_43_, 4);
v_delaytimer_185_ = lean_ctor_get(v_snd_43_, 5);
v___x_186_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_178_, v___x_55_);
if (v___x_186_ == 0)
{
v___y_141_ = v___y_177_;
v___y_142_ = v_snd_43_;
goto v___jp_140_;
}
else
{
uint8_t v_role_187_; uint8_t v___x_188_; 
v_role_187_ = lean_ctor_get_uint8(v_s_u2081_18_, sizeof(void*)*6);
v___x_188_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_187_, v___x_55_);
if (v___x_188_ == 0)
{
if (v___x_186_ == 0)
{
v___y_141_ = v___y_177_;
v___y_142_ = v_snd_43_;
goto v___jp_140_;
}
else
{
lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_196_; 
lean_inc(v_delaytimer_185_);
lean_inc(v_errorcount_184_);
lean_inc(v_children_183_);
lean_inc(v_timer_182_);
lean_inc(v_resetcount_181_);
lean_inc(v_rank_179_);
v_isSharedCheck_196_ = !lean_is_exclusive(v_snd_43_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; lean_object* v_unused_198_; lean_object* v_unused_199_; lean_object* v_unused_200_; lean_object* v_unused_201_; lean_object* v_unused_202_; 
v_unused_197_ = lean_ctor_get(v_snd_43_, 5);
lean_dec(v_unused_197_);
v_unused_198_ = lean_ctor_get(v_snd_43_, 4);
lean_dec(v_unused_198_);
v_unused_199_ = lean_ctor_get(v_snd_43_, 3);
lean_dec(v_unused_199_);
v_unused_200_ = lean_ctor_get(v_snd_43_, 2);
lean_dec(v_unused_200_);
v_unused_201_ = lean_ctor_get(v_snd_43_, 1);
lean_dec(v_unused_201_);
v_unused_202_ = lean_ctor_get(v_snd_43_, 0);
lean_dec(v_unused_202_);
v___x_190_ = v_snd_43_;
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
else
{
lean_dec(v_snd_43_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
uint8_t v___x_192_; lean_object* v___x_194_; 
v___x_192_ = 0;
if (v_isShared_191_ == 0)
{
v___x_194_ = v___x_190_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_rank_179_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_resetcount_181_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_timer_182_);
lean_ctor_set(v_reuseFailAlloc_195_, 3, v_children_183_);
lean_ctor_set(v_reuseFailAlloc_195_, 4, v_errorcount_184_);
lean_ctor_set(v_reuseFailAlloc_195_, 5, v_delaytimer_185_);
lean_ctor_set_uint8(v_reuseFailAlloc_195_, sizeof(void*)*6, v_role_178_);
lean_ctor_set_uint8(v_reuseFailAlloc_195_, sizeof(void*)*6 + 1, v_leader_180_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*6 + 2, v___x_192_);
v___y_141_ = v___y_177_;
v___y_142_ = v___x_194_;
goto v___jp_140_;
}
}
}
}
else
{
v___y_141_ = v___y_177_;
v___y_142_ = v_snd_43_;
goto v___jp_140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4___redArg___boxed(lean_object* v_n_221_, lean_object* v_trank_222_, lean_object* v_rankDelta_223_, lean_object* v_s_u2080_224_, lean_object* v_s_u2081_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = lp_SSExactMajority_SSEM_transitionPEM__prePhase4___redArg(v_n_221_, v_trank_222_, v_rankDelta_223_, v_s_u2080_224_, v_s_u2081_225_);
lean_dec(v_trank_222_);
lean_dec(v_n_221_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4(lean_object* v_n_227_, lean_object* v_trank_228_, lean_object* v_rankDelta_229_, lean_object* v_s_u2080_230_, lean_object* v_s_u2081_231_, uint8_t v_x_u2080_232_, uint8_t v_x_u2081_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lp_SSExactMajority_SSEM_transitionPEM__prePhase4___redArg(v_n_227_, v_trank_228_, v_rankDelta_229_, v_s_u2080_230_, v_s_u2081_231_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__prePhase4___boxed(lean_object* v_n_235_, lean_object* v_trank_236_, lean_object* v_rankDelta_237_, lean_object* v_s_u2080_238_, lean_object* v_s_u2081_239_, lean_object* v_x_u2080_240_, lean_object* v_x_u2081_241_){
_start:
{
uint8_t v_x_u2080_boxed_242_; uint8_t v_x_u2081_boxed_243_; lean_object* v_res_244_; 
v_x_u2080_boxed_242_ = lean_unbox(v_x_u2080_240_);
v_x_u2081_boxed_243_ = lean_unbox(v_x_u2081_241_);
v_res_244_ = lp_SSExactMajority_SSEM_transitionPEM__prePhase4(v_n_235_, v_trank_236_, v_rankDelta_237_, v_s_u2080_238_, v_s_u2081_239_, v_x_u2080_boxed_242_, v_x_u2081_boxed_243_);
lean_dec(v_trank_236_);
lean_dec(v_n_235_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap___redArg(lean_object* v_a_u2080_245_, lean_object* v_a_u2081_246_, uint8_t v_x_u2080_247_, uint8_t v_x_u2081_248_){
_start:
{
lean_object* v_rank_249_; lean_object* v_rank_250_; uint8_t v___x_251_; 
v_rank_249_ = lean_ctor_get(v_a_u2080_245_, 0);
v_rank_250_ = lean_ctor_get(v_a_u2081_246_, 0);
v___x_251_ = lean_nat_dec_lt(v_rank_249_, v_rank_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v_a_u2080_245_);
lean_ctor_set(v___x_252_, 1, v_a_u2081_246_);
return v___x_252_;
}
else
{
uint8_t v___x_253_; uint8_t v___x_254_; 
v___x_253_ = 1;
v___x_254_ = lp_SSExactMajority_SSEM_instDecidableEqOpinion(v_x_u2080_247_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_a_u2080_245_);
lean_ctor_set(v___x_255_, 1, v_a_u2081_246_);
return v___x_255_;
}
else
{
uint8_t v___x_256_; uint8_t v___x_257_; 
v___x_256_ = 0;
v___x_257_ = lp_SSExactMajority_SSEM_instDecidableEqOpinion(v_x_u2081_248_, v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v_a_u2080_245_);
lean_ctor_set(v___x_258_, 1, v_a_u2081_246_);
return v___x_258_;
}
else
{
lean_object* v___x_259_; 
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v_a_u2081_246_);
lean_ctor_set(v___x_259_, 1, v_a_u2080_245_);
return v___x_259_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap___redArg___boxed(lean_object* v_a_u2080_260_, lean_object* v_a_u2081_261_, lean_object* v_x_u2080_262_, lean_object* v_x_u2081_263_){
_start:
{
uint8_t v_x_u2080_boxed_264_; uint8_t v_x_u2081_boxed_265_; lean_object* v_res_266_; 
v_x_u2080_boxed_264_ = lean_unbox(v_x_u2080_262_);
v_x_u2081_boxed_265_ = lean_unbox(v_x_u2081_263_);
v_res_266_ = lp_SSExactMajority_SSEM_phase4__swap___redArg(v_a_u2080_260_, v_a_u2081_261_, v_x_u2080_boxed_264_, v_x_u2081_boxed_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap(lean_object* v_n_267_, lean_object* v_a_u2080_268_, lean_object* v_a_u2081_269_, uint8_t v_x_u2080_270_, uint8_t v_x_u2081_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lp_SSExactMajority_SSEM_phase4__swap___redArg(v_a_u2080_268_, v_a_u2081_269_, v_x_u2080_270_, v_x_u2081_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__swap___boxed(lean_object* v_n_273_, lean_object* v_a_u2080_274_, lean_object* v_a_u2081_275_, lean_object* v_x_u2080_276_, lean_object* v_x_u2081_277_){
_start:
{
uint8_t v_x_u2080_boxed_278_; uint8_t v_x_u2081_boxed_279_; lean_object* v_res_280_; 
v_x_u2080_boxed_278_ = lean_unbox(v_x_u2080_276_);
v_x_u2081_boxed_279_ = lean_unbox(v_x_u2081_277_);
v_res_280_ = lp_SSExactMajority_SSEM_phase4__swap(v_n_273_, v_a_u2080_274_, v_a_u2081_275_, v_x_u2080_boxed_278_, v_x_u2081_boxed_279_);
lean_dec(v_n_273_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__decide(lean_object* v_n_281_, lean_object* v_b_u2080_282_, lean_object* v_b_u2081_283_, uint8_t v_x_u2080_284_, uint8_t v_x_u2081_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_286_ = lean_unsigned_to_nat(2u);
v___x_287_ = lean_nat_mod(v_n_281_, v___x_286_);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_nat_dec_eq(v___x_287_, v___x_288_);
lean_dec(v___x_287_);
if (v___x_289_ == 0)
{
uint8_t v_role_290_; lean_object* v_rank_291_; uint8_t v_leader_292_; lean_object* v_resetcount_293_; lean_object* v_timer_294_; lean_object* v_children_295_; lean_object* v_errorcount_296_; lean_object* v_delaytimer_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___y_302_; uint8_t v___x_329_; 
v_role_290_ = lean_ctor_get_uint8(v_b_u2080_282_, sizeof(void*)*6);
v_rank_291_ = lean_ctor_get(v_b_u2080_282_, 0);
v_leader_292_ = lean_ctor_get_uint8(v_b_u2080_282_, sizeof(void*)*6 + 1);
v_resetcount_293_ = lean_ctor_get(v_b_u2080_282_, 1);
v_timer_294_ = lean_ctor_get(v_b_u2080_282_, 2);
v_children_295_ = lean_ctor_get(v_b_u2080_282_, 3);
v_errorcount_296_ = lean_ctor_get(v_b_u2080_282_, 4);
v_delaytimer_297_ = lean_ctor_get(v_b_u2080_282_, 5);
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_add(v_rank_291_, v___x_298_);
v___x_300_ = lp_SSExactMajority_SSEM_ceilHalf(v_n_281_);
v___x_329_ = lean_nat_dec_eq(v___x_299_, v___x_300_);
lean_dec(v___x_299_);
if (v___x_329_ == 0)
{
v___y_302_ = v_b_u2080_282_;
goto v___jp_301_;
}
else
{
lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_337_; 
lean_inc(v_delaytimer_297_);
lean_inc(v_errorcount_296_);
lean_inc(v_children_295_);
lean_inc(v_timer_294_);
lean_inc(v_resetcount_293_);
lean_inc(v_rank_291_);
v_isSharedCheck_337_ = !lean_is_exclusive(v_b_u2080_282_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; lean_object* v_unused_339_; lean_object* v_unused_340_; lean_object* v_unused_341_; lean_object* v_unused_342_; lean_object* v_unused_343_; 
v_unused_338_ = lean_ctor_get(v_b_u2080_282_, 5);
lean_dec(v_unused_338_);
v_unused_339_ = lean_ctor_get(v_b_u2080_282_, 4);
lean_dec(v_unused_339_);
v_unused_340_ = lean_ctor_get(v_b_u2080_282_, 3);
lean_dec(v_unused_340_);
v_unused_341_ = lean_ctor_get(v_b_u2080_282_, 2);
lean_dec(v_unused_341_);
v_unused_342_ = lean_ctor_get(v_b_u2080_282_, 1);
lean_dec(v_unused_342_);
v_unused_343_ = lean_ctor_get(v_b_u2080_282_, 0);
lean_dec(v_unused_343_);
v___x_331_ = v_b_u2080_282_;
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
else
{
lean_dec(v_b_u2080_282_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
uint8_t v___x_333_; lean_object* v___x_335_; 
v___x_333_ = lp_SSExactMajority_SSEM_opinionToAnswer(v_x_u2080_284_);
if (v_isShared_332_ == 0)
{
v___x_335_ = v___x_331_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_rank_291_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_resetcount_293_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_timer_294_);
lean_ctor_set(v_reuseFailAlloc_336_, 3, v_children_295_);
lean_ctor_set(v_reuseFailAlloc_336_, 4, v_errorcount_296_);
lean_ctor_set(v_reuseFailAlloc_336_, 5, v_delaytimer_297_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*6, v_role_290_);
lean_ctor_set_uint8(v_reuseFailAlloc_336_, sizeof(void*)*6 + 1, v_leader_292_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*6 + 2, v___x_333_);
v___y_302_ = v___x_335_;
goto v___jp_301_;
}
}
}
v___jp_301_:
{
uint8_t v_role_303_; lean_object* v_rank_304_; uint8_t v_leader_305_; lean_object* v_resetcount_306_; lean_object* v_timer_307_; lean_object* v_children_308_; lean_object* v_errorcount_309_; lean_object* v_delaytimer_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_role_303_ = lean_ctor_get_uint8(v_b_u2081_283_, sizeof(void*)*6);
v_rank_304_ = lean_ctor_get(v_b_u2081_283_, 0);
v_leader_305_ = lean_ctor_get_uint8(v_b_u2081_283_, sizeof(void*)*6 + 1);
v_resetcount_306_ = lean_ctor_get(v_b_u2081_283_, 1);
v_timer_307_ = lean_ctor_get(v_b_u2081_283_, 2);
v_children_308_ = lean_ctor_get(v_b_u2081_283_, 3);
v_errorcount_309_ = lean_ctor_get(v_b_u2081_283_, 4);
v_delaytimer_310_ = lean_ctor_get(v_b_u2081_283_, 5);
v___x_311_ = lean_nat_add(v_rank_304_, v___x_298_);
v___x_312_ = lean_nat_dec_eq(v___x_311_, v___x_300_);
lean_dec(v___x_300_);
lean_dec(v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___y_302_);
lean_ctor_set(v___x_313_, 1, v_b_u2081_283_);
return v___x_313_;
}
else
{
lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_322_; 
lean_inc(v_delaytimer_310_);
lean_inc(v_errorcount_309_);
lean_inc(v_children_308_);
lean_inc(v_timer_307_);
lean_inc(v_resetcount_306_);
lean_inc(v_rank_304_);
v_isSharedCheck_322_ = !lean_is_exclusive(v_b_u2081_283_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; lean_object* v_unused_324_; lean_object* v_unused_325_; lean_object* v_unused_326_; lean_object* v_unused_327_; lean_object* v_unused_328_; 
v_unused_323_ = lean_ctor_get(v_b_u2081_283_, 5);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v_b_u2081_283_, 4);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_b_u2081_283_, 3);
lean_dec(v_unused_325_);
v_unused_326_ = lean_ctor_get(v_b_u2081_283_, 2);
lean_dec(v_unused_326_);
v_unused_327_ = lean_ctor_get(v_b_u2081_283_, 1);
lean_dec(v_unused_327_);
v_unused_328_ = lean_ctor_get(v_b_u2081_283_, 0);
lean_dec(v_unused_328_);
v___x_315_ = v_b_u2081_283_;
v_isShared_316_ = v_isSharedCheck_322_;
goto v_resetjp_314_;
}
else
{
lean_dec(v_b_u2081_283_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_322_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
uint8_t v___x_317_; lean_object* v___x_319_; 
v___x_317_ = lp_SSExactMajority_SSEM_opinionToAnswer(v_x_u2081_285_);
if (v_isShared_316_ == 0)
{
v___x_319_ = v___x_315_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_rank_304_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_resetcount_306_);
lean_ctor_set(v_reuseFailAlloc_321_, 2, v_timer_307_);
lean_ctor_set(v_reuseFailAlloc_321_, 3, v_children_308_);
lean_ctor_set(v_reuseFailAlloc_321_, 4, v_errorcount_309_);
lean_ctor_set(v_reuseFailAlloc_321_, 5, v_delaytimer_310_);
lean_ctor_set_uint8(v_reuseFailAlloc_321_, sizeof(void*)*6, v_role_303_);
lean_ctor_set_uint8(v_reuseFailAlloc_321_, sizeof(void*)*6 + 1, v_leader_305_);
v___x_319_ = v_reuseFailAlloc_321_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; 
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*6 + 2, v___x_317_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___y_302_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
return v___x_320_;
}
}
}
}
}
else
{
uint8_t v_role_344_; lean_object* v_rank_345_; uint8_t v_leader_346_; lean_object* v_resetcount_347_; lean_object* v_timer_348_; lean_object* v_children_349_; lean_object* v_errorcount_350_; lean_object* v_delaytimer_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_407_; 
v_role_344_ = lean_ctor_get_uint8(v_b_u2080_282_, sizeof(void*)*6);
v_rank_345_ = lean_ctor_get(v_b_u2080_282_, 0);
v_leader_346_ = lean_ctor_get_uint8(v_b_u2080_282_, sizeof(void*)*6 + 1);
v_resetcount_347_ = lean_ctor_get(v_b_u2080_282_, 1);
v_timer_348_ = lean_ctor_get(v_b_u2080_282_, 2);
v_children_349_ = lean_ctor_get(v_b_u2080_282_, 3);
v_errorcount_350_ = lean_ctor_get(v_b_u2080_282_, 4);
v_delaytimer_351_ = lean_ctor_get(v_b_u2080_282_, 5);
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_add(v_rank_345_, v___x_352_);
v___x_354_ = lean_nat_shiftr(v_n_281_, v___x_352_);
v___x_407_ = lean_nat_dec_eq(v___x_353_, v___x_354_);
if (v___x_407_ == 0)
{
goto v___jp_355_;
}
else
{
uint8_t v_role_408_; lean_object* v_rank_409_; uint8_t v_leader_410_; lean_object* v_resetcount_411_; lean_object* v_timer_412_; lean_object* v_children_413_; lean_object* v_errorcount_414_; lean_object* v_delaytimer_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v_role_408_ = lean_ctor_get_uint8(v_b_u2081_283_, sizeof(void*)*6);
v_rank_409_ = lean_ctor_get(v_b_u2081_283_, 0);
v_leader_410_ = lean_ctor_get_uint8(v_b_u2081_283_, sizeof(void*)*6 + 1);
v_resetcount_411_ = lean_ctor_get(v_b_u2081_283_, 1);
v_timer_412_ = lean_ctor_get(v_b_u2081_283_, 2);
v_children_413_ = lean_ctor_get(v_b_u2081_283_, 3);
v_errorcount_414_ = lean_ctor_get(v_b_u2081_283_, 4);
v_delaytimer_415_ = lean_ctor_get(v_b_u2081_283_, 5);
v___x_416_ = lean_nat_add(v_rank_409_, v___x_352_);
v___x_417_ = lean_nat_add(v___x_354_, v___x_352_);
v___x_418_ = lean_nat_dec_eq(v___x_416_, v___x_417_);
lean_dec(v___x_417_);
lean_dec(v___x_416_);
if (v___x_418_ == 0)
{
goto v___jp_355_;
}
else
{
lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_449_; 
lean_inc(v_delaytimer_415_);
lean_inc(v_errorcount_414_);
lean_inc(v_children_413_);
lean_inc(v_timer_412_);
lean_inc(v_resetcount_411_);
lean_inc(v_rank_409_);
lean_inc(v_delaytimer_351_);
lean_inc(v_errorcount_350_);
lean_inc(v_children_349_);
lean_inc(v_timer_348_);
lean_inc(v_resetcount_347_);
lean_inc(v_rank_345_);
lean_dec(v___x_354_);
lean_dec(v___x_353_);
v_isSharedCheck_449_ = !lean_is_exclusive(v_b_u2080_282_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; lean_object* v_unused_451_; lean_object* v_unused_452_; lean_object* v_unused_453_; lean_object* v_unused_454_; lean_object* v_unused_455_; 
v_unused_450_ = lean_ctor_get(v_b_u2080_282_, 5);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_b_u2080_282_, 4);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v_b_u2080_282_, 3);
lean_dec(v_unused_452_);
v_unused_453_ = lean_ctor_get(v_b_u2080_282_, 2);
lean_dec(v_unused_453_);
v_unused_454_ = lean_ctor_get(v_b_u2080_282_, 1);
lean_dec(v_unused_454_);
v_unused_455_ = lean_ctor_get(v_b_u2080_282_, 0);
lean_dec(v_unused_455_);
v___x_420_ = v_b_u2080_282_;
v_isShared_421_ = v_isSharedCheck_449_;
goto v_resetjp_419_;
}
else
{
lean_dec(v_b_u2080_282_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_449_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_442_; 
v_isSharedCheck_442_ = !lean_is_exclusive(v_b_u2081_283_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; lean_object* v_unused_444_; lean_object* v_unused_445_; lean_object* v_unused_446_; lean_object* v_unused_447_; lean_object* v_unused_448_; 
v_unused_443_ = lean_ctor_get(v_b_u2081_283_, 5);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_b_u2081_283_, 4);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_b_u2081_283_, 3);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_b_u2081_283_, 2);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v_b_u2081_283_, 1);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_b_u2081_283_, 0);
lean_dec(v_unused_448_);
v___x_423_ = v_b_u2081_283_;
v_isShared_424_ = v_isSharedCheck_442_;
goto v_resetjp_422_;
}
else
{
lean_dec(v_b_u2081_283_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_442_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
uint8_t v___x_425_; 
v___x_425_ = lp_SSExactMajority_SSEM_instDecidableEqOpinion(v_x_u2080_284_, v_x_u2081_285_);
if (v___x_425_ == 0)
{
uint8_t v___x_426_; lean_object* v___x_428_; 
v___x_426_ = 1;
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 5, v_delaytimer_351_);
lean_ctor_set(v___x_423_, 4, v_errorcount_350_);
lean_ctor_set(v___x_423_, 3, v_children_349_);
lean_ctor_set(v___x_423_, 2, v_timer_348_);
lean_ctor_set(v___x_423_, 1, v_resetcount_347_);
lean_ctor_set(v___x_423_, 0, v_rank_345_);
v___x_428_ = v___x_423_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_rank_345_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_resetcount_347_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_timer_348_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v_children_349_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v_errorcount_350_);
lean_ctor_set(v_reuseFailAlloc_433_, 5, v_delaytimer_351_);
v___x_428_ = v_reuseFailAlloc_433_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_430_; 
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*6, v_role_344_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*6 + 1, v_leader_346_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*6 + 2, v___x_426_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 5, v_delaytimer_415_);
lean_ctor_set(v___x_420_, 4, v_errorcount_414_);
lean_ctor_set(v___x_420_, 3, v_children_413_);
lean_ctor_set(v___x_420_, 2, v_timer_412_);
lean_ctor_set(v___x_420_, 1, v_resetcount_411_);
lean_ctor_set(v___x_420_, 0, v_rank_409_);
v___x_430_ = v___x_420_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_rank_409_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_resetcount_411_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_timer_412_);
lean_ctor_set(v_reuseFailAlloc_432_, 3, v_children_413_);
lean_ctor_set(v_reuseFailAlloc_432_, 4, v_errorcount_414_);
lean_ctor_set(v_reuseFailAlloc_432_, 5, v_delaytimer_415_);
v___x_430_ = v_reuseFailAlloc_432_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_431_; 
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*6, v_role_408_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*6 + 1, v_leader_410_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*6 + 2, v___x_426_);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_428_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
return v___x_431_;
}
}
}
else
{
uint8_t v___x_434_; lean_object* v___x_436_; 
v___x_434_ = lp_SSExactMajority_SSEM_opinionToAnswer(v_x_u2080_284_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 5, v_delaytimer_351_);
lean_ctor_set(v___x_423_, 4, v_errorcount_350_);
lean_ctor_set(v___x_423_, 3, v_children_349_);
lean_ctor_set(v___x_423_, 2, v_timer_348_);
lean_ctor_set(v___x_423_, 1, v_resetcount_347_);
lean_ctor_set(v___x_423_, 0, v_rank_345_);
v___x_436_ = v___x_423_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_rank_345_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_resetcount_347_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_timer_348_);
lean_ctor_set(v_reuseFailAlloc_441_, 3, v_children_349_);
lean_ctor_set(v_reuseFailAlloc_441_, 4, v_errorcount_350_);
lean_ctor_set(v_reuseFailAlloc_441_, 5, v_delaytimer_351_);
v___x_436_ = v_reuseFailAlloc_441_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_438_; 
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*6, v_role_344_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*6 + 1, v_leader_346_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*6 + 2, v___x_434_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 5, v_delaytimer_415_);
lean_ctor_set(v___x_420_, 4, v_errorcount_414_);
lean_ctor_set(v___x_420_, 3, v_children_413_);
lean_ctor_set(v___x_420_, 2, v_timer_412_);
lean_ctor_set(v___x_420_, 1, v_resetcount_411_);
lean_ctor_set(v___x_420_, 0, v_rank_409_);
v___x_438_ = v___x_420_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_rank_409_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_resetcount_411_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_timer_412_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_children_413_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v_errorcount_414_);
lean_ctor_set(v_reuseFailAlloc_440_, 5, v_delaytimer_415_);
v___x_438_ = v_reuseFailAlloc_440_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; 
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*6, v_role_408_);
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*6 + 1, v_leader_410_);
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*6 + 2, v___x_434_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_436_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
return v___x_439_;
}
}
}
}
}
}
}
v___jp_355_:
{
uint8_t v_role_356_; lean_object* v_rank_357_; uint8_t v_leader_358_; lean_object* v_resetcount_359_; lean_object* v_timer_360_; lean_object* v_children_361_; lean_object* v_errorcount_362_; lean_object* v_delaytimer_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v_role_356_ = lean_ctor_get_uint8(v_b_u2081_283_, sizeof(void*)*6);
v_rank_357_ = lean_ctor_get(v_b_u2081_283_, 0);
v_leader_358_ = lean_ctor_get_uint8(v_b_u2081_283_, sizeof(void*)*6 + 1);
v_resetcount_359_ = lean_ctor_get(v_b_u2081_283_, 1);
v_timer_360_ = lean_ctor_get(v_b_u2081_283_, 2);
v_children_361_ = lean_ctor_get(v_b_u2081_283_, 3);
v_errorcount_362_ = lean_ctor_get(v_b_u2081_283_, 4);
v_delaytimer_363_ = lean_ctor_get(v_b_u2081_283_, 5);
v___x_364_ = lean_nat_add(v_rank_357_, v___x_352_);
v___x_365_ = lean_nat_dec_eq(v___x_364_, v___x_354_);
lean_dec(v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec(v___x_354_);
lean_dec(v___x_353_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_b_u2080_282_);
lean_ctor_set(v___x_366_, 1, v_b_u2081_283_);
return v___x_366_;
}
else
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = lean_nat_add(v___x_354_, v___x_352_);
lean_dec(v___x_354_);
v___x_368_ = lean_nat_dec_eq(v___x_353_, v___x_367_);
lean_dec(v___x_367_);
lean_dec(v___x_353_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v_b_u2080_282_);
lean_ctor_set(v___x_369_, 1, v_b_u2081_283_);
return v___x_369_;
}
else
{
lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_400_; 
lean_inc(v_delaytimer_363_);
lean_inc(v_errorcount_362_);
lean_inc(v_children_361_);
lean_inc(v_timer_360_);
lean_inc(v_resetcount_359_);
lean_inc(v_rank_357_);
lean_inc(v_delaytimer_351_);
lean_inc(v_errorcount_350_);
lean_inc(v_children_349_);
lean_inc(v_timer_348_);
lean_inc(v_resetcount_347_);
lean_inc(v_rank_345_);
v_isSharedCheck_400_ = !lean_is_exclusive(v_b_u2080_282_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; lean_object* v_unused_402_; lean_object* v_unused_403_; lean_object* v_unused_404_; lean_object* v_unused_405_; lean_object* v_unused_406_; 
v_unused_401_ = lean_ctor_get(v_b_u2080_282_, 5);
lean_dec(v_unused_401_);
v_unused_402_ = lean_ctor_get(v_b_u2080_282_, 4);
lean_dec(v_unused_402_);
v_unused_403_ = lean_ctor_get(v_b_u2080_282_, 3);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_b_u2080_282_, 2);
lean_dec(v_unused_404_);
v_unused_405_ = lean_ctor_get(v_b_u2080_282_, 1);
lean_dec(v_unused_405_);
v_unused_406_ = lean_ctor_get(v_b_u2080_282_, 0);
lean_dec(v_unused_406_);
v___x_371_ = v_b_u2080_282_;
v_isShared_372_ = v_isSharedCheck_400_;
goto v_resetjp_370_;
}
else
{
lean_dec(v_b_u2080_282_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_400_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_393_; 
v_isSharedCheck_393_ = !lean_is_exclusive(v_b_u2081_283_);
if (v_isSharedCheck_393_ == 0)
{
lean_object* v_unused_394_; lean_object* v_unused_395_; lean_object* v_unused_396_; lean_object* v_unused_397_; lean_object* v_unused_398_; lean_object* v_unused_399_; 
v_unused_394_ = lean_ctor_get(v_b_u2081_283_, 5);
lean_dec(v_unused_394_);
v_unused_395_ = lean_ctor_get(v_b_u2081_283_, 4);
lean_dec(v_unused_395_);
v_unused_396_ = lean_ctor_get(v_b_u2081_283_, 3);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_b_u2081_283_, 2);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v_b_u2081_283_, 1);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v_b_u2081_283_, 0);
lean_dec(v_unused_399_);
v___x_374_ = v_b_u2081_283_;
v_isShared_375_ = v_isSharedCheck_393_;
goto v_resetjp_373_;
}
else
{
lean_dec(v_b_u2081_283_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_393_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
uint8_t v___x_376_; 
v___x_376_ = lp_SSExactMajority_SSEM_instDecidableEqOpinion(v_x_u2081_285_, v_x_u2080_284_);
if (v___x_376_ == 0)
{
uint8_t v___x_377_; lean_object* v___x_379_; 
v___x_377_ = 1;
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 5, v_delaytimer_351_);
lean_ctor_set(v___x_374_, 4, v_errorcount_350_);
lean_ctor_set(v___x_374_, 3, v_children_349_);
lean_ctor_set(v___x_374_, 2, v_timer_348_);
lean_ctor_set(v___x_374_, 1, v_resetcount_347_);
lean_ctor_set(v___x_374_, 0, v_rank_345_);
v___x_379_ = v___x_374_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_rank_345_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_resetcount_347_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v_timer_348_);
lean_ctor_set(v_reuseFailAlloc_384_, 3, v_children_349_);
lean_ctor_set(v_reuseFailAlloc_384_, 4, v_errorcount_350_);
lean_ctor_set(v_reuseFailAlloc_384_, 5, v_delaytimer_351_);
v___x_379_ = v_reuseFailAlloc_384_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_381_; 
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*6, v_role_344_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*6 + 1, v_leader_346_);
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*6 + 2, v___x_377_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 5, v_delaytimer_363_);
lean_ctor_set(v___x_371_, 4, v_errorcount_362_);
lean_ctor_set(v___x_371_, 3, v_children_361_);
lean_ctor_set(v___x_371_, 2, v_timer_360_);
lean_ctor_set(v___x_371_, 1, v_resetcount_359_);
lean_ctor_set(v___x_371_, 0, v_rank_357_);
v___x_381_ = v___x_371_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_rank_357_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_resetcount_359_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v_timer_360_);
lean_ctor_set(v_reuseFailAlloc_383_, 3, v_children_361_);
lean_ctor_set(v_reuseFailAlloc_383_, 4, v_errorcount_362_);
lean_ctor_set(v_reuseFailAlloc_383_, 5, v_delaytimer_363_);
v___x_381_ = v_reuseFailAlloc_383_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; 
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*6, v_role_356_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*6 + 1, v_leader_358_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*6 + 2, v___x_377_);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_379_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
return v___x_382_;
}
}
}
else
{
uint8_t v___x_385_; lean_object* v___x_387_; 
v___x_385_ = lp_SSExactMajority_SSEM_opinionToAnswer(v_x_u2081_285_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 5, v_delaytimer_351_);
lean_ctor_set(v___x_374_, 4, v_errorcount_350_);
lean_ctor_set(v___x_374_, 3, v_children_349_);
lean_ctor_set(v___x_374_, 2, v_timer_348_);
lean_ctor_set(v___x_374_, 1, v_resetcount_347_);
lean_ctor_set(v___x_374_, 0, v_rank_345_);
v___x_387_ = v___x_374_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_rank_345_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_resetcount_347_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v_timer_348_);
lean_ctor_set(v_reuseFailAlloc_392_, 3, v_children_349_);
lean_ctor_set(v_reuseFailAlloc_392_, 4, v_errorcount_350_);
lean_ctor_set(v_reuseFailAlloc_392_, 5, v_delaytimer_351_);
v___x_387_ = v_reuseFailAlloc_392_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_389_; 
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*6, v_role_344_);
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*6 + 1, v_leader_346_);
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*6 + 2, v___x_385_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 5, v_delaytimer_363_);
lean_ctor_set(v___x_371_, 4, v_errorcount_362_);
lean_ctor_set(v___x_371_, 3, v_children_361_);
lean_ctor_set(v___x_371_, 2, v_timer_360_);
lean_ctor_set(v___x_371_, 1, v_resetcount_359_);
lean_ctor_set(v___x_371_, 0, v_rank_357_);
v___x_389_ = v___x_371_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_rank_357_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_resetcount_359_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v_timer_360_);
lean_ctor_set(v_reuseFailAlloc_391_, 3, v_children_361_);
lean_ctor_set(v_reuseFailAlloc_391_, 4, v_errorcount_362_);
lean_ctor_set(v_reuseFailAlloc_391_, 5, v_delaytimer_363_);
v___x_389_ = v_reuseFailAlloc_391_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; 
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*6, v_role_356_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*6 + 1, v_leader_358_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*6 + 2, v___x_385_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_387_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
return v___x_390_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__decide___boxed(lean_object* v_n_456_, lean_object* v_b_u2080_457_, lean_object* v_b_u2081_458_, lean_object* v_x_u2080_459_, lean_object* v_x_u2081_460_){
_start:
{
uint8_t v_x_u2080_boxed_461_; uint8_t v_x_u2081_boxed_462_; lean_object* v_res_463_; 
v_x_u2080_boxed_461_ = lean_unbox(v_x_u2080_459_);
v_x_u2081_boxed_462_ = lean_unbox(v_x_u2081_460_);
v_res_463_ = lp_SSExactMajority_SSEM_phase4__decide(v_n_456_, v_b_u2080_457_, v_b_u2081_458_, v_x_u2080_boxed_461_, v_x_u2081_boxed_462_);
lean_dec(v_n_456_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__propagate(lean_object* v_n_464_, lean_object* v_Rmax_465_, lean_object* v_b_u2080_466_, lean_object* v_b_u2081_467_){
_start:
{
uint8_t v_role_468_; lean_object* v_rank_469_; uint8_t v_leader_470_; lean_object* v_resetcount_471_; uint8_t v_answer_472_; lean_object* v_timer_473_; lean_object* v_children_474_; lean_object* v_errorcount_475_; lean_object* v_delaytimer_476_; lean_object* v___y_478_; lean_object* v_rank_479_; uint8_t v_answer_480_; lean_object* v_timer_481_; lean_object* v_children_482_; lean_object* v_errorcount_483_; lean_object* v_delaytimer_484_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v_role_468_ = lean_ctor_get_uint8(v_b_u2080_466_, sizeof(void*)*6);
v_rank_469_ = lean_ctor_get(v_b_u2080_466_, 0);
v_leader_470_ = lean_ctor_get_uint8(v_b_u2080_466_, sizeof(void*)*6 + 1);
v_resetcount_471_ = lean_ctor_get(v_b_u2080_466_, 1);
v_answer_472_ = lean_ctor_get_uint8(v_b_u2080_466_, sizeof(void*)*6 + 2);
v_timer_473_ = lean_ctor_get(v_b_u2080_466_, 2);
v_children_474_ = lean_ctor_get(v_b_u2080_466_, 3);
v_errorcount_475_ = lean_ctor_get(v_b_u2080_466_, 4);
v_delaytimer_476_ = lean_ctor_get(v_b_u2080_466_, 5);
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = lean_nat_add(v_rank_469_, v___x_508_);
v___x_510_ = lp_SSExactMajority_SSEM_ceilHalf(v_n_464_);
v___x_511_ = lean_nat_dec_eq(v___x_509_, v___x_510_);
if (v___x_511_ == 0)
{
uint8_t v_role_512_; lean_object* v_rank_513_; uint8_t v_leader_514_; lean_object* v_resetcount_515_; uint8_t v_answer_516_; lean_object* v_timer_517_; lean_object* v_children_518_; lean_object* v_errorcount_519_; lean_object* v_delaytimer_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_role_512_ = lean_ctor_get_uint8(v_b_u2081_467_, sizeof(void*)*6);
v_rank_513_ = lean_ctor_get(v_b_u2081_467_, 0);
v_leader_514_ = lean_ctor_get_uint8(v_b_u2081_467_, sizeof(void*)*6 + 1);
v_resetcount_515_ = lean_ctor_get(v_b_u2081_467_, 1);
v_answer_516_ = lean_ctor_get_uint8(v_b_u2081_467_, sizeof(void*)*6 + 2);
v_timer_517_ = lean_ctor_get(v_b_u2081_467_, 2);
v_children_518_ = lean_ctor_get(v_b_u2081_467_, 3);
v_errorcount_519_ = lean_ctor_get(v_b_u2081_467_, 4);
v_delaytimer_520_ = lean_ctor_get(v_b_u2081_467_, 5);
v___x_521_ = lean_nat_add(v_rank_513_, v___x_508_);
v___x_522_ = lean_nat_dec_eq(v___x_521_, v___x_510_);
lean_dec(v___x_510_);
lean_dec(v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
lean_dec(v___x_509_);
lean_dec(v_Rmax_465_);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v_b_u2080_466_);
lean_ctor_set(v___x_523_, 1, v_b_u2081_467_);
return v___x_523_;
}
else
{
uint8_t v___x_524_; 
lean_inc(v_delaytimer_520_);
lean_inc(v_errorcount_519_);
lean_inc(v_children_518_);
lean_inc(v_timer_517_);
lean_inc(v_rank_513_);
v___x_524_ = lean_nat_dec_eq(v___x_509_, v_n_464_);
lean_dec(v___x_509_);
if (v___x_524_ == 0)
{
v___y_478_ = v_b_u2081_467_;
v_rank_479_ = v_rank_513_;
v_answer_480_ = v_answer_516_;
v_timer_481_ = v_timer_517_;
v_children_482_ = v_children_518_;
v_errorcount_483_ = v_errorcount_519_;
v_delaytimer_484_ = v_delaytimer_520_;
goto v___jp_477_;
}
else
{
lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_532_; 
lean_inc(v_resetcount_515_);
v_isSharedCheck_532_ = !lean_is_exclusive(v_b_u2081_467_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; lean_object* v_unused_534_; lean_object* v_unused_535_; lean_object* v_unused_536_; lean_object* v_unused_537_; lean_object* v_unused_538_; 
v_unused_533_ = lean_ctor_get(v_b_u2081_467_, 5);
lean_dec(v_unused_533_);
v_unused_534_ = lean_ctor_get(v_b_u2081_467_, 4);
lean_dec(v_unused_534_);
v_unused_535_ = lean_ctor_get(v_b_u2081_467_, 3);
lean_dec(v_unused_535_);
v_unused_536_ = lean_ctor_get(v_b_u2081_467_, 2);
lean_dec(v_unused_536_);
v_unused_537_ = lean_ctor_get(v_b_u2081_467_, 1);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_b_u2081_467_, 0);
lean_dec(v_unused_538_);
v___x_526_ = v_b_u2081_467_;
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
else
{
lean_dec(v_b_u2081_467_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = lean_nat_sub(v_timer_517_, v___x_508_);
lean_dec(v_timer_517_);
lean_inc(v_delaytimer_520_);
lean_inc(v_errorcount_519_);
lean_inc(v_children_518_);
lean_inc(v___x_528_);
lean_inc(v_rank_513_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 2, v___x_528_);
v___x_530_ = v___x_526_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_rank_513_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_resetcount_515_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_531_, 3, v_children_518_);
lean_ctor_set(v_reuseFailAlloc_531_, 4, v_errorcount_519_);
lean_ctor_set(v_reuseFailAlloc_531_, 5, v_delaytimer_520_);
lean_ctor_set_uint8(v_reuseFailAlloc_531_, sizeof(void*)*6, v_role_512_);
lean_ctor_set_uint8(v_reuseFailAlloc_531_, sizeof(void*)*6 + 1, v_leader_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_531_, sizeof(void*)*6 + 2, v_answer_516_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
v___y_478_ = v___x_530_;
v_rank_479_ = v_rank_513_;
v_answer_480_ = v_answer_516_;
v_timer_481_ = v___x_528_;
v_children_482_ = v_children_518_;
v_errorcount_483_ = v_errorcount_519_;
v_delaytimer_484_ = v_delaytimer_520_;
goto v___jp_477_;
}
}
}
}
}
else
{
lean_object* v_rank_539_; uint8_t v_answer_540_; lean_object* v_timer_541_; lean_object* v_children_542_; lean_object* v_errorcount_543_; lean_object* v_delaytimer_544_; lean_object* v___y_546_; lean_object* v_rank_547_; uint8_t v_answer_548_; lean_object* v_timer_549_; lean_object* v_children_550_; lean_object* v_errorcount_551_; lean_object* v_delaytimer_552_; lean_object* v___x_576_; uint8_t v___x_577_; 
lean_inc(v_delaytimer_476_);
lean_inc(v_errorcount_475_);
lean_inc(v_children_474_);
lean_inc(v_timer_473_);
lean_inc(v_rank_469_);
lean_dec(v___x_510_);
lean_dec(v___x_509_);
v_rank_539_ = lean_ctor_get(v_b_u2081_467_, 0);
v_answer_540_ = lean_ctor_get_uint8(v_b_u2081_467_, sizeof(void*)*6 + 2);
v_timer_541_ = lean_ctor_get(v_b_u2081_467_, 2);
v_children_542_ = lean_ctor_get(v_b_u2081_467_, 3);
v_errorcount_543_ = lean_ctor_get(v_b_u2081_467_, 4);
v_delaytimer_544_ = lean_ctor_get(v_b_u2081_467_, 5);
v___x_576_ = lean_nat_add(v_rank_539_, v___x_508_);
v___x_577_ = lean_nat_dec_eq(v___x_576_, v_n_464_);
lean_dec(v___x_576_);
if (v___x_577_ == 0)
{
v___y_546_ = v_b_u2080_466_;
v_rank_547_ = v_rank_469_;
v_answer_548_ = v_answer_472_;
v_timer_549_ = v_timer_473_;
v_children_550_ = v_children_474_;
v_errorcount_551_ = v_errorcount_475_;
v_delaytimer_552_ = v_delaytimer_476_;
goto v___jp_545_;
}
else
{
lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_585_; 
lean_inc(v_resetcount_471_);
v_isSharedCheck_585_ = !lean_is_exclusive(v_b_u2080_466_);
if (v_isSharedCheck_585_ == 0)
{
lean_object* v_unused_586_; lean_object* v_unused_587_; lean_object* v_unused_588_; lean_object* v_unused_589_; lean_object* v_unused_590_; lean_object* v_unused_591_; 
v_unused_586_ = lean_ctor_get(v_b_u2080_466_, 5);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_b_u2080_466_, 4);
lean_dec(v_unused_587_);
v_unused_588_ = lean_ctor_get(v_b_u2080_466_, 3);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v_b_u2080_466_, 2);
lean_dec(v_unused_589_);
v_unused_590_ = lean_ctor_get(v_b_u2080_466_, 1);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_b_u2080_466_, 0);
lean_dec(v_unused_591_);
v___x_579_ = v_b_u2080_466_;
v_isShared_580_ = v_isSharedCheck_585_;
goto v_resetjp_578_;
}
else
{
lean_dec(v_b_u2080_466_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_585_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_581_ = lean_nat_sub(v_timer_473_, v___x_508_);
lean_dec(v_timer_473_);
lean_inc(v_delaytimer_476_);
lean_inc(v_errorcount_475_);
lean_inc(v_children_474_);
lean_inc(v___x_581_);
lean_inc(v_rank_469_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 2, v___x_581_);
v___x_583_ = v___x_579_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_rank_469_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_resetcount_471_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_584_, 3, v_children_474_);
lean_ctor_set(v_reuseFailAlloc_584_, 4, v_errorcount_475_);
lean_ctor_set(v_reuseFailAlloc_584_, 5, v_delaytimer_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_584_, sizeof(void*)*6, v_role_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_584_, sizeof(void*)*6 + 1, v_leader_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_584_, sizeof(void*)*6 + 2, v_answer_472_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
v___y_546_ = v___x_583_;
v_rank_547_ = v_rank_469_;
v_answer_548_ = v_answer_472_;
v_timer_549_ = v___x_581_;
v_children_550_ = v_children_474_;
v_errorcount_551_ = v_errorcount_475_;
v_delaytimer_552_ = v_delaytimer_476_;
goto v___jp_545_;
}
}
}
v___jp_545_:
{
lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_nat_dec_eq(v_timer_549_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; 
lean_dec(v_delaytimer_552_);
lean_dec(v_errorcount_551_);
lean_dec(v_children_550_);
lean_dec(v_timer_549_);
lean_dec(v_rank_547_);
lean_dec(v_Rmax_465_);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v___y_546_);
lean_ctor_set(v___x_555_, 1, v_b_u2081_467_);
return v___x_555_;
}
else
{
uint8_t v___x_556_; 
v___x_556_ = lp_SSExactMajority_SSEM_instDecidableEqAnswer(v_answer_548_, v_answer_540_);
if (v___x_556_ == 0)
{
if (v___x_554_ == 0)
{
lean_object* v___x_557_; 
lean_dec(v_delaytimer_552_);
lean_dec(v_errorcount_551_);
lean_dec(v_children_550_);
lean_dec(v_timer_549_);
lean_dec(v_rank_547_);
lean_dec(v_Rmax_465_);
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v___y_546_);
lean_ctor_set(v___x_557_, 1, v_b_u2081_467_);
return v___x_557_;
}
else
{
lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_568_; 
lean_inc(v_delaytimer_544_);
lean_inc(v_errorcount_543_);
lean_inc(v_children_542_);
lean_inc(v_timer_541_);
lean_inc(v_rank_539_);
lean_dec_ref(v___y_546_);
v_isSharedCheck_568_ = !lean_is_exclusive(v_b_u2081_467_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; lean_object* v_unused_570_; lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; lean_object* v_unused_574_; 
v_unused_569_ = lean_ctor_get(v_b_u2081_467_, 5);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_b_u2081_467_, 4);
lean_dec(v_unused_570_);
v_unused_571_ = lean_ctor_get(v_b_u2081_467_, 3);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_b_u2081_467_, 2);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_b_u2081_467_, 1);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_b_u2081_467_, 0);
lean_dec(v_unused_574_);
v___x_559_ = v_b_u2081_467_;
v_isShared_560_ = v_isSharedCheck_568_;
goto v_resetjp_558_;
}
else
{
lean_dec(v_b_u2081_467_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_568_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
uint8_t v___x_561_; uint8_t v___x_562_; lean_object* v___x_564_; 
v___x_561_ = 0;
v___x_562_ = 0;
lean_inc(v_Rmax_465_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 5, v_delaytimer_552_);
lean_ctor_set(v___x_559_, 4, v_errorcount_551_);
lean_ctor_set(v___x_559_, 3, v_children_550_);
lean_ctor_set(v___x_559_, 2, v_timer_549_);
lean_ctor_set(v___x_559_, 1, v_Rmax_465_);
lean_ctor_set(v___x_559_, 0, v_rank_547_);
v___x_564_ = v___x_559_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_rank_547_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_Rmax_465_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_timer_549_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v_children_550_);
lean_ctor_set(v_reuseFailAlloc_567_, 4, v_errorcount_551_);
lean_ctor_set(v_reuseFailAlloc_567_, 5, v_delaytimer_552_);
v___x_564_ = v_reuseFailAlloc_567_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*6, v___x_561_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*6 + 1, v___x_562_);
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*6 + 2, v_answer_548_);
v___x_565_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_565_, 0, v_rank_539_);
lean_ctor_set(v___x_565_, 1, v_Rmax_465_);
lean_ctor_set(v___x_565_, 2, v_timer_541_);
lean_ctor_set(v___x_565_, 3, v_children_542_);
lean_ctor_set(v___x_565_, 4, v_errorcount_543_);
lean_ctor_set(v___x_565_, 5, v_delaytimer_544_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*6, v___x_561_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*6 + 1, v___x_562_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*6 + 2, v_answer_548_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
return v___x_566_;
}
}
}
}
else
{
lean_object* v___x_575_; 
lean_dec(v_delaytimer_552_);
lean_dec(v_errorcount_551_);
lean_dec(v_children_550_);
lean_dec(v_timer_549_);
lean_dec(v_rank_547_);
lean_dec(v_Rmax_465_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v___y_546_);
lean_ctor_set(v___x_575_, 1, v_b_u2081_467_);
return v___x_575_;
}
}
}
}
v___jp_477_:
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_nat_dec_eq(v_timer_481_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec(v_delaytimer_484_);
lean_dec(v_errorcount_483_);
lean_dec(v_children_482_);
lean_dec(v_timer_481_);
lean_dec(v_rank_479_);
lean_dec(v_Rmax_465_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v_b_u2080_466_);
lean_ctor_set(v___x_487_, 1, v___y_478_);
return v___x_487_;
}
else
{
uint8_t v___x_488_; 
v___x_488_ = lp_SSExactMajority_SSEM_instDecidableEqAnswer(v_answer_480_, v_answer_472_);
if (v___x_488_ == 0)
{
if (v___x_486_ == 0)
{
lean_object* v___x_489_; 
lean_dec(v_delaytimer_484_);
lean_dec(v_errorcount_483_);
lean_dec(v_children_482_);
lean_dec(v_timer_481_);
lean_dec(v_rank_479_);
lean_dec(v_Rmax_465_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v_b_u2080_466_);
lean_ctor_set(v___x_489_, 1, v___y_478_);
return v___x_489_;
}
else
{
lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_500_; 
lean_inc(v_delaytimer_476_);
lean_inc(v_errorcount_475_);
lean_inc(v_children_474_);
lean_inc(v_timer_473_);
lean_inc(v_rank_469_);
lean_dec_ref(v___y_478_);
v_isSharedCheck_500_ = !lean_is_exclusive(v_b_u2080_466_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; lean_object* v_unused_502_; lean_object* v_unused_503_; lean_object* v_unused_504_; lean_object* v_unused_505_; lean_object* v_unused_506_; 
v_unused_501_ = lean_ctor_get(v_b_u2080_466_, 5);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_b_u2080_466_, 4);
lean_dec(v_unused_502_);
v_unused_503_ = lean_ctor_get(v_b_u2080_466_, 3);
lean_dec(v_unused_503_);
v_unused_504_ = lean_ctor_get(v_b_u2080_466_, 2);
lean_dec(v_unused_504_);
v_unused_505_ = lean_ctor_get(v_b_u2080_466_, 1);
lean_dec(v_unused_505_);
v_unused_506_ = lean_ctor_get(v_b_u2080_466_, 0);
lean_dec(v_unused_506_);
v___x_491_ = v_b_u2080_466_;
v_isShared_492_ = v_isSharedCheck_500_;
goto v_resetjp_490_;
}
else
{
lean_dec(v_b_u2080_466_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_500_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
uint8_t v___x_493_; uint8_t v___x_494_; lean_object* v___x_496_; 
v___x_493_ = 0;
v___x_494_ = 0;
lean_inc(v_Rmax_465_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v_Rmax_465_);
v___x_496_ = v___x_491_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_rank_469_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_Rmax_465_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_timer_473_);
lean_ctor_set(v_reuseFailAlloc_499_, 3, v_children_474_);
lean_ctor_set(v_reuseFailAlloc_499_, 4, v_errorcount_475_);
lean_ctor_set(v_reuseFailAlloc_499_, 5, v_delaytimer_476_);
v___x_496_ = v_reuseFailAlloc_499_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*6, v___x_493_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*6 + 1, v___x_494_);
lean_ctor_set_uint8(v___x_496_, sizeof(void*)*6 + 2, v_answer_480_);
v___x_497_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_497_, 0, v_rank_479_);
lean_ctor_set(v___x_497_, 1, v_Rmax_465_);
lean_ctor_set(v___x_497_, 2, v_timer_481_);
lean_ctor_set(v___x_497_, 3, v_children_482_);
lean_ctor_set(v___x_497_, 4, v_errorcount_483_);
lean_ctor_set(v___x_497_, 5, v_delaytimer_484_);
lean_ctor_set_uint8(v___x_497_, sizeof(void*)*6, v___x_493_);
lean_ctor_set_uint8(v___x_497_, sizeof(void*)*6 + 1, v___x_494_);
lean_ctor_set_uint8(v___x_497_, sizeof(void*)*6 + 2, v_answer_480_);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
return v___x_498_;
}
}
}
}
else
{
lean_object* v___x_507_; 
lean_dec(v_delaytimer_484_);
lean_dec(v_errorcount_483_);
lean_dec(v_children_482_);
lean_dec(v_timer_481_);
lean_dec(v_rank_479_);
lean_dec(v_Rmax_465_);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v_b_u2080_466_);
lean_ctor_set(v___x_507_, 1, v___y_478_);
return v___x_507_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phase4__propagate___boxed(lean_object* v_n_592_, lean_object* v_Rmax_593_, lean_object* v_b_u2080_594_, lean_object* v_b_u2081_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = lp_SSExactMajority_SSEM_phase4__propagate(v_n_592_, v_Rmax_593_, v_b_u2080_594_, v_b_u2081_595_);
lean_dec(v_n_592_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__phase4(lean_object* v_n_597_, lean_object* v_Rmax_598_, lean_object* v_a_599_, uint8_t v_x_u2080_600_, uint8_t v_x_u2081_601_){
_start:
{
lean_object* v_fst_602_; lean_object* v_snd_603_; uint8_t v_role_604_; uint8_t v___x_605_; uint8_t v___x_606_; 
v_fst_602_ = lean_ctor_get(v_a_599_, 0);
v_snd_603_ = lean_ctor_get(v_a_599_, 1);
v_role_604_ = lean_ctor_get_uint8(v_fst_602_, sizeof(void*)*6);
v___x_605_ = 1;
v___x_606_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_604_, v___x_605_);
if (v___x_606_ == 0)
{
lean_dec(v_Rmax_598_);
return v_a_599_;
}
else
{
uint8_t v_role_607_; uint8_t v___x_608_; 
v_role_607_ = lean_ctor_get_uint8(v_snd_603_, sizeof(void*)*6);
v___x_608_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_607_, v___x_605_);
if (v___x_608_ == 0)
{
lean_dec(v_Rmax_598_);
return v_a_599_;
}
else
{
lean_object* v___x_609_; lean_object* v_fst_610_; lean_object* v_snd_611_; lean_object* v___x_612_; lean_object* v_fst_613_; lean_object* v_snd_614_; lean_object* v___x_615_; 
lean_inc(v_snd_603_);
lean_inc(v_fst_602_);
lean_dec_ref(v_a_599_);
v___x_609_ = lp_SSExactMajority_SSEM_phase4__swap___redArg(v_fst_602_, v_snd_603_, v_x_u2080_600_, v_x_u2081_601_);
v_fst_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_fst_610_);
v_snd_611_ = lean_ctor_get(v___x_609_, 1);
lean_inc(v_snd_611_);
lean_dec_ref(v___x_609_);
v___x_612_ = lp_SSExactMajority_SSEM_phase4__decide(v_n_597_, v_fst_610_, v_snd_611_, v_x_u2080_600_, v_x_u2081_601_);
v_fst_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_fst_613_);
v_snd_614_ = lean_ctor_get(v___x_612_, 1);
lean_inc(v_snd_614_);
lean_dec_ref(v___x_612_);
v___x_615_ = lp_SSExactMajority_SSEM_phase4__propagate(v_n_597_, v_Rmax_598_, v_fst_613_, v_snd_614_);
return v___x_615_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM__phase4___boxed(lean_object* v_n_616_, lean_object* v_Rmax_617_, lean_object* v_a_618_, lean_object* v_x_u2080_619_, lean_object* v_x_u2081_620_){
_start:
{
uint8_t v_x_u2080_boxed_621_; uint8_t v_x_u2081_boxed_622_; lean_object* v_res_623_; 
v_x_u2080_boxed_621_ = lean_unbox(v_x_u2080_619_);
v_x_u2081_boxed_622_ = lean_unbox(v_x_u2081_620_);
v_res_623_ = lp_SSExactMajority_SSEM_transitionPEM__phase4(v_n_616_, v_Rmax_617_, v_a_618_, v_x_u2080_boxed_621_, v_x_u2081_boxed_622_);
lean_dec(v_n_616_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Transition_0__SSEM_transitionPEM__prePhase4_match__1_splitter___redArg(lean_object* v_x_624_, lean_object* v_h__1_625_){
_start:
{
lean_object* v_fst_626_; lean_object* v_snd_627_; lean_object* v___x_628_; 
v_fst_626_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_fst_626_);
v_snd_627_ = lean_ctor_get(v_x_624_, 1);
lean_inc(v_snd_627_);
lean_dec_ref(v_x_624_);
v___x_628_ = lean_apply_2(v_h__1_625_, v_fst_626_, v_snd_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Transition_0__SSEM_transitionPEM__prePhase4_match__1_splitter(lean_object* v_n_629_, lean_object* v_motive_630_, lean_object* v_x_631_, lean_object* v_h__1_632_){
_start:
{
lean_object* v_fst_633_; lean_object* v_snd_634_; lean_object* v___x_635_; 
v_fst_633_ = lean_ctor_get(v_x_631_, 0);
lean_inc(v_fst_633_);
v_snd_634_ = lean_ctor_get(v_x_631_, 1);
lean_inc(v_snd_634_);
lean_dec_ref(v_x_631_);
v___x_635_ = lean_apply_2(v_h__1_632_, v_fst_633_, v_snd_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Protocol_Transition_0__SSEM_transitionPEM__prePhase4_match__1_splitter___boxed(lean_object* v_n_636_, lean_object* v_motive_637_, lean_object* v_x_638_, lean_object* v_h__1_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = lp_SSExactMajority___private_SSExactMajority_Protocol_Transition_0__SSEM_transitionPEM__prePhase4_match__1_splitter(v_n_636_, v_motive_637_, v_x_638_, v_h__1_639_);
lean_dec(v_n_636_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM(lean_object* v_n_641_, lean_object* v_trank_642_, lean_object* v_Rmax_643_, lean_object* v_rankDelta_644_, lean_object* v_x_645_){
_start:
{
lean_object* v_fst_646_; lean_object* v_snd_647_; lean_object* v_fst_648_; lean_object* v_snd_649_; lean_object* v_fst_650_; lean_object* v_snd_651_; lean_object* v___x_652_; uint8_t v___x_653_; uint8_t v___x_654_; lean_object* v___x_655_; 
v_fst_646_ = lean_ctor_get(v_x_645_, 0);
lean_inc(v_fst_646_);
v_snd_647_ = lean_ctor_get(v_x_645_, 1);
lean_inc(v_snd_647_);
lean_dec_ref(v_x_645_);
v_fst_648_ = lean_ctor_get(v_fst_646_, 0);
lean_inc(v_fst_648_);
v_snd_649_ = lean_ctor_get(v_fst_646_, 1);
lean_inc(v_snd_649_);
lean_dec(v_fst_646_);
v_fst_650_ = lean_ctor_get(v_snd_647_, 0);
lean_inc(v_fst_650_);
v_snd_651_ = lean_ctor_get(v_snd_647_, 1);
lean_inc(v_snd_651_);
lean_dec(v_snd_647_);
v___x_652_ = lp_SSExactMajority_SSEM_transitionPEM__prePhase4___redArg(v_n_641_, v_trank_642_, v_rankDelta_644_, v_fst_648_, v_fst_650_);
v___x_653_ = lean_unbox(v_snd_649_);
lean_dec(v_snd_649_);
v___x_654_ = lean_unbox(v_snd_651_);
lean_dec(v_snd_651_);
v___x_655_ = lp_SSExactMajority_SSEM_transitionPEM__phase4(v_n_641_, v_Rmax_643_, v___x_652_, v___x_653_, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_transitionPEM___boxed(lean_object* v_n_656_, lean_object* v_trank_657_, lean_object* v_Rmax_658_, lean_object* v_rankDelta_659_, lean_object* v_x_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = lp_SSExactMajority_SSEM_transitionPEM(v_n_656_, v_trank_657_, v_Rmax_658_, v_rankDelta_659_, v_x_660_);
lean_dec(v_trank_657_);
lean_dec(v_n_656_);
return v_res_661_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_outputPEM___redArg(lean_object* v_x_662_){
_start:
{
lean_object* v_fst_663_; uint8_t v___x_664_; 
v_fst_663_ = lean_ctor_get(v_x_662_, 0);
v___x_664_ = lp_SSExactMajority_SSEM_agentOutput___redArg(v_fst_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_outputPEM___redArg___boxed(lean_object* v_x_665_){
_start:
{
uint8_t v_res_666_; lean_object* v_r_667_; 
v_res_666_ = lp_SSExactMajority_SSEM_outputPEM___redArg(v_x_665_);
lean_dec_ref(v_x_665_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_outputPEM(lean_object* v_n_668_, lean_object* v_x_669_){
_start:
{
uint8_t v___x_670_; 
v___x_670_ = lp_SSExactMajority_SSEM_outputPEM___redArg(v_x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_outputPEM___boxed(lean_object* v_n_671_, lean_object* v_x_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = lp_SSExactMajority_SSEM_outputPEM(v_n_671_, v_x_672_);
lean_dec_ref(v_x_672_);
lean_dec(v_n_671_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_protocolPEM(lean_object* v_n_675_, lean_object* v_trank_676_, lean_object* v_Rmax_677_, lean_object* v_rankDelta_678_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
lean_inc(v_n_675_);
v___x_679_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_transitionPEM___boxed), 5, 4);
lean_closure_set(v___x_679_, 0, v_n_675_);
lean_closure_set(v___x_679_, 1, v_trank_676_);
lean_closure_set(v___x_679_, 2, v_Rmax_677_);
lean_closure_set(v___x_679_, 3, v_rankDelta_678_);
v___x_680_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_outputPEM___boxed), 2, 1);
lean_closure_set(v___x_680_, 0, v_n_675_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
return v___x_681_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Protocol(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_State(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_Transition(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Defs_Protocol(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Protocol_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
