// Lean compiler output
// Module: SSExactMajority.Protocol.RankDelta
// Imports: public import Init public meta import Init public import SSExactMajority.Protocol.State public import SSExactMajority.Convergence.Silent
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
uint8_t lp_SSExactMajority_SSEM_instDecidableEqRole(uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqLeader(uint8_t, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetOSSR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetOSSR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetOSSR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_propagateReset___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_propagateReset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_propagateReset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetOSSR___redArg(lean_object* v_Emax_1_, lean_object* v_s_2_){
_start:
{
uint8_t v_leader_3_; 
v_leader_3_ = lean_ctor_get_uint8(v_s_2_, sizeof(void*)*6 + 1);
if (v_leader_3_ == 0)
{
lean_object* v_resetcount_4_; uint8_t v_answer_5_; lean_object* v_timer_6_; lean_object* v_errorcount_7_; lean_object* v_delaytimer_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_17_; 
lean_dec(v_Emax_1_);
v_resetcount_4_ = lean_ctor_get(v_s_2_, 1);
v_answer_5_ = lean_ctor_get_uint8(v_s_2_, sizeof(void*)*6 + 2);
v_timer_6_ = lean_ctor_get(v_s_2_, 2);
v_errorcount_7_ = lean_ctor_get(v_s_2_, 4);
v_delaytimer_8_ = lean_ctor_get(v_s_2_, 5);
v_isSharedCheck_17_ = !lean_is_exclusive(v_s_2_);
if (v_isSharedCheck_17_ == 0)
{
lean_object* v_unused_18_; lean_object* v_unused_19_; 
v_unused_18_ = lean_ctor_get(v_s_2_, 3);
lean_dec(v_unused_18_);
v_unused_19_ = lean_ctor_get(v_s_2_, 0);
lean_dec(v_unused_19_);
v___x_10_ = v_s_2_;
v_isShared_11_ = v_isSharedCheck_17_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_delaytimer_8_);
lean_inc(v_errorcount_7_);
lean_inc(v_timer_6_);
lean_inc(v_resetcount_4_);
lean_dec(v_s_2_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_17_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
uint8_t v___x_12_; lean_object* v___x_13_; lean_object* v___x_15_; 
v___x_12_ = 1;
v___x_13_ = lean_unsigned_to_nat(0u);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 3, v___x_13_);
lean_ctor_set(v___x_10_, 0, v___x_13_);
v___x_15_ = v___x_10_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v___x_13_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v_resetcount_4_);
lean_ctor_set(v_reuseFailAlloc_16_, 2, v_timer_6_);
lean_ctor_set(v_reuseFailAlloc_16_, 3, v___x_13_);
lean_ctor_set(v_reuseFailAlloc_16_, 4, v_errorcount_7_);
lean_ctor_set(v_reuseFailAlloc_16_, 5, v_delaytimer_8_);
lean_ctor_set_uint8(v_reuseFailAlloc_16_, sizeof(void*)*6 + 1, v_leader_3_);
lean_ctor_set_uint8(v_reuseFailAlloc_16_, sizeof(void*)*6 + 2, v_answer_5_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
lean_ctor_set_uint8(v___x_15_, sizeof(void*)*6, v___x_12_);
return v___x_15_;
}
}
}
else
{
lean_object* v_rank_20_; lean_object* v_resetcount_21_; uint8_t v_answer_22_; lean_object* v_timer_23_; lean_object* v_children_24_; lean_object* v_delaytimer_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_33_; 
v_rank_20_ = lean_ctor_get(v_s_2_, 0);
v_resetcount_21_ = lean_ctor_get(v_s_2_, 1);
v_answer_22_ = lean_ctor_get_uint8(v_s_2_, sizeof(void*)*6 + 2);
v_timer_23_ = lean_ctor_get(v_s_2_, 2);
v_children_24_ = lean_ctor_get(v_s_2_, 3);
v_delaytimer_25_ = lean_ctor_get(v_s_2_, 5);
v_isSharedCheck_33_ = !lean_is_exclusive(v_s_2_);
if (v_isSharedCheck_33_ == 0)
{
lean_object* v_unused_34_; 
v_unused_34_ = lean_ctor_get(v_s_2_, 4);
lean_dec(v_unused_34_);
v___x_27_ = v_s_2_;
v_isShared_28_ = v_isSharedCheck_33_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_delaytimer_25_);
lean_inc(v_children_24_);
lean_inc(v_timer_23_);
lean_inc(v_resetcount_21_);
lean_inc(v_rank_20_);
lean_dec(v_s_2_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_33_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
uint8_t v___x_29_; lean_object* v___x_31_; 
v___x_29_ = 2;
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 4, v_Emax_1_);
v___x_31_ = v___x_27_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_rank_20_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v_resetcount_21_);
lean_ctor_set(v_reuseFailAlloc_32_, 2, v_timer_23_);
lean_ctor_set(v_reuseFailAlloc_32_, 3, v_children_24_);
lean_ctor_set(v_reuseFailAlloc_32_, 4, v_Emax_1_);
lean_ctor_set(v_reuseFailAlloc_32_, 5, v_delaytimer_25_);
lean_ctor_set_uint8(v_reuseFailAlloc_32_, sizeof(void*)*6 + 1, v_leader_3_);
lean_ctor_set_uint8(v_reuseFailAlloc_32_, sizeof(void*)*6 + 2, v_answer_22_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_ctor_set_uint8(v___x_31_, sizeof(void*)*6, v___x_29_);
return v___x_31_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetOSSR(lean_object* v_n_35_, lean_object* v_Emax_36_, lean_object* v_hn_37_, lean_object* v_s_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_SSExactMajority_SSEM_resetOSSR___redArg(v_Emax_36_, v_s_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetOSSR___boxed(lean_object* v_n_40_, lean_object* v_Emax_41_, lean_object* v_hn_42_, lean_object* v_s_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_SSExactMajority_SSEM_resetOSSR(v_n_40_, v_Emax_41_, v_hn_42_, v_s_43_);
lean_dec(v_n_40_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent___redArg(lean_object* v_Emax_45_, lean_object* v_Dmax_46_, lean_object* v_s_47_, lean_object* v_oldRc_48_, uint8_t v_partnerResetting_49_){
_start:
{
uint8_t v_role_50_; lean_object* v_rank_51_; uint8_t v_leader_52_; lean_object* v_resetcount_53_; uint8_t v_answer_54_; lean_object* v_timer_55_; lean_object* v_children_56_; lean_object* v_errorcount_57_; lean_object* v_delaytimer_58_; uint8_t v___x_59_; uint8_t v___x_60_; 
v_role_50_ = lean_ctor_get_uint8(v_s_47_, sizeof(void*)*6);
v_rank_51_ = lean_ctor_get(v_s_47_, 0);
v_leader_52_ = lean_ctor_get_uint8(v_s_47_, sizeof(void*)*6 + 1);
v_resetcount_53_ = lean_ctor_get(v_s_47_, 1);
v_answer_54_ = lean_ctor_get_uint8(v_s_47_, sizeof(void*)*6 + 2);
v_timer_55_ = lean_ctor_get(v_s_47_, 2);
v_children_56_ = lean_ctor_get(v_s_47_, 3);
v_errorcount_57_ = lean_ctor_get(v_s_47_, 4);
v_delaytimer_58_ = lean_ctor_get(v_s_47_, 5);
v___x_59_ = 0;
v___x_60_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_50_, v___x_59_);
if (v___x_60_ == 0)
{
lean_dec(v_Dmax_46_);
lean_dec(v_Emax_45_);
return v_s_47_;
}
else
{
lean_object* v___x_61_; lean_object* v___y_63_; lean_object* v_delaytimer_64_; uint8_t v___x_68_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_dec_eq(v_resetcount_53_, v___x_61_);
if (v___x_68_ == 0)
{
lean_dec(v_Dmax_46_);
lean_dec(v_Emax_45_);
return v_s_47_;
}
else
{
lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_85_; 
lean_inc(v_delaytimer_58_);
lean_inc(v_errorcount_57_);
lean_inc(v_children_56_);
lean_inc(v_timer_55_);
lean_inc(v_resetcount_53_);
lean_inc(v_rank_51_);
v_isSharedCheck_85_ = !lean_is_exclusive(v_s_47_);
if (v_isSharedCheck_85_ == 0)
{
lean_object* v_unused_86_; lean_object* v_unused_87_; lean_object* v_unused_88_; lean_object* v_unused_89_; lean_object* v_unused_90_; lean_object* v_unused_91_; 
v_unused_86_ = lean_ctor_get(v_s_47_, 5);
lean_dec(v_unused_86_);
v_unused_87_ = lean_ctor_get(v_s_47_, 4);
lean_dec(v_unused_87_);
v_unused_88_ = lean_ctor_get(v_s_47_, 3);
lean_dec(v_unused_88_);
v_unused_89_ = lean_ctor_get(v_s_47_, 2);
lean_dec(v_unused_89_);
v_unused_90_ = lean_ctor_get(v_s_47_, 1);
lean_dec(v_unused_90_);
v_unused_91_ = lean_ctor_get(v_s_47_, 0);
lean_dec(v_unused_91_);
v___x_70_ = v_s_47_;
v_isShared_71_ = v_isSharedCheck_85_;
goto v_resetjp_69_;
}
else
{
lean_dec(v_s_47_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_85_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
uint8_t v___x_72_; lean_object* v___y_74_; 
v___x_72_ = lean_nat_dec_lt(v___x_61_, v_oldRc_48_);
if (v___x_72_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_sub(v_delaytimer_58_, v___x_77_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 5, v___x_78_);
v___x_80_ = v___x_70_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_rank_51_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_resetcount_53_);
lean_ctor_set(v_reuseFailAlloc_81_, 2, v_timer_55_);
lean_ctor_set(v_reuseFailAlloc_81_, 3, v_children_56_);
lean_ctor_set(v_reuseFailAlloc_81_, 4, v_errorcount_57_);
lean_ctor_set(v_reuseFailAlloc_81_, 5, v___x_78_);
lean_ctor_set_uint8(v_reuseFailAlloc_81_, sizeof(void*)*6, v_role_50_);
lean_ctor_set_uint8(v_reuseFailAlloc_81_, sizeof(void*)*6 + 1, v_leader_52_);
lean_ctor_set_uint8(v_reuseFailAlloc_81_, sizeof(void*)*6 + 2, v_answer_54_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
v___y_74_ = v___x_80_;
goto v___jp_73_;
}
}
else
{
lean_object* v___x_83_; 
lean_inc(v_Dmax_46_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 5, v_Dmax_46_);
v___x_83_ = v___x_70_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_rank_51_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v_resetcount_53_);
lean_ctor_set(v_reuseFailAlloc_84_, 2, v_timer_55_);
lean_ctor_set(v_reuseFailAlloc_84_, 3, v_children_56_);
lean_ctor_set(v_reuseFailAlloc_84_, 4, v_errorcount_57_);
lean_ctor_set(v_reuseFailAlloc_84_, 5, v_Dmax_46_);
lean_ctor_set_uint8(v_reuseFailAlloc_84_, sizeof(void*)*6, v_role_50_);
lean_ctor_set_uint8(v_reuseFailAlloc_84_, sizeof(void*)*6 + 1, v_leader_52_);
lean_ctor_set_uint8(v_reuseFailAlloc_84_, sizeof(void*)*6 + 2, v_answer_54_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
v___y_74_ = v___x_83_;
goto v___jp_73_;
}
}
v___jp_73_:
{
if (v___x_72_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v_Dmax_46_);
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_sub(v_delaytimer_58_, v___x_75_);
lean_dec(v_delaytimer_58_);
v___y_63_ = v___y_74_;
v_delaytimer_64_ = v___x_76_;
goto v___jp_62_;
}
else
{
lean_dec(v_delaytimer_58_);
v___y_63_ = v___y_74_;
v_delaytimer_64_ = v_Dmax_46_;
goto v___jp_62_;
}
}
}
}
v___jp_62_:
{
uint8_t v___x_65_; 
v___x_65_ = lean_nat_dec_eq(v_delaytimer_64_, v___x_61_);
lean_dec(v_delaytimer_64_);
if (v___x_65_ == 0)
{
if (v_partnerResetting_49_ == 0)
{
lean_object* v___x_66_; 
v___x_66_ = lp_SSExactMajority_SSEM_resetOSSR___redArg(v_Emax_45_, v___y_63_);
return v___x_66_;
}
else
{
lean_dec(v_Emax_45_);
return v___y_63_;
}
}
else
{
lean_object* v___x_67_; 
v___x_67_ = lp_SSExactMajority_SSEM_resetOSSR___redArg(v_Emax_45_, v___y_63_);
return v___x_67_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent___redArg___boxed(lean_object* v_Emax_92_, lean_object* v_Dmax_93_, lean_object* v_s_94_, lean_object* v_oldRc_95_, lean_object* v_partnerResetting_96_){
_start:
{
uint8_t v_partnerResetting_boxed_97_; lean_object* v_res_98_; 
v_partnerResetting_boxed_97_ = lean_unbox(v_partnerResetting_96_);
v_res_98_ = lp_SSExactMajority_SSEM_processAgent___redArg(v_Emax_92_, v_Dmax_93_, v_s_94_, v_oldRc_95_, v_partnerResetting_boxed_97_);
lean_dec(v_oldRc_95_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent(lean_object* v_n_99_, lean_object* v_Emax_100_, lean_object* v_Dmax_101_, lean_object* v_hn_102_, lean_object* v_s_103_, lean_object* v_oldRc_104_, uint8_t v_partnerResetting_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lp_SSExactMajority_SSEM_processAgent___redArg(v_Emax_100_, v_Dmax_101_, v_s_103_, v_oldRc_104_, v_partnerResetting_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_processAgent___boxed(lean_object* v_n_107_, lean_object* v_Emax_108_, lean_object* v_Dmax_109_, lean_object* v_hn_110_, lean_object* v_s_111_, lean_object* v_oldRc_112_, lean_object* v_partnerResetting_113_){
_start:
{
uint8_t v_partnerResetting_boxed_114_; lean_object* v_res_115_; 
v_partnerResetting_boxed_114_ = lean_unbox(v_partnerResetting_113_);
v_res_115_ = lp_SSExactMajority_SSEM_processAgent(v_n_107_, v_Emax_108_, v_Dmax_109_, v_hn_110_, v_s_111_, v_oldRc_112_, v_partnerResetting_boxed_114_);
lean_dec(v_oldRc_112_);
lean_dec(v_n_107_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_propagateReset___redArg(lean_object* v_Emax_116_, lean_object* v_Dmax_117_, lean_object* v_a_118_, lean_object* v_b_119_){
_start:
{
lean_object* v___y_121_; lean_object* v___y_122_; lean_object* v_fst_123_; uint8_t v_role_124_; lean_object* v_snd_125_; uint8_t v_role_126_; lean_object* v___y_134_; lean_object* v___y_135_; uint8_t v___y_136_; lean_object* v___y_137_; lean_object* v___y_138_; uint8_t v___y_139_; uint8_t v___y_140_; lean_object* v___y_141_; lean_object* v___y_142_; lean_object* v___y_143_; lean_object* v___y_144_; uint8_t v___y_145_; lean_object* v___y_146_; lean_object* v___y_147_; uint8_t v___y_148_; uint8_t v___y_149_; lean_object* v___y_150_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v_fst_158_; lean_object* v_snd_159_; uint8_t v_role_160_; lean_object* v_fst_163_; uint8_t v_role_164_; lean_object* v_rank_165_; uint8_t v_leader_166_; lean_object* v_resetcount_167_; uint8_t v_answer_168_; lean_object* v_timer_169_; lean_object* v_children_170_; lean_object* v_errorcount_171_; lean_object* v_delaytimer_172_; lean_object* v_snd_173_; uint8_t v_role_174_; lean_object* v_rank_175_; uint8_t v_leader_176_; lean_object* v_resetcount_177_; uint8_t v_answer_178_; lean_object* v_timer_179_; lean_object* v_children_180_; lean_object* v_errorcount_181_; lean_object* v_delaytimer_182_; uint8_t v_role_190_; lean_object* v_rank_191_; uint8_t v_leader_192_; lean_object* v_resetcount_193_; uint8_t v_answer_194_; lean_object* v_timer_195_; lean_object* v_children_196_; lean_object* v_errorcount_197_; lean_object* v_delaytimer_198_; uint8_t v___x_199_; uint8_t v___x_200_; 
v_role_190_ = lean_ctor_get_uint8(v_a_118_, sizeof(void*)*6);
v_rank_191_ = lean_ctor_get(v_a_118_, 0);
lean_inc(v_rank_191_);
v_leader_192_ = lean_ctor_get_uint8(v_a_118_, sizeof(void*)*6 + 1);
v_resetcount_193_ = lean_ctor_get(v_a_118_, 1);
v_answer_194_ = lean_ctor_get_uint8(v_a_118_, sizeof(void*)*6 + 2);
v_timer_195_ = lean_ctor_get(v_a_118_, 2);
lean_inc(v_timer_195_);
v_children_196_ = lean_ctor_get(v_a_118_, 3);
lean_inc(v_children_196_);
v_errorcount_197_ = lean_ctor_get(v_a_118_, 4);
lean_inc(v_errorcount_197_);
v_delaytimer_198_ = lean_ctor_get(v_a_118_, 5);
v___x_199_ = 0;
v___x_200_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_190_, v___x_199_);
if (v___x_200_ == 0)
{
goto v___jp_201_;
}
else
{
lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_nat_dec_lt(v___x_227_, v_resetcount_193_);
if (v___x_228_ == 0)
{
goto v___jp_201_;
}
else
{
uint8_t v_role_229_; lean_object* v_rank_230_; uint8_t v_leader_231_; uint8_t v_answer_232_; lean_object* v_timer_233_; lean_object* v_children_234_; lean_object* v_errorcount_235_; uint8_t v___x_236_; 
v_role_229_ = lean_ctor_get_uint8(v_b_119_, sizeof(void*)*6);
v_rank_230_ = lean_ctor_get(v_b_119_, 0);
v_leader_231_ = lean_ctor_get_uint8(v_b_119_, sizeof(void*)*6 + 1);
v_answer_232_ = lean_ctor_get_uint8(v_b_119_, sizeof(void*)*6 + 2);
v_timer_233_ = lean_ctor_get(v_b_119_, 2);
v_children_234_ = lean_ctor_get(v_b_119_, 3);
v_errorcount_235_ = lean_ctor_get(v_b_119_, 4);
v___x_236_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_229_, v___x_199_);
if (v___x_236_ == 0)
{
if (v___x_228_ == 0)
{
goto v___jp_201_;
}
else
{
lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_inc(v_errorcount_235_);
lean_inc(v_children_234_);
lean_inc(v_timer_233_);
lean_inc(v_rank_230_);
lean_inc(v_delaytimer_198_);
lean_inc(v_resetcount_193_);
v_isSharedCheck_243_ = !lean_is_exclusive(v_b_119_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; lean_object* v_unused_245_; lean_object* v_unused_246_; lean_object* v_unused_247_; lean_object* v_unused_248_; lean_object* v_unused_249_; 
v_unused_244_ = lean_ctor_get(v_b_119_, 5);
lean_dec(v_unused_244_);
v_unused_245_ = lean_ctor_get(v_b_119_, 4);
lean_dec(v_unused_245_);
v_unused_246_ = lean_ctor_get(v_b_119_, 3);
lean_dec(v_unused_246_);
v_unused_247_ = lean_ctor_get(v_b_119_, 2);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_b_119_, 1);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_b_119_, 0);
lean_dec(v_unused_249_);
v___x_238_ = v_b_119_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_dec(v_b_119_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
lean_inc(v_Dmax_117_);
lean_inc(v_errorcount_235_);
lean_inc(v_children_234_);
lean_inc(v_timer_233_);
lean_inc(v_rank_230_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 5, v_Dmax_117_);
lean_ctor_set(v___x_238_, 1, v___x_227_);
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_rank_230_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_timer_233_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_children_234_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_errorcount_235_);
lean_ctor_set(v_reuseFailAlloc_242_, 5, v_Dmax_117_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, sizeof(void*)*6 + 1, v_leader_231_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, sizeof(void*)*6 + 2, v_answer_232_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_ctor_set_uint8(v___x_241_, sizeof(void*)*6, v___x_199_);
lean_inc(v_Dmax_117_);
v_fst_163_ = v_a_118_;
v_role_164_ = v_role_190_;
v_rank_165_ = v_rank_191_;
v_leader_166_ = v_leader_192_;
v_resetcount_167_ = v_resetcount_193_;
v_answer_168_ = v_answer_194_;
v_timer_169_ = v_timer_195_;
v_children_170_ = v_children_196_;
v_errorcount_171_ = v_errorcount_197_;
v_delaytimer_172_ = v_delaytimer_198_;
v_snd_173_ = v___x_241_;
v_role_174_ = v___x_199_;
v_rank_175_ = v_rank_230_;
v_leader_176_ = v_leader_231_;
v_resetcount_177_ = v___x_227_;
v_answer_178_ = v_answer_232_;
v_timer_179_ = v_timer_233_;
v_children_180_ = v_children_234_;
v_errorcount_181_ = v_errorcount_235_;
v_delaytimer_182_ = v_Dmax_117_;
goto v___jp_162_;
}
}
}
}
else
{
goto v___jp_201_;
}
}
}
v___jp_120_:
{
uint8_t v___x_127_; uint8_t v_aRes_128_; uint8_t v_bRes_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_127_ = 0;
v_aRes_128_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_126_, v___x_127_);
v_bRes_129_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_124_, v___x_127_);
lean_inc(v_Dmax_117_);
lean_inc(v_Emax_116_);
v___x_130_ = lp_SSExactMajority_SSEM_processAgent___redArg(v_Emax_116_, v_Dmax_117_, v_fst_123_, v___y_122_, v_aRes_128_);
lean_dec(v___y_122_);
v___x_131_ = lp_SSExactMajority_SSEM_processAgent___redArg(v_Emax_116_, v_Dmax_117_, v_snd_125_, v___y_121_, v_bRes_129_);
lean_dec(v___y_121_);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
return v___x_132_;
}
v___jp_133_:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_inc(v___y_152_);
v___x_153_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_153_, 0, v___y_141_);
lean_ctor_set(v___x_153_, 1, v___y_152_);
lean_ctor_set(v___x_153_, 2, v___y_142_);
lean_ctor_set(v___x_153_, 3, v___y_151_);
lean_ctor_set(v___x_153_, 4, v___y_146_);
lean_ctor_set(v___x_153_, 5, v___y_138_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*6, v___y_140_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*6 + 1, v___y_136_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*6 + 2, v___y_148_);
v___x_154_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_154_, 0, v___y_144_);
lean_ctor_set(v___x_154_, 1, v___y_152_);
lean_ctor_set(v___x_154_, 2, v___y_150_);
lean_ctor_set(v___x_154_, 3, v___y_143_);
lean_ctor_set(v___x_154_, 4, v___y_137_);
lean_ctor_set(v___x_154_, 5, v___y_135_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*6, v___y_145_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*6 + 1, v___y_149_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*6 + 2, v___y_139_);
v___y_121_ = v___y_134_;
v___y_122_ = v___y_147_;
v_fst_123_ = v___x_153_;
v_role_124_ = v___y_140_;
v_snd_125_ = v___x_154_;
v_role_126_ = v___y_145_;
goto v___jp_120_;
}
v___jp_155_:
{
uint8_t v_role_161_; 
v_role_161_ = lean_ctor_get_uint8(v_fst_158_, sizeof(void*)*6);
v___y_121_ = v___y_156_;
v___y_122_ = v___y_157_;
v_fst_123_ = v_fst_158_;
v_role_124_ = v_role_161_;
v_snd_125_ = v_snd_159_;
v_role_126_ = v_role_160_;
goto v___jp_120_;
}
v___jp_162_:
{
uint8_t v___x_183_; uint8_t v___x_184_; 
v___x_183_ = 0;
v___x_184_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_164_, v___x_183_);
if (v___x_184_ == 0)
{
lean_dec(v_delaytimer_182_);
lean_dec(v_errorcount_181_);
lean_dec(v_children_180_);
lean_dec(v_timer_179_);
lean_dec(v_rank_175_);
lean_dec(v_delaytimer_172_);
lean_dec(v_errorcount_171_);
lean_dec(v_children_170_);
lean_dec(v_timer_169_);
lean_dec(v_rank_165_);
v___y_156_ = v_resetcount_177_;
v___y_157_ = v_resetcount_167_;
v_fst_158_ = v_fst_163_;
v_snd_159_ = v_snd_173_;
v_role_160_ = v_role_174_;
goto v___jp_155_;
}
else
{
uint8_t v___x_185_; 
v___x_185_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_174_, v___x_183_);
if (v___x_185_ == 0)
{
lean_dec(v_delaytimer_182_);
lean_dec(v_errorcount_181_);
lean_dec(v_children_180_);
lean_dec(v_timer_179_);
lean_dec(v_rank_175_);
lean_dec(v_delaytimer_172_);
lean_dec(v_errorcount_171_);
lean_dec(v_children_170_);
lean_dec(v_timer_169_);
lean_dec(v_rank_165_);
v___y_156_ = v_resetcount_177_;
v___y_157_ = v_resetcount_167_;
v_fst_158_ = v_fst_163_;
v_snd_159_ = v_snd_173_;
v_role_160_ = v_role_174_;
goto v___jp_155_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
lean_dec_ref(v_snd_173_);
lean_dec_ref(v_fst_163_);
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_sub(v_resetcount_167_, v___x_186_);
v___x_188_ = lean_nat_sub(v_resetcount_177_, v___x_186_);
v___x_189_ = lean_nat_dec_le(v___x_187_, v___x_188_);
if (v___x_189_ == 0)
{
lean_dec(v___x_188_);
v___y_134_ = v_resetcount_177_;
v___y_135_ = v_delaytimer_182_;
v___y_136_ = v_leader_166_;
v___y_137_ = v_errorcount_181_;
v___y_138_ = v_delaytimer_172_;
v___y_139_ = v_answer_178_;
v___y_140_ = v_role_164_;
v___y_141_ = v_rank_165_;
v___y_142_ = v_timer_169_;
v___y_143_ = v_children_180_;
v___y_144_ = v_rank_175_;
v___y_145_ = v_role_174_;
v___y_146_ = v_errorcount_171_;
v___y_147_ = v_resetcount_167_;
v___y_148_ = v_answer_168_;
v___y_149_ = v_leader_176_;
v___y_150_ = v_timer_179_;
v___y_151_ = v_children_170_;
v___y_152_ = v___x_187_;
goto v___jp_133_;
}
else
{
lean_dec(v___x_187_);
v___y_134_ = v_resetcount_177_;
v___y_135_ = v_delaytimer_182_;
v___y_136_ = v_leader_166_;
v___y_137_ = v_errorcount_181_;
v___y_138_ = v_delaytimer_172_;
v___y_139_ = v_answer_178_;
v___y_140_ = v_role_164_;
v___y_141_ = v_rank_165_;
v___y_142_ = v_timer_169_;
v___y_143_ = v_children_180_;
v___y_144_ = v_rank_175_;
v___y_145_ = v_role_174_;
v___y_146_ = v_errorcount_171_;
v___y_147_ = v_resetcount_167_;
v___y_148_ = v_answer_168_;
v___y_149_ = v_leader_176_;
v___y_150_ = v_timer_179_;
v___y_151_ = v_children_170_;
v___y_152_ = v___x_188_;
goto v___jp_133_;
}
}
}
}
v___jp_201_:
{
uint8_t v_role_202_; lean_object* v_rank_203_; uint8_t v_leader_204_; lean_object* v_resetcount_205_; uint8_t v_answer_206_; lean_object* v_timer_207_; lean_object* v_children_208_; lean_object* v_errorcount_209_; lean_object* v_delaytimer_210_; uint8_t v___x_211_; 
v_role_202_ = lean_ctor_get_uint8(v_b_119_, sizeof(void*)*6);
v_rank_203_ = lean_ctor_get(v_b_119_, 0);
lean_inc(v_rank_203_);
v_leader_204_ = lean_ctor_get_uint8(v_b_119_, sizeof(void*)*6 + 1);
v_resetcount_205_ = lean_ctor_get(v_b_119_, 1);
lean_inc(v_resetcount_205_);
v_answer_206_ = lean_ctor_get_uint8(v_b_119_, sizeof(void*)*6 + 2);
v_timer_207_ = lean_ctor_get(v_b_119_, 2);
lean_inc(v_timer_207_);
v_children_208_ = lean_ctor_get(v_b_119_, 3);
lean_inc(v_children_208_);
v_errorcount_209_ = lean_ctor_get(v_b_119_, 4);
lean_inc(v_errorcount_209_);
v_delaytimer_210_ = lean_ctor_get(v_b_119_, 5);
lean_inc(v_delaytimer_210_);
v___x_211_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_202_, v___x_199_);
if (v___x_211_ == 0)
{
lean_inc(v_delaytimer_198_);
lean_inc(v_resetcount_193_);
v_fst_163_ = v_a_118_;
v_role_164_ = v_role_190_;
v_rank_165_ = v_rank_191_;
v_leader_166_ = v_leader_192_;
v_resetcount_167_ = v_resetcount_193_;
v_answer_168_ = v_answer_194_;
v_timer_169_ = v_timer_195_;
v_children_170_ = v_children_196_;
v_errorcount_171_ = v_errorcount_197_;
v_delaytimer_172_ = v_delaytimer_198_;
v_snd_173_ = v_b_119_;
v_role_174_ = v_role_202_;
v_rank_175_ = v_rank_203_;
v_leader_176_ = v_leader_204_;
v_resetcount_177_ = v_resetcount_205_;
v_answer_178_ = v_answer_206_;
v_timer_179_ = v_timer_207_;
v_children_180_ = v_children_208_;
v_errorcount_181_ = v_errorcount_209_;
v_delaytimer_182_ = v_delaytimer_210_;
goto v___jp_162_;
}
else
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_nat_dec_lt(v___x_212_, v_resetcount_205_);
if (v___x_213_ == 0)
{
lean_inc(v_delaytimer_198_);
lean_inc(v_resetcount_193_);
v_fst_163_ = v_a_118_;
v_role_164_ = v_role_190_;
v_rank_165_ = v_rank_191_;
v_leader_166_ = v_leader_192_;
v_resetcount_167_ = v_resetcount_193_;
v_answer_168_ = v_answer_194_;
v_timer_169_ = v_timer_195_;
v_children_170_ = v_children_196_;
v_errorcount_171_ = v_errorcount_197_;
v_delaytimer_172_ = v_delaytimer_198_;
v_snd_173_ = v_b_119_;
v_role_174_ = v_role_202_;
v_rank_175_ = v_rank_203_;
v_leader_176_ = v_leader_204_;
v_resetcount_177_ = v_resetcount_205_;
v_answer_178_ = v_answer_206_;
v_timer_179_ = v_timer_207_;
v_children_180_ = v_children_208_;
v_errorcount_181_ = v_errorcount_209_;
v_delaytimer_182_ = v_delaytimer_210_;
goto v___jp_162_;
}
else
{
if (v___x_200_ == 0)
{
if (v___x_213_ == 0)
{
lean_inc(v_delaytimer_198_);
lean_inc(v_resetcount_193_);
v_fst_163_ = v_a_118_;
v_role_164_ = v_role_190_;
v_rank_165_ = v_rank_191_;
v_leader_166_ = v_leader_192_;
v_resetcount_167_ = v_resetcount_193_;
v_answer_168_ = v_answer_194_;
v_timer_169_ = v_timer_195_;
v_children_170_ = v_children_196_;
v_errorcount_171_ = v_errorcount_197_;
v_delaytimer_172_ = v_delaytimer_198_;
v_snd_173_ = v_b_119_;
v_role_174_ = v_role_202_;
v_rank_175_ = v_rank_203_;
v_leader_176_ = v_leader_204_;
v_resetcount_177_ = v_resetcount_205_;
v_answer_178_ = v_answer_206_;
v_timer_179_ = v_timer_207_;
v_children_180_ = v_children_208_;
v_errorcount_181_ = v_errorcount_209_;
v_delaytimer_182_ = v_delaytimer_210_;
goto v___jp_162_;
}
else
{
lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
v_isSharedCheck_220_ = !lean_is_exclusive(v_a_118_);
if (v_isSharedCheck_220_ == 0)
{
lean_object* v_unused_221_; lean_object* v_unused_222_; lean_object* v_unused_223_; lean_object* v_unused_224_; lean_object* v_unused_225_; lean_object* v_unused_226_; 
v_unused_221_ = lean_ctor_get(v_a_118_, 5);
lean_dec(v_unused_221_);
v_unused_222_ = lean_ctor_get(v_a_118_, 4);
lean_dec(v_unused_222_);
v_unused_223_ = lean_ctor_get(v_a_118_, 3);
lean_dec(v_unused_223_);
v_unused_224_ = lean_ctor_get(v_a_118_, 2);
lean_dec(v_unused_224_);
v_unused_225_ = lean_ctor_get(v_a_118_, 1);
lean_dec(v_unused_225_);
v_unused_226_ = lean_ctor_get(v_a_118_, 0);
lean_dec(v_unused_226_);
v___x_215_ = v_a_118_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_dec(v_a_118_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
lean_inc(v_Dmax_117_);
lean_inc(v_errorcount_197_);
lean_inc(v_children_196_);
lean_inc(v_timer_195_);
lean_inc(v_rank_191_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 5, v_Dmax_117_);
lean_ctor_set(v___x_215_, 1, v___x_212_);
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_rank_191_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_timer_195_);
lean_ctor_set(v_reuseFailAlloc_219_, 3, v_children_196_);
lean_ctor_set(v_reuseFailAlloc_219_, 4, v_errorcount_197_);
lean_ctor_set(v_reuseFailAlloc_219_, 5, v_Dmax_117_);
lean_ctor_set_uint8(v_reuseFailAlloc_219_, sizeof(void*)*6 + 1, v_leader_192_);
lean_ctor_set_uint8(v_reuseFailAlloc_219_, sizeof(void*)*6 + 2, v_answer_194_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*6, v___x_199_);
lean_inc(v_Dmax_117_);
v_fst_163_ = v___x_218_;
v_role_164_ = v___x_199_;
v_rank_165_ = v_rank_191_;
v_leader_166_ = v_leader_192_;
v_resetcount_167_ = v___x_212_;
v_answer_168_ = v_answer_194_;
v_timer_169_ = v_timer_195_;
v_children_170_ = v_children_196_;
v_errorcount_171_ = v_errorcount_197_;
v_delaytimer_172_ = v_Dmax_117_;
v_snd_173_ = v_b_119_;
v_role_174_ = v_role_202_;
v_rank_175_ = v_rank_203_;
v_leader_176_ = v_leader_204_;
v_resetcount_177_ = v_resetcount_205_;
v_answer_178_ = v_answer_206_;
v_timer_179_ = v_timer_207_;
v_children_180_ = v_children_208_;
v_errorcount_181_ = v_errorcount_209_;
v_delaytimer_182_ = v_delaytimer_210_;
goto v___jp_162_;
}
}
}
}
else
{
lean_inc(v_delaytimer_198_);
lean_inc(v_resetcount_193_);
v_fst_163_ = v_a_118_;
v_role_164_ = v_role_190_;
v_rank_165_ = v_rank_191_;
v_leader_166_ = v_leader_192_;
v_resetcount_167_ = v_resetcount_193_;
v_answer_168_ = v_answer_194_;
v_timer_169_ = v_timer_195_;
v_children_170_ = v_children_196_;
v_errorcount_171_ = v_errorcount_197_;
v_delaytimer_172_ = v_delaytimer_198_;
v_snd_173_ = v_b_119_;
v_role_174_ = v_role_202_;
v_rank_175_ = v_rank_203_;
v_leader_176_ = v_leader_204_;
v_resetcount_177_ = v_resetcount_205_;
v_answer_178_ = v_answer_206_;
v_timer_179_ = v_timer_207_;
v_children_180_ = v_children_208_;
v_errorcount_181_ = v_errorcount_209_;
v_delaytimer_182_ = v_delaytimer_210_;
goto v___jp_162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_propagateReset(lean_object* v_n_250_, lean_object* v_Emax_251_, lean_object* v_Dmax_252_, lean_object* v_hn_253_, lean_object* v_a_254_, lean_object* v_b_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lp_SSExactMajority_SSEM_propagateReset___redArg(v_Emax_251_, v_Dmax_252_, v_a_254_, v_b_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_propagateReset___boxed(lean_object* v_n_257_, lean_object* v_Emax_258_, lean_object* v_Dmax_259_, lean_object* v_hn_260_, lean_object* v_a_261_, lean_object* v_b_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = lp_SSExactMajority_SSEM_propagateReset(v_n_257_, v_Emax_258_, v_Dmax_259_, v_hn_260_, v_a_261_, v_b_262_);
lean_dec(v_n_257_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg(lean_object* v_n_264_, lean_object* v_Rmax_265_, lean_object* v_Emax_266_, lean_object* v_Dmax_267_, lean_object* v_pair_268_){
_start:
{
lean_object* v_fst_269_; lean_object* v_snd_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_551_; 
v_fst_269_ = lean_ctor_get(v_pair_268_, 0);
v_snd_270_ = lean_ctor_get(v_pair_268_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_pair_268_);
if (v_isSharedCheck_551_ == 0)
{
v___x_272_ = v_pair_268_;
v_isShared_273_ = v_isSharedCheck_551_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_snd_270_);
lean_inc(v_fst_269_);
lean_dec(v_pair_268_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_551_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
uint8_t v_role_274_; lean_object* v_rank_275_; uint8_t v_leader_276_; lean_object* v_resetcount_277_; uint8_t v_answer_278_; lean_object* v_timer_279_; lean_object* v_children_280_; lean_object* v_errorcount_281_; lean_object* v_delaytimer_282_; uint8_t v___x_283_; lean_object* v_rank_285_; uint8_t v_answer_286_; lean_object* v_timer_287_; lean_object* v_children_288_; lean_object* v_errorcount_289_; lean_object* v_delaytimer_290_; lean_object* v_rank_291_; uint8_t v_answer_292_; lean_object* v_timer_293_; lean_object* v_children_294_; lean_object* v_errorcount_295_; lean_object* v_delaytimer_296_; lean_object* v___y_304_; lean_object* v___y_305_; uint8_t v___y_306_; lean_object* v___y_324_; uint8_t v___y_325_; uint8_t v___y_326_; lean_object* v___y_327_; uint8_t v___x_379_; 
v_role_274_ = lean_ctor_get_uint8(v_fst_269_, sizeof(void*)*6);
v_rank_275_ = lean_ctor_get(v_fst_269_, 0);
v_leader_276_ = lean_ctor_get_uint8(v_fst_269_, sizeof(void*)*6 + 1);
v_resetcount_277_ = lean_ctor_get(v_fst_269_, 1);
v_answer_278_ = lean_ctor_get_uint8(v_fst_269_, sizeof(void*)*6 + 2);
v_timer_279_ = lean_ctor_get(v_fst_269_, 2);
v_children_280_ = lean_ctor_get(v_fst_269_, 3);
v_errorcount_281_ = lean_ctor_get(v_fst_269_, 4);
v_delaytimer_282_ = lean_ctor_get(v_fst_269_, 5);
v___x_283_ = 0;
v___x_379_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_274_, v___x_283_);
if (v___x_379_ == 0)
{
uint8_t v_role_380_; lean_object* v_rank_381_; uint8_t v_leader_382_; lean_object* v_resetcount_383_; uint8_t v_answer_384_; lean_object* v_timer_385_; lean_object* v_children_386_; lean_object* v_errorcount_387_; lean_object* v_delaytimer_388_; uint8_t v___y_390_; uint8_t v___y_391_; lean_object* v___y_392_; uint8_t v___x_439_; 
v_role_380_ = lean_ctor_get_uint8(v_snd_270_, sizeof(void*)*6);
v_rank_381_ = lean_ctor_get(v_snd_270_, 0);
v_leader_382_ = lean_ctor_get_uint8(v_snd_270_, sizeof(void*)*6 + 1);
v_resetcount_383_ = lean_ctor_get(v_snd_270_, 1);
v_answer_384_ = lean_ctor_get_uint8(v_snd_270_, sizeof(void*)*6 + 2);
v_timer_385_ = lean_ctor_get(v_snd_270_, 2);
v_children_386_ = lean_ctor_get(v_snd_270_, 3);
v_errorcount_387_ = lean_ctor_get(v_snd_270_, 4);
v_delaytimer_388_ = lean_ctor_get(v_snd_270_, 5);
v___x_439_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_380_, v___x_283_);
if (v___x_439_ == 0)
{
uint8_t v___x_440_; uint8_t v___x_481_; 
lean_dec(v_Dmax_267_);
lean_dec(v_Emax_266_);
v___x_440_ = 1;
v___x_481_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_274_, v___x_440_);
if (v___x_481_ == 0)
{
goto v___jp_482_;
}
else
{
uint8_t v___x_521_; 
v___x_521_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_380_, v___x_440_);
if (v___x_521_ == 0)
{
goto v___jp_482_;
}
else
{
uint8_t v___x_522_; 
v___x_522_ = lean_nat_dec_eq(v_rank_275_, v_rank_381_);
if (v___x_522_ == 0)
{
goto v___jp_482_;
}
else
{
lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_544_; 
lean_inc(v_delaytimer_388_);
lean_inc(v_errorcount_387_);
lean_inc(v_children_386_);
lean_inc(v_timer_385_);
lean_inc(v_rank_381_);
lean_inc(v_delaytimer_282_);
lean_inc(v_errorcount_281_);
lean_inc(v_children_280_);
lean_inc(v_timer_279_);
lean_inc(v_rank_275_);
lean_del_object(v___x_272_);
v_isSharedCheck_544_ = !lean_is_exclusive(v_fst_269_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; lean_object* v_unused_546_; lean_object* v_unused_547_; lean_object* v_unused_548_; lean_object* v_unused_549_; lean_object* v_unused_550_; 
v_unused_545_ = lean_ctor_get(v_fst_269_, 5);
lean_dec(v_unused_545_);
v_unused_546_ = lean_ctor_get(v_fst_269_, 4);
lean_dec(v_unused_546_);
v_unused_547_ = lean_ctor_get(v_fst_269_, 3);
lean_dec(v_unused_547_);
v_unused_548_ = lean_ctor_get(v_fst_269_, 2);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_fst_269_, 1);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_fst_269_, 0);
lean_dec(v_unused_550_);
v___x_524_ = v_fst_269_;
v_isShared_525_ = v_isSharedCheck_544_;
goto v_resetjp_523_;
}
else
{
lean_dec(v_fst_269_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_544_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_537_; 
v_isSharedCheck_537_ = !lean_is_exclusive(v_snd_270_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; lean_object* v_unused_539_; lean_object* v_unused_540_; lean_object* v_unused_541_; lean_object* v_unused_542_; lean_object* v_unused_543_; 
v_unused_538_ = lean_ctor_get(v_snd_270_, 5);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_snd_270_, 4);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_snd_270_, 3);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_snd_270_, 2);
lean_dec(v_unused_541_);
v_unused_542_ = lean_ctor_get(v_snd_270_, 1);
lean_dec(v_unused_542_);
v_unused_543_ = lean_ctor_get(v_snd_270_, 0);
lean_dec(v_unused_543_);
v___x_527_ = v_snd_270_;
v_isShared_528_ = v_isSharedCheck_537_;
goto v_resetjp_526_;
}
else
{
lean_dec(v_snd_270_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_537_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
uint8_t v___x_529_; lean_object* v___x_531_; 
v___x_529_ = 0;
lean_inc(v_Rmax_265_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 5, v_delaytimer_282_);
lean_ctor_set(v___x_527_, 4, v_errorcount_281_);
lean_ctor_set(v___x_527_, 3, v_children_280_);
lean_ctor_set(v___x_527_, 2, v_timer_279_);
lean_ctor_set(v___x_527_, 1, v_Rmax_265_);
lean_ctor_set(v___x_527_, 0, v_rank_275_);
v___x_531_ = v___x_527_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_rank_275_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_Rmax_265_);
lean_ctor_set(v_reuseFailAlloc_536_, 2, v_timer_279_);
lean_ctor_set(v_reuseFailAlloc_536_, 3, v_children_280_);
lean_ctor_set(v_reuseFailAlloc_536_, 4, v_errorcount_281_);
lean_ctor_set(v_reuseFailAlloc_536_, 5, v_delaytimer_282_);
v___x_531_ = v_reuseFailAlloc_536_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_533_; 
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*6, v___x_283_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*6 + 1, v___x_529_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*6 + 2, v_answer_278_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 5, v_delaytimer_388_);
lean_ctor_set(v___x_524_, 4, v_errorcount_387_);
lean_ctor_set(v___x_524_, 3, v_children_386_);
lean_ctor_set(v___x_524_, 2, v_timer_385_);
lean_ctor_set(v___x_524_, 1, v_Rmax_265_);
lean_ctor_set(v___x_524_, 0, v_rank_381_);
v___x_533_ = v___x_524_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_rank_381_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_Rmax_265_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v_timer_385_);
lean_ctor_set(v_reuseFailAlloc_535_, 3, v_children_386_);
lean_ctor_set(v_reuseFailAlloc_535_, 4, v_errorcount_387_);
lean_ctor_set(v_reuseFailAlloc_535_, 5, v_delaytimer_388_);
v___x_533_ = v_reuseFailAlloc_535_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; 
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*6, v___x_283_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*6 + 1, v___x_529_);
lean_ctor_set_uint8(v___x_533_, sizeof(void*)*6 + 2, v_answer_384_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_531_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
return v___x_534_;
}
}
}
}
}
}
}
v___jp_441_:
{
uint8_t v___x_442_; 
v___x_442_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_380_, v___x_440_);
if (v___x_442_ == 0)
{
goto v___jp_415_;
}
else
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 2;
v___x_444_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_274_, v___x_443_);
if (v___x_444_ == 0)
{
goto v___jp_415_;
}
else
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(2u);
v___x_446_ = lean_nat_dec_lt(v_children_386_, v___x_445_);
if (v___x_446_ == 0)
{
goto v___jp_415_;
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v_childRank_450_; uint8_t v___x_451_; 
v___x_447_ = lean_nat_mul(v___x_445_, v_rank_381_);
v___x_448_ = lean_nat_add(v___x_447_, v_children_386_);
lean_dec(v___x_447_);
v___x_449_ = lean_unsigned_to_nat(1u);
v_childRank_450_ = lean_nat_add(v___x_448_, v___x_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_nat_dec_lt(v_childRank_450_, v_n_264_);
if (v___x_451_ == 0)
{
lean_dec(v_childRank_450_);
goto v___jp_415_;
}
else
{
lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_474_; 
lean_inc(v_delaytimer_388_);
lean_inc(v_errorcount_387_);
lean_inc(v_children_386_);
lean_inc(v_timer_385_);
lean_inc(v_resetcount_383_);
lean_inc(v_rank_381_);
lean_inc(v_delaytimer_282_);
lean_inc(v_errorcount_281_);
lean_inc(v_timer_279_);
lean_inc(v_resetcount_277_);
lean_del_object(v___x_272_);
lean_dec(v_Rmax_265_);
v_isSharedCheck_474_ = !lean_is_exclusive(v_fst_269_);
if (v_isSharedCheck_474_ == 0)
{
lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; lean_object* v_unused_479_; lean_object* v_unused_480_; 
v_unused_475_ = lean_ctor_get(v_fst_269_, 5);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_fst_269_, 4);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_fst_269_, 3);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_fst_269_, 2);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v_fst_269_, 1);
lean_dec(v_unused_479_);
v_unused_480_ = lean_ctor_get(v_fst_269_, 0);
lean_dec(v_unused_480_);
v___x_453_ = v_fst_269_;
v_isShared_454_ = v_isSharedCheck_474_;
goto v_resetjp_452_;
}
else
{
lean_dec(v_fst_269_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_474_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_467_; 
v_isSharedCheck_467_ = !lean_is_exclusive(v_snd_270_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; lean_object* v_unused_469_; lean_object* v_unused_470_; lean_object* v_unused_471_; lean_object* v_unused_472_; lean_object* v_unused_473_; 
v_unused_468_ = lean_ctor_get(v_snd_270_, 5);
lean_dec(v_unused_468_);
v_unused_469_ = lean_ctor_get(v_snd_270_, 4);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_snd_270_, 3);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_snd_270_, 2);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_snd_270_, 1);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_snd_270_, 0);
lean_dec(v_unused_473_);
v___x_456_ = v_snd_270_;
v_isShared_457_ = v_isSharedCheck_467_;
goto v_resetjp_455_;
}
else
{
lean_dec(v_snd_270_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_467_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_458_ = lean_unsigned_to_nat(0u);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 5, v_delaytimer_282_);
lean_ctor_set(v___x_456_, 4, v_errorcount_281_);
lean_ctor_set(v___x_456_, 3, v___x_458_);
lean_ctor_set(v___x_456_, 2, v_timer_279_);
lean_ctor_set(v___x_456_, 1, v_resetcount_277_);
lean_ctor_set(v___x_456_, 0, v_childRank_450_);
v___x_460_ = v___x_456_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_childRank_450_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_resetcount_277_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_timer_279_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v_errorcount_281_);
lean_ctor_set(v_reuseFailAlloc_466_, 5, v_delaytimer_282_);
v___x_460_ = v_reuseFailAlloc_466_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
lean_ctor_set_uint8(v___x_460_, sizeof(void*)*6, v___x_440_);
lean_ctor_set_uint8(v___x_460_, sizeof(void*)*6 + 1, v_leader_276_);
lean_ctor_set_uint8(v___x_460_, sizeof(void*)*6 + 2, v_answer_278_);
v___x_461_ = lean_nat_add(v_children_386_, v___x_449_);
lean_dec(v_children_386_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 5, v_delaytimer_388_);
lean_ctor_set(v___x_453_, 4, v_errorcount_387_);
lean_ctor_set(v___x_453_, 3, v___x_461_);
lean_ctor_set(v___x_453_, 2, v_timer_385_);
lean_ctor_set(v___x_453_, 1, v_resetcount_383_);
lean_ctor_set(v___x_453_, 0, v_rank_381_);
v___x_463_ = v___x_453_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_rank_381_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_resetcount_383_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_timer_385_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v_errorcount_387_);
lean_ctor_set(v_reuseFailAlloc_465_, 5, v_delaytimer_388_);
v___x_463_ = v_reuseFailAlloc_465_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; 
lean_ctor_set_uint8(v___x_463_, sizeof(void*)*6, v_role_380_);
lean_ctor_set_uint8(v___x_463_, sizeof(void*)*6 + 1, v_leader_382_);
lean_ctor_set_uint8(v___x_463_, sizeof(void*)*6 + 2, v_answer_384_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_460_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
return v___x_464_;
}
}
}
}
}
}
}
}
}
v___jp_482_:
{
if (v___x_481_ == 0)
{
goto v___jp_441_;
}
else
{
uint8_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = 2;
v___x_484_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_380_, v___x_483_);
if (v___x_484_ == 0)
{
goto v___jp_441_;
}
else
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(2u);
v___x_486_ = lean_nat_dec_lt(v_children_280_, v___x_485_);
if (v___x_486_ == 0)
{
goto v___jp_441_;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_childRank_490_; uint8_t v___x_491_; 
v___x_487_ = lean_nat_mul(v___x_485_, v_rank_275_);
v___x_488_ = lean_nat_add(v___x_487_, v_children_280_);
lean_dec(v___x_487_);
v___x_489_ = lean_unsigned_to_nat(1u);
v_childRank_490_ = lean_nat_add(v___x_488_, v___x_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_nat_dec_lt(v_childRank_490_, v_n_264_);
if (v___x_491_ == 0)
{
lean_dec(v_childRank_490_);
goto v___jp_441_;
}
else
{
lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_514_; 
lean_inc(v_delaytimer_388_);
lean_inc(v_errorcount_387_);
lean_inc(v_timer_385_);
lean_inc(v_resetcount_383_);
lean_inc(v_delaytimer_282_);
lean_inc(v_errorcount_281_);
lean_inc(v_children_280_);
lean_inc(v_timer_279_);
lean_inc(v_resetcount_277_);
lean_inc(v_rank_275_);
lean_del_object(v___x_272_);
lean_dec(v_Rmax_265_);
v_isSharedCheck_514_ = !lean_is_exclusive(v_fst_269_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; lean_object* v_unused_516_; lean_object* v_unused_517_; lean_object* v_unused_518_; lean_object* v_unused_519_; lean_object* v_unused_520_; 
v_unused_515_ = lean_ctor_get(v_fst_269_, 5);
lean_dec(v_unused_515_);
v_unused_516_ = lean_ctor_get(v_fst_269_, 4);
lean_dec(v_unused_516_);
v_unused_517_ = lean_ctor_get(v_fst_269_, 3);
lean_dec(v_unused_517_);
v_unused_518_ = lean_ctor_get(v_fst_269_, 2);
lean_dec(v_unused_518_);
v_unused_519_ = lean_ctor_get(v_fst_269_, 1);
lean_dec(v_unused_519_);
v_unused_520_ = lean_ctor_get(v_fst_269_, 0);
lean_dec(v_unused_520_);
v___x_493_ = v_fst_269_;
v_isShared_494_ = v_isSharedCheck_514_;
goto v_resetjp_492_;
}
else
{
lean_dec(v_fst_269_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_514_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_507_; 
v_isSharedCheck_507_ = !lean_is_exclusive(v_snd_270_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; lean_object* v_unused_509_; lean_object* v_unused_510_; lean_object* v_unused_511_; lean_object* v_unused_512_; lean_object* v_unused_513_; 
v_unused_508_ = lean_ctor_get(v_snd_270_, 5);
lean_dec(v_unused_508_);
v_unused_509_ = lean_ctor_get(v_snd_270_, 4);
lean_dec(v_unused_509_);
v_unused_510_ = lean_ctor_get(v_snd_270_, 3);
lean_dec(v_unused_510_);
v_unused_511_ = lean_ctor_get(v_snd_270_, 2);
lean_dec(v_unused_511_);
v_unused_512_ = lean_ctor_get(v_snd_270_, 1);
lean_dec(v_unused_512_);
v_unused_513_ = lean_ctor_get(v_snd_270_, 0);
lean_dec(v_unused_513_);
v___x_496_ = v_snd_270_;
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
else
{
lean_dec(v_snd_270_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_498_ = lean_nat_add(v_children_280_, v___x_489_);
lean_dec(v_children_280_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 5, v_delaytimer_282_);
lean_ctor_set(v___x_496_, 4, v_errorcount_281_);
lean_ctor_set(v___x_496_, 3, v___x_498_);
lean_ctor_set(v___x_496_, 2, v_timer_279_);
lean_ctor_set(v___x_496_, 1, v_resetcount_277_);
lean_ctor_set(v___x_496_, 0, v_rank_275_);
v___x_500_ = v___x_496_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_rank_275_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_resetcount_277_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_timer_279_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v_errorcount_281_);
lean_ctor_set(v_reuseFailAlloc_506_, 5, v_delaytimer_282_);
v___x_500_ = v_reuseFailAlloc_506_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_501_; lean_object* v___x_503_; 
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*6, v_role_274_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*6 + 1, v_leader_276_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*6 + 2, v_answer_278_);
v___x_501_ = lean_unsigned_to_nat(0u);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 5, v_delaytimer_388_);
lean_ctor_set(v___x_493_, 4, v_errorcount_387_);
lean_ctor_set(v___x_493_, 3, v___x_501_);
lean_ctor_set(v___x_493_, 2, v_timer_385_);
lean_ctor_set(v___x_493_, 1, v_resetcount_383_);
lean_ctor_set(v___x_493_, 0, v_childRank_490_);
v___x_503_ = v___x_493_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_childRank_490_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_resetcount_383_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v_timer_385_);
lean_ctor_set(v_reuseFailAlloc_505_, 3, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_505_, 4, v_errorcount_387_);
lean_ctor_set(v_reuseFailAlloc_505_, 5, v_delaytimer_388_);
v___x_503_ = v_reuseFailAlloc_505_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; 
lean_ctor_set_uint8(v___x_503_, sizeof(void*)*6, v___x_440_);
lean_ctor_set_uint8(v___x_503_, sizeof(void*)*6 + 1, v_leader_382_);
lean_ctor_set_uint8(v___x_503_, sizeof(void*)*6 + 2, v_answer_384_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_500_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
return v___x_504_;
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
else
{
lean_del_object(v___x_272_);
lean_dec(v_Rmax_265_);
goto v___jp_342_;
}
v___jp_389_:
{
uint8_t v___x_393_; 
v___x_393_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_380_, v___y_390_);
if (v___x_393_ == 0)
{
v___y_324_ = v___y_392_;
v___y_325_ = v___y_391_;
v___y_326_ = v___x_393_;
v___y_327_ = v_snd_270_;
goto v___jp_323_;
}
else
{
lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_408_; 
lean_inc(v_delaytimer_388_);
lean_inc(v_errorcount_387_);
lean_inc(v_children_386_);
lean_inc(v_timer_385_);
lean_inc(v_resetcount_383_);
lean_inc(v_rank_381_);
v_isSharedCheck_408_ = !lean_is_exclusive(v_snd_270_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; lean_object* v_unused_410_; lean_object* v_unused_411_; lean_object* v_unused_412_; lean_object* v_unused_413_; lean_object* v_unused_414_; 
v_unused_409_ = lean_ctor_get(v_snd_270_, 5);
lean_dec(v_unused_409_);
v_unused_410_ = lean_ctor_get(v_snd_270_, 4);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v_snd_270_, 3);
lean_dec(v_unused_411_);
v_unused_412_ = lean_ctor_get(v_snd_270_, 2);
lean_dec(v_unused_412_);
v_unused_413_ = lean_ctor_get(v_snd_270_, 1);
lean_dec(v_unused_413_);
v_unused_414_ = lean_ctor_get(v_snd_270_, 0);
lean_dec(v_unused_414_);
v___x_395_ = v_snd_270_;
v_isShared_396_ = v_isSharedCheck_408_;
goto v_resetjp_394_;
}
else
{
lean_dec(v_snd_270_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_408_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_397_ = lean_unsigned_to_nat(1u);
v___x_398_ = lean_nat_sub(v_errorcount_387_, v___x_397_);
lean_dec(v_errorcount_387_);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_nat_dec_eq(v___x_398_, v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v_b_x27_x27_402_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 4, v___x_398_);
v_b_x27_x27_402_ = v___x_395_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_rank_381_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_resetcount_383_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_timer_385_);
lean_ctor_set(v_reuseFailAlloc_403_, 3, v_children_386_);
lean_ctor_set(v_reuseFailAlloc_403_, 4, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_403_, 5, v_delaytimer_388_);
lean_ctor_set_uint8(v_reuseFailAlloc_403_, sizeof(void*)*6, v_role_380_);
lean_ctor_set_uint8(v_reuseFailAlloc_403_, sizeof(void*)*6 + 1, v_leader_382_);
lean_ctor_set_uint8(v_reuseFailAlloc_403_, sizeof(void*)*6 + 2, v_answer_384_);
v_b_x27_x27_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
v___y_324_ = v___y_392_;
v___y_325_ = v___y_391_;
v___y_326_ = v___x_393_;
v___y_327_ = v_b_x27_x27_402_;
goto v___jp_323_;
}
}
else
{
uint8_t v___x_404_; lean_object* v___x_406_; 
lean_dec(v_resetcount_383_);
v___x_404_ = 0;
lean_inc(v_Rmax_265_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 4, v___x_398_);
lean_ctor_set(v___x_395_, 1, v_Rmax_265_);
v___x_406_ = v___x_395_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_rank_381_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_Rmax_265_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_timer_385_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_children_386_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_407_, 5, v_delaytimer_388_);
lean_ctor_set_uint8(v_reuseFailAlloc_407_, sizeof(void*)*6 + 2, v_answer_384_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*6, v___x_283_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*6 + 1, v___x_404_);
v___y_324_ = v___y_392_;
v___y_325_ = v___y_391_;
v___y_326_ = v___x_393_;
v___y_327_ = v___x_406_;
goto v___jp_323_;
}
}
}
}
}
v___jp_415_:
{
uint8_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = 2;
v___x_417_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_274_, v___x_416_);
if (v___x_417_ == 0)
{
v___y_390_ = v___x_416_;
v___y_391_ = v___x_417_;
v___y_392_ = v_fst_269_;
goto v___jp_389_;
}
else
{
lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_432_; 
lean_inc(v_delaytimer_282_);
lean_inc(v_errorcount_281_);
lean_inc(v_children_280_);
lean_inc(v_timer_279_);
lean_inc(v_resetcount_277_);
lean_inc(v_rank_275_);
v_isSharedCheck_432_ = !lean_is_exclusive(v_fst_269_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; lean_object* v_unused_434_; lean_object* v_unused_435_; lean_object* v_unused_436_; lean_object* v_unused_437_; lean_object* v_unused_438_; 
v_unused_433_ = lean_ctor_get(v_fst_269_, 5);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_fst_269_, 4);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_fst_269_, 3);
lean_dec(v_unused_435_);
v_unused_436_ = lean_ctor_get(v_fst_269_, 2);
lean_dec(v_unused_436_);
v_unused_437_ = lean_ctor_get(v_fst_269_, 1);
lean_dec(v_unused_437_);
v_unused_438_ = lean_ctor_get(v_fst_269_, 0);
lean_dec(v_unused_438_);
v___x_419_ = v_fst_269_;
v_isShared_420_ = v_isSharedCheck_432_;
goto v_resetjp_418_;
}
else
{
lean_dec(v_fst_269_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_432_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_sub(v_errorcount_281_, v___x_421_);
lean_dec(v_errorcount_281_);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_nat_dec_eq(v___x_422_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v_a_x27_x27_426_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 4, v___x_422_);
v_a_x27_x27_426_ = v___x_419_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_rank_275_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_resetcount_277_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_timer_279_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v_children_280_);
lean_ctor_set(v_reuseFailAlloc_427_, 4, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_427_, 5, v_delaytimer_282_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*6, v_role_274_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*6 + 1, v_leader_276_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*6 + 2, v_answer_278_);
v_a_x27_x27_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
v___y_390_ = v___x_416_;
v___y_391_ = v___x_417_;
v___y_392_ = v_a_x27_x27_426_;
goto v___jp_389_;
}
}
else
{
uint8_t v___x_428_; lean_object* v___x_430_; 
lean_dec(v_resetcount_277_);
v___x_428_ = 0;
lean_inc(v_Rmax_265_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 4, v___x_422_);
lean_ctor_set(v___x_419_, 1, v_Rmax_265_);
v___x_430_ = v___x_419_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_rank_275_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_Rmax_265_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_timer_279_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_children_280_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_431_, 5, v_delaytimer_282_);
lean_ctor_set_uint8(v_reuseFailAlloc_431_, sizeof(void*)*6 + 2, v_answer_278_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*6, v___x_283_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*6 + 1, v___x_428_);
v___y_390_ = v___x_416_;
v___y_391_ = v___x_417_;
v___y_392_ = v___x_430_;
goto v___jp_389_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_272_);
lean_dec(v_Rmax_265_);
goto v___jp_342_;
}
v___jp_284_:
{
uint8_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_297_ = 0;
lean_inc(v_Rmax_265_);
v___x_298_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_298_, 0, v_rank_285_);
lean_ctor_set(v___x_298_, 1, v_Rmax_265_);
lean_ctor_set(v___x_298_, 2, v_timer_287_);
lean_ctor_set(v___x_298_, 3, v_children_288_);
lean_ctor_set(v___x_298_, 4, v_errorcount_289_);
lean_ctor_set(v___x_298_, 5, v_delaytimer_290_);
lean_ctor_set_uint8(v___x_298_, sizeof(void*)*6, v___x_283_);
lean_ctor_set_uint8(v___x_298_, sizeof(void*)*6 + 1, v___x_297_);
lean_ctor_set_uint8(v___x_298_, sizeof(void*)*6 + 2, v_answer_286_);
v___x_299_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_299_, 0, v_rank_291_);
lean_ctor_set(v___x_299_, 1, v_Rmax_265_);
lean_ctor_set(v___x_299_, 2, v_timer_293_);
lean_ctor_set(v___x_299_, 3, v_children_294_);
lean_ctor_set(v___x_299_, 4, v_errorcount_295_);
lean_ctor_set(v___x_299_, 5, v_delaytimer_296_);
lean_ctor_set_uint8(v___x_299_, sizeof(void*)*6, v___x_283_);
lean_ctor_set_uint8(v___x_299_, sizeof(void*)*6 + 1, v___x_297_);
lean_ctor_set_uint8(v___x_299_, sizeof(void*)*6 + 2, v_answer_292_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v___x_299_);
lean_ctor_set(v___x_272_, 0, v___x_298_);
v___x_301_ = v___x_272_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
v___jp_303_:
{
uint8_t v_role_307_; lean_object* v_rank_308_; uint8_t v_answer_309_; lean_object* v_timer_310_; lean_object* v_children_311_; lean_object* v_errorcount_312_; lean_object* v_delaytimer_313_; uint8_t v___x_314_; 
v_role_307_ = lean_ctor_get_uint8(v___y_305_, sizeof(void*)*6);
v_rank_308_ = lean_ctor_get(v___y_305_, 0);
v_answer_309_ = lean_ctor_get_uint8(v___y_305_, sizeof(void*)*6 + 2);
v_timer_310_ = lean_ctor_get(v___y_305_, 2);
v_children_311_ = lean_ctor_get(v___y_305_, 3);
v_errorcount_312_ = lean_ctor_get(v___y_305_, 4);
v_delaytimer_313_ = lean_ctor_get(v___y_305_, 5);
v___x_314_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_307_, v___x_283_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; 
lean_del_object(v___x_272_);
lean_dec(v_Rmax_265_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___y_304_);
lean_ctor_set(v___x_315_, 1, v___y_305_);
return v___x_315_;
}
else
{
if (v___y_306_ == 0)
{
lean_object* v___x_316_; 
lean_del_object(v___x_272_);
lean_dec(v_Rmax_265_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___y_304_);
lean_ctor_set(v___x_316_, 1, v___y_305_);
return v___x_316_;
}
else
{
lean_object* v_rank_317_; uint8_t v_answer_318_; lean_object* v_timer_319_; lean_object* v_children_320_; lean_object* v_errorcount_321_; lean_object* v_delaytimer_322_; 
lean_inc(v_delaytimer_313_);
lean_inc(v_errorcount_312_);
lean_inc(v_children_311_);
lean_inc(v_timer_310_);
lean_inc(v_rank_308_);
lean_dec_ref(v___y_305_);
v_rank_317_ = lean_ctor_get(v___y_304_, 0);
lean_inc(v_rank_317_);
v_answer_318_ = lean_ctor_get_uint8(v___y_304_, sizeof(void*)*6 + 2);
v_timer_319_ = lean_ctor_get(v___y_304_, 2);
lean_inc(v_timer_319_);
v_children_320_ = lean_ctor_get(v___y_304_, 3);
lean_inc(v_children_320_);
v_errorcount_321_ = lean_ctor_get(v___y_304_, 4);
lean_inc(v_errorcount_321_);
v_delaytimer_322_ = lean_ctor_get(v___y_304_, 5);
lean_inc(v_delaytimer_322_);
lean_dec_ref(v___y_304_);
v_rank_285_ = v_rank_317_;
v_answer_286_ = v_answer_318_;
v_timer_287_ = v_timer_319_;
v_children_288_ = v_children_320_;
v_errorcount_289_ = v_errorcount_321_;
v_delaytimer_290_ = v_delaytimer_322_;
v_rank_291_ = v_rank_308_;
v_answer_292_ = v_answer_309_;
v_timer_293_ = v_timer_310_;
v_children_294_ = v_children_311_;
v_errorcount_295_ = v_errorcount_312_;
v_delaytimer_296_ = v_delaytimer_313_;
goto v___jp_284_;
}
}
}
v___jp_323_:
{
uint8_t v_role_328_; lean_object* v_rank_329_; uint8_t v_answer_330_; lean_object* v_timer_331_; lean_object* v_children_332_; lean_object* v_errorcount_333_; lean_object* v_delaytimer_334_; uint8_t v___x_335_; 
v_role_328_ = lean_ctor_get_uint8(v___y_324_, sizeof(void*)*6);
v_rank_329_ = lean_ctor_get(v___y_324_, 0);
v_answer_330_ = lean_ctor_get_uint8(v___y_324_, sizeof(void*)*6 + 2);
v_timer_331_ = lean_ctor_get(v___y_324_, 2);
v_children_332_ = lean_ctor_get(v___y_324_, 3);
v_errorcount_333_ = lean_ctor_get(v___y_324_, 4);
v_delaytimer_334_ = lean_ctor_get(v___y_324_, 5);
v___x_335_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_328_, v___x_283_);
if (v___x_335_ == 0)
{
v___y_304_ = v___y_324_;
v___y_305_ = v___y_327_;
v___y_306_ = v___y_326_;
goto v___jp_303_;
}
else
{
if (v___y_325_ == 0)
{
v___y_304_ = v___y_324_;
v___y_305_ = v___y_327_;
v___y_306_ = v___y_326_;
goto v___jp_303_;
}
else
{
lean_object* v_rank_336_; uint8_t v_answer_337_; lean_object* v_timer_338_; lean_object* v_children_339_; lean_object* v_errorcount_340_; lean_object* v_delaytimer_341_; 
lean_inc(v_delaytimer_334_);
lean_inc(v_errorcount_333_);
lean_inc(v_children_332_);
lean_inc(v_timer_331_);
lean_inc(v_rank_329_);
lean_dec_ref(v___y_324_);
v_rank_336_ = lean_ctor_get(v___y_327_, 0);
lean_inc(v_rank_336_);
v_answer_337_ = lean_ctor_get_uint8(v___y_327_, sizeof(void*)*6 + 2);
v_timer_338_ = lean_ctor_get(v___y_327_, 2);
lean_inc(v_timer_338_);
v_children_339_ = lean_ctor_get(v___y_327_, 3);
lean_inc(v_children_339_);
v_errorcount_340_ = lean_ctor_get(v___y_327_, 4);
lean_inc(v_errorcount_340_);
v_delaytimer_341_ = lean_ctor_get(v___y_327_, 5);
lean_inc(v_delaytimer_341_);
lean_dec_ref(v___y_327_);
v_rank_285_ = v_rank_329_;
v_answer_286_ = v_answer_330_;
v_timer_287_ = v_timer_331_;
v_children_288_ = v_children_332_;
v_errorcount_289_ = v_errorcount_333_;
v_delaytimer_290_ = v_delaytimer_334_;
v_rank_291_ = v_rank_336_;
v_answer_292_ = v_answer_337_;
v_timer_293_ = v_timer_338_;
v_children_294_ = v_children_339_;
v_errorcount_295_ = v_errorcount_340_;
v_delaytimer_296_ = v_delaytimer_341_;
goto v___jp_284_;
}
}
}
v___jp_342_:
{
lean_object* v___x_343_; lean_object* v_fst_344_; lean_object* v_snd_345_; uint8_t v_role_346_; uint8_t v_leader_347_; uint8_t v___x_348_; uint8_t v___x_349_; 
v___x_343_ = lp_SSExactMajority_SSEM_propagateReset___redArg(v_Emax_266_, v_Dmax_267_, v_fst_269_, v_snd_270_);
v_fst_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_fst_344_);
v_snd_345_ = lean_ctor_get(v___x_343_, 1);
lean_inc(v_snd_345_);
v_role_346_ = lean_ctor_get_uint8(v_fst_344_, sizeof(void*)*6);
v_leader_347_ = lean_ctor_get_uint8(v_fst_344_, sizeof(void*)*6 + 1);
v___x_348_ = 0;
v___x_349_ = lp_SSExactMajority_SSEM_instDecidableEqLeader(v_leader_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_dec(v_snd_345_);
lean_dec(v_fst_344_);
return v___x_343_;
}
else
{
uint8_t v_role_350_; lean_object* v_rank_351_; uint8_t v_leader_352_; lean_object* v_resetcount_353_; uint8_t v_answer_354_; lean_object* v_timer_355_; lean_object* v_children_356_; lean_object* v_errorcount_357_; lean_object* v_delaytimer_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_378_; 
v_role_350_ = lean_ctor_get_uint8(v_snd_345_, sizeof(void*)*6);
v_rank_351_ = lean_ctor_get(v_snd_345_, 0);
v_leader_352_ = lean_ctor_get_uint8(v_snd_345_, sizeof(void*)*6 + 1);
v_resetcount_353_ = lean_ctor_get(v_snd_345_, 1);
v_answer_354_ = lean_ctor_get_uint8(v_snd_345_, sizeof(void*)*6 + 2);
v_timer_355_ = lean_ctor_get(v_snd_345_, 2);
v_children_356_ = lean_ctor_get(v_snd_345_, 3);
v_errorcount_357_ = lean_ctor_get(v_snd_345_, 4);
v_delaytimer_358_ = lean_ctor_get(v_snd_345_, 5);
v_isSharedCheck_378_ = !lean_is_exclusive(v_snd_345_);
if (v_isSharedCheck_378_ == 0)
{
v___x_360_ = v_snd_345_;
v_isShared_361_ = v_isSharedCheck_378_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_delaytimer_358_);
lean_inc(v_errorcount_357_);
lean_inc(v_children_356_);
lean_inc(v_timer_355_);
lean_inc(v_resetcount_353_);
lean_inc(v_rank_351_);
lean_dec(v_snd_345_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_378_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
uint8_t v___x_362_; 
v___x_362_ = lp_SSExactMajority_SSEM_instDecidableEqLeader(v_leader_352_, v___x_348_);
if (v___x_362_ == 0)
{
lean_del_object(v___x_360_);
lean_dec(v_delaytimer_358_);
lean_dec(v_errorcount_357_);
lean_dec(v_children_356_);
lean_dec(v_timer_355_);
lean_dec(v_resetcount_353_);
lean_dec(v_rank_351_);
lean_dec(v_fst_344_);
return v___x_343_;
}
else
{
uint8_t v___x_363_; 
v___x_363_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_346_, v___x_283_);
if (v___x_363_ == 0)
{
lean_del_object(v___x_360_);
lean_dec(v_delaytimer_358_);
lean_dec(v_errorcount_357_);
lean_dec(v_children_356_);
lean_dec(v_timer_355_);
lean_dec(v_resetcount_353_);
lean_dec(v_rank_351_);
lean_dec(v_fst_344_);
return v___x_343_;
}
else
{
uint8_t v___x_364_; 
v___x_364_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_350_, v___x_283_);
if (v___x_364_ == 0)
{
lean_del_object(v___x_360_);
lean_dec(v_delaytimer_358_);
lean_dec(v_errorcount_357_);
lean_dec(v_children_356_);
lean_dec(v_timer_355_);
lean_dec(v_resetcount_353_);
lean_dec(v_rank_351_);
lean_dec(v_fst_344_);
return v___x_343_;
}
else
{
lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_375_; 
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; lean_object* v_unused_377_; 
v_unused_376_ = lean_ctor_get(v___x_343_, 1);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v___x_343_, 0);
lean_dec(v_unused_377_);
v___x_366_ = v___x_343_;
v_isShared_367_ = v_isSharedCheck_375_;
goto v_resetjp_365_;
}
else
{
lean_dec(v___x_343_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_375_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
uint8_t v___x_368_; lean_object* v___x_370_; 
v___x_368_ = 1;
if (v_isShared_361_ == 0)
{
v___x_370_ = v___x_360_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_rank_351_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_resetcount_353_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_timer_355_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v_children_356_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v_errorcount_357_);
lean_ctor_set(v_reuseFailAlloc_374_, 5, v_delaytimer_358_);
lean_ctor_set_uint8(v_reuseFailAlloc_374_, sizeof(void*)*6, v_role_350_);
lean_ctor_set_uint8(v_reuseFailAlloc_374_, sizeof(void*)*6 + 2, v_answer_354_);
v___x_370_ = v_reuseFailAlloc_374_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_372_; 
lean_ctor_set_uint8(v___x_370_, sizeof(void*)*6 + 1, v___x_368_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v___x_370_);
v___x_372_ = v___x_366_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_fst_344_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
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
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg___boxed(lean_object* v_n_552_, lean_object* v_Rmax_553_, lean_object* v_Emax_554_, lean_object* v_Dmax_555_, lean_object* v_pair_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg(v_n_552_, v_Rmax_553_, v_Emax_554_, v_Dmax_555_, v_pair_556_);
lean_dec(v_n_552_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR(lean_object* v_n_558_, lean_object* v_Rmax_559_, lean_object* v_Emax_560_, lean_object* v_Dmax_561_, lean_object* v_hn_562_, lean_object* v_pair_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg(v_n_558_, v_Rmax_559_, v_Emax_560_, v_Dmax_561_, v_pair_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed(lean_object* v_n_565_, lean_object* v_Rmax_566_, lean_object* v_Emax_567_, lean_object* v_Dmax_568_, lean_object* v_hn_569_, lean_object* v_pair_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = lp_SSExactMajority_SSEM_rankDeltaOSSR(v_n_565_, v_Rmax_566_, v_Emax_567_, v_Dmax_568_, v_hn_569_, v_pair_570_);
lean_dec(v_n_565_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable___redArg(lean_object* v_n_572_, lean_object* v_Rmax_573_, lean_object* v_Emax_574_, lean_object* v_Dmax_575_, lean_object* v_pair_576_){
_start:
{
lean_object* v_fst_577_; lean_object* v_snd_578_; uint8_t v_role_579_; uint8_t v___x_580_; uint8_t v___x_581_; 
v_fst_577_ = lean_ctor_get(v_pair_576_, 0);
v_snd_578_ = lean_ctor_get(v_pair_576_, 1);
v_role_579_ = lean_ctor_get_uint8(v_fst_577_, sizeof(void*)*6);
v___x_580_ = 1;
v___x_581_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_579_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
v___x_582_ = lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg(v_n_572_, v_Rmax_573_, v_Emax_574_, v_Dmax_575_, v_pair_576_);
return v___x_582_;
}
else
{
uint8_t v_role_583_; uint8_t v___x_584_; 
v_role_583_ = lean_ctor_get_uint8(v_snd_578_, sizeof(void*)*6);
v___x_584_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_583_, v___x_580_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
v___x_585_ = lp_SSExactMajority_SSEM_rankDeltaOSSR___redArg(v_n_572_, v_Rmax_573_, v_Emax_574_, v_Dmax_575_, v_pair_576_);
return v___x_585_;
}
else
{
lean_dec(v_Dmax_575_);
lean_dec(v_Emax_574_);
lean_dec(v_Rmax_573_);
return v_pair_576_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable___redArg___boxed(lean_object* v_n_586_, lean_object* v_Rmax_587_, lean_object* v_Emax_588_, lean_object* v_Dmax_589_, lean_object* v_pair_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = lp_SSExactMajority_SSEM_rankDeltaStable___redArg(v_n_586_, v_Rmax_587_, v_Emax_588_, v_Dmax_589_, v_pair_590_);
lean_dec(v_n_586_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable(lean_object* v_n_592_, lean_object* v_Rmax_593_, lean_object* v_Emax_594_, lean_object* v_Dmax_595_, lean_object* v_hn_596_, lean_object* v_pair_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = lp_SSExactMajority_SSEM_rankDeltaStable___redArg(v_n_592_, v_Rmax_593_, v_Emax_594_, v_Dmax_595_, v_pair_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rankDeltaStable___boxed(lean_object* v_n_599_, lean_object* v_Rmax_600_, lean_object* v_Emax_601_, lean_object* v_Dmax_602_, lean_object* v_hn_603_, lean_object* v_pair_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = lp_SSExactMajority_SSEM_rankDeltaStable(v_n_599_, v_Rmax_600_, v_Emax_601_, v_Dmax_602_, v_hn_603_, v_pair_604_);
lean_dec(v_n_599_);
return v_res_605_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_State(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_Silent(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_RankDelta(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Protocol_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_Silent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
