// Lean compiler output
// Module: SSExactMajority.Convergence.BurmanConvergenceFinal
// Imports: public import Init public meta import Init public import SSExactMajority.Convergence.BurmanProof
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqOpinion(uint8_t, uint8_t);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqAnswer(uint8_t, uint8_t);
uint8_t l_Nat_decidableExistsFin___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lp_SSExactMajority_SSEM_nAOf(lean_object*, lean_object*);
lean_object* lp_SSExactMajority_SSEM_nBOf(lean_object*, lean_object*);
lean_object* lp_SSExactMajority_SSEM_nonResettingCount(lean_object*, lean_object*);
lean_object* lp_SSExactMajority_Finset_sum___at___00SSEM_unsettledMass_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetFuelContribution___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetFuelContribution___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetFuelContribution(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetFuelContribution___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetFuel___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetFuel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_execution_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_execution_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_execution_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_execution_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_majorityOpinionOfAnswerBCF(uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_majorityOpinionOfAnswerBCF___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_majorityCountOfAnswerBCF(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_majorityCountOfAnswerBCF___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityAgentsOfAnswerBCF___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityAgentsOfAnswerBCF___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityAgentsOfAnswerBCF(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityAgentsOfAnswerBCF___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityCountOfAnswerBCF_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityCountOfAnswerBCF_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityCountOfAnswerBCF_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityCountOfAnswerBCF_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityOpinionOfAnswerBCF_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityOpinionOfAnswerBCF_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityOpinionOfAnswerBCF_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityOpinionOfAnswerBCF_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_phiCount___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phiCount___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phiCount(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_unrecruitedTargetRanks___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unrecruitedTargetRanks___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_unrecruitedTargetRanks___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unrecruitedTargetRanks___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unrecruitedTargetRanks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unrecruitedTargetRankCount(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rank1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rank1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rank1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetFuelContribution___redArg(lean_object* v_s_1_){
_start:
{
uint8_t v_role_2_; lean_object* v_resetcount_3_; uint8_t v___x_4_; uint8_t v___x_5_; 
v_role_2_ = lean_ctor_get_uint8(v_s_1_, sizeof(void*)*6);
v_resetcount_3_ = lean_ctor_get(v_s_1_, 1);
v___x_4_ = 0;
v___x_5_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_2_, v___x_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(0u);
return v___x_6_;
}
else
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = lean_unsigned_to_nat(2u);
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_add(v_resetcount_3_, v___x_8_);
v___x_10_ = lean_nat_pow(v___x_7_, v___x_9_);
lean_dec(v___x_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetFuelContribution___redArg___boxed(lean_object* v_s_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_SSExactMajority_SSEM_resetFuelContribution___redArg(v_s_11_);
lean_dec_ref(v_s_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetFuelContribution(lean_object* v_n_13_, lean_object* v_s_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_SSExactMajority_SSEM_resetFuelContribution___redArg(v_s_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetFuelContribution___boxed(lean_object* v_n_16_, lean_object* v_s_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_SSExactMajority_SSEM_resetFuelContribution(v_n_16_, v_s_17_);
lean_dec_ref(v_s_17_);
lean_dec(v_n_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetFuel___lam__0(lean_object* v_C_19_, lean_object* v_w_20_){
_start:
{
lean_object* v___x_21_; lean_object* v_fst_22_; lean_object* v___x_23_; 
v___x_21_ = lean_apply_1(v_C_19_, v_w_20_);
v_fst_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_fst_22_);
lean_dec_ref(v___x_21_);
v___x_23_ = lp_SSExactMajority_SSEM_resetFuelContribution___redArg(v_fst_22_);
lean_dec(v_fst_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetFuel(lean_object* v_n_24_, lean_object* v_C_25_){
_start:
{
lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
lean_inc_ref(v_C_25_);
v___f_26_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_resetFuel___lam__0), 2, 1);
lean_closure_set(v___f_26_, 0, v_C_25_);
lean_inc(v_n_24_);
v___x_27_ = lp_SSExactMajority_SSEM_nonResettingCount(v_n_24_, v_C_25_);
v___x_28_ = l_List_finRange(v_n_24_);
v___x_29_ = lp_SSExactMajority_Finset_sum___at___00SSEM_unsettledMass_spec__0___redArg(v___x_28_, v___f_26_);
v___x_30_ = lean_nat_add(v___x_27_, v___x_29_);
lean_dec(v___x_29_);
lean_dec(v___x_27_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_execution_match__1_splitter___redArg(lean_object* v_x_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v_zero_34_; uint8_t v_isZero_35_; 
v_zero_34_ = lean_unsigned_to_nat(0u);
v_isZero_35_ = lean_nat_dec_eq(v_x_31_, v_zero_34_);
if (v_isZero_35_ == 1)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v_h__2_33_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_apply_1(v_h__1_32_, v___x_36_);
return v___x_37_;
}
else
{
lean_object* v_one_38_; lean_object* v_n_39_; lean_object* v___x_40_; 
lean_dec(v_h__1_32_);
v_one_38_ = lean_unsigned_to_nat(1u);
v_n_39_ = lean_nat_sub(v_x_31_, v_one_38_);
v___x_40_ = lean_apply_1(v_h__2_33_, v_n_39_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_execution_match__1_splitter___redArg___boxed(lean_object* v_x_41_, lean_object* v_h__1_42_, lean_object* v_h__2_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_execution_match__1_splitter___redArg(v_x_41_, v_h__1_42_, v_h__2_43_);
lean_dec(v_x_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_execution_match__1_splitter(lean_object* v_motive_45_, lean_object* v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
lean_object* v_zero_49_; uint8_t v_isZero_50_; 
v_zero_49_ = lean_unsigned_to_nat(0u);
v_isZero_50_ = lean_nat_dec_eq(v_x_46_, v_zero_49_);
if (v_isZero_50_ == 1)
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec(v_h__2_48_);
v___x_51_ = lean_box(0);
v___x_52_ = lean_apply_1(v_h__1_47_, v___x_51_);
return v___x_52_;
}
else
{
lean_object* v_one_53_; lean_object* v_n_54_; lean_object* v___x_55_; 
lean_dec(v_h__1_47_);
v_one_53_ = lean_unsigned_to_nat(1u);
v_n_54_ = lean_nat_sub(v_x_46_, v_one_53_);
v___x_55_ = lean_apply_1(v_h__2_48_, v_n_54_);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_execution_match__1_splitter___boxed(lean_object* v_motive_56_, lean_object* v_x_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_execution_match__1_splitter(v_motive_56_, v_x_57_, v_h__1_58_, v_h__2_59_);
lean_dec(v_x_57_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_majorityOpinionOfAnswerBCF(uint8_t v_m_61_){
_start:
{
if (v_m_61_ == 3)
{
uint8_t v___x_62_; 
v___x_62_ = 1;
return v___x_62_;
}
else
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_majorityOpinionOfAnswerBCF___boxed(lean_object* v_m_64_){
_start:
{
uint8_t v_m_boxed_65_; uint8_t v_res_66_; lean_object* v_r_67_; 
v_m_boxed_65_ = lean_unbox(v_m_64_);
v_res_66_ = lp_SSExactMajority_SSEM_majorityOpinionOfAnswerBCF(v_m_boxed_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_majorityCountOfAnswerBCF(lean_object* v_n_68_, lean_object* v_C_69_, uint8_t v_m_70_){
_start:
{
switch(v_m_70_)
{
case 2:
{
lean_object* v___x_71_; 
v___x_71_ = lp_SSExactMajority_SSEM_nAOf(v_n_68_, v_C_69_);
return v___x_71_;
}
case 3:
{
lean_object* v___x_72_; 
v___x_72_ = lp_SSExactMajority_SSEM_nBOf(v_n_68_, v_C_69_);
return v___x_72_;
}
default: 
{
lean_object* v___x_73_; 
lean_dec_ref(v_C_69_);
lean_dec(v_n_68_);
v___x_73_ = lean_unsigned_to_nat(0u);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_majorityCountOfAnswerBCF___boxed(lean_object* v_n_74_, lean_object* v_C_75_, lean_object* v_m_76_){
_start:
{
uint8_t v_m_boxed_77_; lean_object* v_res_78_; 
v_m_boxed_77_ = lean_unbox(v_m_76_);
v_res_78_ = lp_SSExactMajority_SSEM_majorityCountOfAnswerBCF(v_n_74_, v_C_75_, v_m_boxed_77_);
return v_res_78_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityAgentsOfAnswerBCF___lam__0(lean_object* v_C_79_, uint8_t v_m_80_, lean_object* v_a_81_){
_start:
{
lean_object* v___x_82_; lean_object* v_snd_83_; uint8_t v___x_84_; uint8_t v___x_85_; uint8_t v___x_86_; 
v___x_82_ = lean_apply_1(v_C_79_, v_a_81_);
v_snd_83_ = lean_ctor_get(v___x_82_, 1);
lean_inc(v_snd_83_);
lean_dec_ref(v___x_82_);
v___x_84_ = lp_SSExactMajority_SSEM_majorityOpinionOfAnswerBCF(v_m_80_);
v___x_85_ = lean_unbox(v_snd_83_);
lean_dec(v_snd_83_);
v___x_86_ = lp_SSExactMajority_SSEM_instDecidableEqOpinion(v___x_85_, v___x_84_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityAgentsOfAnswerBCF___lam__0___boxed(lean_object* v_C_87_, lean_object* v_m_88_, lean_object* v_a_89_){
_start:
{
uint8_t v_m_boxed_90_; uint8_t v_res_91_; lean_object* v_r_92_; 
v_m_boxed_90_ = lean_unbox(v_m_88_);
v_res_91_ = lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityAgentsOfAnswerBCF___lam__0(v_C_87_, v_m_boxed_90_, v_a_89_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityAgentsOfAnswerBCF(lean_object* v_n_93_, lean_object* v_C_94_, uint8_t v_m_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___f_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_96_ = lean_box(v_m_95_);
v___f_97_ = lean_alloc_closure((void*)(lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityAgentsOfAnswerBCF___lam__0___boxed), 3, 2);
lean_closure_set(v___f_97_, 0, v_C_94_);
lean_closure_set(v___f_97_, 1, v___x_96_);
v___x_98_ = l_List_finRange(v_n_93_);
v___x_99_ = lp_mathlib_Multiset_filter___redArg(v___f_97_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityAgentsOfAnswerBCF___boxed(lean_object* v_n_100_, lean_object* v_C_101_, lean_object* v_m_102_){
_start:
{
uint8_t v_m_boxed_103_; lean_object* v_res_104_; 
v_m_boxed_103_ = lean_unbox(v_m_102_);
v_res_104_ = lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityAgentsOfAnswerBCF(v_n_100_, v_C_101_, v_m_boxed_103_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityCountOfAnswerBCF_match__1_splitter___redArg(uint8_t v_m_105_, lean_object* v_h__1_106_, lean_object* v_h__2_107_, lean_object* v_h__3_108_){
_start:
{
switch(v_m_105_)
{
case 2:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v_h__3_108_);
lean_dec(v_h__2_107_);
v___x_109_ = lean_box(0);
v___x_110_ = lean_apply_1(v_h__1_106_, v___x_109_);
return v___x_110_;
}
case 3:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec(v_h__3_108_);
lean_dec(v_h__1_106_);
v___x_111_ = lean_box(0);
v___x_112_ = lean_apply_1(v_h__2_107_, v___x_111_);
return v___x_112_;
}
default: 
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v_h__2_107_);
lean_dec(v_h__1_106_);
v___x_113_ = lean_box(v_m_105_);
v___x_114_ = lean_apply_3(v_h__3_108_, v___x_113_, lean_box(0), lean_box(0));
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityCountOfAnswerBCF_match__1_splitter___redArg___boxed(lean_object* v_m_115_, lean_object* v_h__1_116_, lean_object* v_h__2_117_, lean_object* v_h__3_118_){
_start:
{
uint8_t v_m_22__boxed_119_; lean_object* v_res_120_; 
v_m_22__boxed_119_ = lean_unbox(v_m_115_);
v_res_120_ = lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityCountOfAnswerBCF_match__1_splitter___redArg(v_m_22__boxed_119_, v_h__1_116_, v_h__2_117_, v_h__3_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityCountOfAnswerBCF_match__1_splitter(lean_object* v_motive_121_, uint8_t v_m_122_, lean_object* v_h__1_123_, lean_object* v_h__2_124_, lean_object* v_h__3_125_){
_start:
{
switch(v_m_122_)
{
case 2:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec(v_h__3_125_);
lean_dec(v_h__2_124_);
v___x_126_ = lean_box(0);
v___x_127_ = lean_apply_1(v_h__1_123_, v___x_126_);
return v___x_127_;
}
case 3:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v_h__3_125_);
lean_dec(v_h__1_123_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_apply_1(v_h__2_124_, v___x_128_);
return v___x_129_;
}
default: 
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_h__2_124_);
lean_dec(v_h__1_123_);
v___x_130_ = lean_box(v_m_122_);
v___x_131_ = lean_apply_3(v_h__3_125_, v___x_130_, lean_box(0), lean_box(0));
return v___x_131_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityCountOfAnswerBCF_match__1_splitter___boxed(lean_object* v_motive_132_, lean_object* v_m_133_, lean_object* v_h__1_134_, lean_object* v_h__2_135_, lean_object* v_h__3_136_){
_start:
{
uint8_t v_m_37__boxed_137_; lean_object* v_res_138_; 
v_m_37__boxed_137_ = lean_unbox(v_m_133_);
v_res_138_ = lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityCountOfAnswerBCF_match__1_splitter(v_motive_132_, v_m_37__boxed_137_, v_h__1_134_, v_h__2_135_, v_h__3_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityOpinionOfAnswerBCF_match__1_splitter___redArg(uint8_t v_m_139_, lean_object* v_h__1_140_, lean_object* v_h__2_141_, lean_object* v_h__3_142_, lean_object* v_h__4_143_){
_start:
{
switch(v_m_139_)
{
case 0:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v_h__3_142_);
lean_dec(v_h__2_141_);
lean_dec(v_h__1_140_);
v___x_144_ = lean_box(0);
v___x_145_ = lean_apply_1(v_h__4_143_, v___x_144_);
return v___x_145_;
}
case 1:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v_h__4_143_);
lean_dec(v_h__2_141_);
lean_dec(v_h__1_140_);
v___x_146_ = lean_box(0);
v___x_147_ = lean_apply_1(v_h__3_142_, v___x_146_);
return v___x_147_;
}
case 2:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v_h__4_143_);
lean_dec(v_h__3_142_);
lean_dec(v_h__2_141_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_apply_1(v_h__1_140_, v___x_148_);
return v___x_149_;
}
default: 
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec(v_h__4_143_);
lean_dec(v_h__3_142_);
lean_dec(v_h__1_140_);
v___x_150_ = lean_box(0);
v___x_151_ = lean_apply_1(v_h__2_141_, v___x_150_);
return v___x_151_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityOpinionOfAnswerBCF_match__1_splitter___redArg___boxed(lean_object* v_m_152_, lean_object* v_h__1_153_, lean_object* v_h__2_154_, lean_object* v_h__3_155_, lean_object* v_h__4_156_){
_start:
{
uint8_t v_m_46__boxed_157_; lean_object* v_res_158_; 
v_m_46__boxed_157_ = lean_unbox(v_m_152_);
v_res_158_ = lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityOpinionOfAnswerBCF_match__1_splitter___redArg(v_m_46__boxed_157_, v_h__1_153_, v_h__2_154_, v_h__3_155_, v_h__4_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityOpinionOfAnswerBCF_match__1_splitter(lean_object* v_motive_159_, uint8_t v_m_160_, lean_object* v_h__1_161_, lean_object* v_h__2_162_, lean_object* v_h__3_163_, lean_object* v_h__4_164_){
_start:
{
switch(v_m_160_)
{
case 0:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v_h__3_163_);
lean_dec(v_h__2_162_);
lean_dec(v_h__1_161_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_apply_1(v_h__4_164_, v___x_165_);
return v___x_166_;
}
case 1:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec(v_h__4_164_);
lean_dec(v_h__2_162_);
lean_dec(v_h__1_161_);
v___x_167_ = lean_box(0);
v___x_168_ = lean_apply_1(v_h__3_163_, v___x_167_);
return v___x_168_;
}
case 2:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec(v_h__4_164_);
lean_dec(v_h__3_163_);
lean_dec(v_h__2_162_);
v___x_169_ = lean_box(0);
v___x_170_ = lean_apply_1(v_h__1_161_, v___x_169_);
return v___x_170_;
}
default: 
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec(v_h__4_164_);
lean_dec(v_h__3_163_);
lean_dec(v_h__1_161_);
v___x_171_ = lean_box(0);
v___x_172_ = lean_apply_1(v_h__2_162_, v___x_171_);
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityOpinionOfAnswerBCF_match__1_splitter___boxed(lean_object* v_motive_173_, lean_object* v_m_174_, lean_object* v_h__1_175_, lean_object* v_h__2_176_, lean_object* v_h__3_177_, lean_object* v_h__4_178_){
_start:
{
uint8_t v_m_65__boxed_179_; lean_object* v_res_180_; 
v_m_65__boxed_179_ = lean_unbox(v_m_174_);
v_res_180_ = lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanConvergenceFinal_0__SSEM_majorityOpinionOfAnswerBCF_match__1_splitter(v_motive_173_, v_m_65__boxed_179_, v_h__1_175_, v_h__2_176_, v_h__3_177_, v_h__4_178_);
return v_res_180_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_phiCount___lam__0(lean_object* v_C_181_, lean_object* v_a_182_){
_start:
{
lean_object* v___x_183_; lean_object* v_fst_184_; uint8_t v_answer_185_; uint8_t v___x_186_; uint8_t v___x_187_; 
v___x_183_ = lean_apply_1(v_C_181_, v_a_182_);
v_fst_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_fst_184_);
lean_dec_ref(v___x_183_);
v_answer_185_ = lean_ctor_get_uint8(v_fst_184_, sizeof(void*)*6 + 2);
lean_dec(v_fst_184_);
v___x_186_ = 0;
v___x_187_ = lp_SSExactMajority_SSEM_instDecidableEqAnswer(v_answer_185_, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phiCount___lam__0___boxed(lean_object* v_C_188_, lean_object* v_a_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = lp_SSExactMajority_SSEM_phiCount___lam__0(v_C_188_, v_a_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phiCount(lean_object* v_n_192_, lean_object* v_C_193_){
_start:
{
lean_object* v___f_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___f_194_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_phiCount___lam__0___boxed), 2, 1);
lean_closure_set(v___f_194_, 0, v_C_193_);
v___x_195_ = l_List_finRange(v_n_192_);
v___x_196_ = lp_mathlib_Multiset_filter___redArg(v___f_194_, v___x_195_);
v___x_197_ = l_List_lengthTR___redArg(v___x_196_);
lean_dec(v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_unrecruitedTargetRanks___lam__0(lean_object* v_C_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_201_; lean_object* v_fst_202_; uint8_t v_role_203_; lean_object* v_rank_204_; uint8_t v___x_205_; uint8_t v___x_206_; 
v___x_201_ = lean_apply_1(v_C_198_, v_a_200_);
v_fst_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_fst_202_);
lean_dec_ref(v___x_201_);
v_role_203_ = lean_ctor_get_uint8(v_fst_202_, sizeof(void*)*6);
v_rank_204_ = lean_ctor_get(v_fst_202_, 0);
lean_inc(v_rank_204_);
lean_dec(v_fst_202_);
v___x_205_ = 1;
v___x_206_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_203_, v___x_205_);
if (v___x_206_ == 0)
{
lean_dec(v_rank_204_);
return v___x_206_;
}
else
{
uint8_t v___x_207_; 
v___x_207_ = lean_nat_dec_eq(v_rank_204_, v_a_199_);
lean_dec(v_rank_204_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unrecruitedTargetRanks___lam__0___boxed(lean_object* v_C_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = lp_SSExactMajority_SSEM_unrecruitedTargetRanks___lam__0(v_C_208_, v_a_209_, v_a_210_);
lean_dec(v_a_209_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_unrecruitedTargetRanks___lam__1(lean_object* v_C_213_, lean_object* v_n_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___f_216_; uint8_t v___x_217_; 
v___f_216_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_unrecruitedTargetRanks___lam__0___boxed), 3, 2);
lean_closure_set(v___f_216_, 0, v_C_213_);
lean_closure_set(v___f_216_, 1, v_a_215_);
v___x_217_ = l_Nat_decidableExistsFin___redArg(v_n_214_, v___f_216_);
if (v___x_217_ == 0)
{
uint8_t v___x_218_; 
v___x_218_ = 1;
return v___x_218_;
}
else
{
uint8_t v___x_219_; 
v___x_219_ = 0;
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unrecruitedTargetRanks___lam__1___boxed(lean_object* v_C_220_, lean_object* v_n_221_, lean_object* v_a_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = lp_SSExactMajority_SSEM_unrecruitedTargetRanks___lam__1(v_C_220_, v_n_221_, v_a_222_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unrecruitedTargetRanks(lean_object* v_n_225_, lean_object* v_C_226_){
_start:
{
lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
lean_inc(v_n_225_);
v___f_227_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_unrecruitedTargetRanks___lam__1___boxed), 3, 2);
lean_closure_set(v___f_227_, 0, v_C_226_);
lean_closure_set(v___f_227_, 1, v_n_225_);
v___x_228_ = l_List_finRange(v_n_225_);
v___x_229_ = lp_mathlib_Multiset_filter___redArg(v___f_227_, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unrecruitedTargetRankCount(lean_object* v_n_230_, lean_object* v_C_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lp_SSExactMajority_SSEM_unrecruitedTargetRanks(v_n_230_, v_C_231_);
v___x_233_ = l_List_lengthTR___redArg(v___x_232_);
lean_dec(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rank1___redArg(lean_object* v_D_234_, lean_object* v_u_235_){
_start:
{
lean_object* v___x_236_; lean_object* v_fst_237_; lean_object* v_rank_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_236_ = lean_apply_1(v_D_234_, v_u_235_);
v_fst_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_fst_237_);
lean_dec_ref(v___x_236_);
v_rank_238_ = lean_ctor_get(v_fst_237_, 0);
lean_inc(v_rank_238_);
lean_dec(v_fst_237_);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_add(v_rank_238_, v___x_239_);
lean_dec(v_rank_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rank1(lean_object* v_n_241_, lean_object* v_D_242_, lean_object* v_u_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lp_SSExactMajority_SSEM_rank1___redArg(v_D_242_, v_u_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_rank1___boxed(lean_object* v_n_245_, lean_object* v_D_246_, lean_object* v_u_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = lp_SSExactMajority_SSEM_rank1(v_n_245_, v_D_246_, v_u_247_);
lean_dec(v_n_245_);
return v_res_248_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_BurmanProof(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_BurmanConvergenceFinal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_BurmanProof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
