// Lean compiler output
// Module: SSExactMajority.Convergence.BurmanProof
// Imports: public import Init public meta import Init public import SSExactMajority.Convergence.BurmanProperties public import Mathlib.Algebra.Order.BigOperators.Group.Finset public import Mathlib.Data.Fintype.Card
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
lean_object* lp_SSExactMajority_SSEM_Config_step___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqRole(uint8_t, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_getD___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqLeader(uint8_t, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_settledCount___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_settledCount___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_settledCount(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_unsettledCount___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledCount___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledCount(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_foldl___at___00SSEM_runPairs_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_foldl___at___00SSEM_runPairs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_runPairs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_runPairs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_runPairs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_runPairs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_foldl___at___00SSEM_runPairs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_foldl___at___00SSEM_runPairs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_schedOfList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_schedOfList___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_schedOfList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_schedOfList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledContribution___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledContribution___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledContribution(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledContribution___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledMass___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_SSExactMajority_Multiset_sum___at___00Finset_sum___at___00SSEM_unsettledMass_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SSExactMajority_Multiset_sum___at___00Finset_sum___at___00SSEM_unsettledMass_spec__0_spec__0___closed__0 = (const lean_object*)&lp_SSExactMajority_Multiset_sum___at___00Finset_sum___at___00SSEM_unsettledMass_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_sum___at___00Finset_sum___at___00SSEM_unsettledMass_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_sum___at___00SSEM_unsettledMass_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledMass(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_sum___at___00SSEM_unsettledMass_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanProof_0__SSEM_transitionPEM_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanProof_0__SSEM_transitionPEM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanProof_0__SSEM_transitionPEM_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_nonResettingCount___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nonResettingCount___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nonResettingCount(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_resetLeaderCount___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetLeaderCount___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetLeaderCount(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_positiveRcExcept___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_positiveRcExcept___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_positiveRcExcept(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_positiveRcAgents___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_positiveRcAgents___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_positiveRcAgents(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_resettingCount___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resettingCount___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resettingCount(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_followerDormantContribution___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_followerDormantContribution___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_followerDormantContribution(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_followerDormantContribution___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_followerDormantMeasure___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_followerDormantMeasure(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_awakeningResettingFollowers___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_awakeningResettingFollowers___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_awakeningResettingFollowers(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_heapParent(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_heapParent___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_heapChildIndex(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_heapChildIndex___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_heapChildrenBefore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_heapChildrenBefore___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_settledCount___lam__0(lean_object* v_C_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; lean_object* v_fst_4_; uint8_t v_role_5_; uint8_t v___x_6_; uint8_t v___x_7_; 
v___x_3_ = lean_apply_1(v_C_1_, v_a_2_);
v_fst_4_ = lean_ctor_get(v___x_3_, 0);
lean_inc(v_fst_4_);
lean_dec_ref(v___x_3_);
v_role_5_ = lean_ctor_get_uint8(v_fst_4_, sizeof(void*)*6);
lean_dec(v_fst_4_);
v___x_6_ = 1;
v___x_7_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_settledCount___lam__0___boxed(lean_object* v_C_8_, lean_object* v_a_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = lp_SSExactMajority_SSEM_settledCount___lam__0(v_C_8_, v_a_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_settledCount(lean_object* v_n_12_, lean_object* v_C_13_){
_start:
{
lean_object* v___f_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___f_14_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_settledCount___lam__0___boxed), 2, 1);
lean_closure_set(v___f_14_, 0, v_C_13_);
v___x_15_ = l_List_finRange(v_n_12_);
v___x_16_ = lp_mathlib_Multiset_filter___redArg(v___f_14_, v___x_15_);
v___x_17_ = l_List_lengthTR___redArg(v___x_16_);
lean_dec(v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_unsettledCount___lam__0(lean_object* v_C_18_, lean_object* v_a_19_){
_start:
{
lean_object* v___x_20_; lean_object* v_fst_21_; uint8_t v_role_22_; uint8_t v___x_23_; uint8_t v___x_24_; 
v___x_20_ = lean_apply_1(v_C_18_, v_a_19_);
v_fst_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_fst_21_);
lean_dec_ref(v___x_20_);
v_role_22_ = lean_ctor_get_uint8(v_fst_21_, sizeof(void*)*6);
lean_dec(v_fst_21_);
v___x_23_ = 2;
v___x_24_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_22_, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledCount___lam__0___boxed(lean_object* v_C_25_, lean_object* v_a_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = lp_SSExactMajority_SSEM_unsettledCount___lam__0(v_C_25_, v_a_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledCount(lean_object* v_n_29_, lean_object* v_C_30_){
_start:
{
lean_object* v___f_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___f_31_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_unsettledCount___lam__0___boxed), 2, 1);
lean_closure_set(v___f_31_, 0, v_C_30_);
v___x_32_ = l_List_finRange(v_n_29_);
v___x_33_ = lp_mathlib_Multiset_filter___redArg(v___f_31_, v___x_32_);
v___x_34_ = l_List_lengthTR___redArg(v___x_33_);
lean_dec(v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_foldl___at___00SSEM_runPairs_spec__0___redArg___lam__0(lean_object* v_head_35_, lean_object* v_P_36_, lean_object* v_x_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_fst_39_; lean_object* v_snd_40_; lean_object* v___x_41_; 
v_fst_39_ = lean_ctor_get(v_head_35_, 0);
lean_inc(v_fst_39_);
v_snd_40_ = lean_ctor_get(v_head_35_, 1);
lean_inc(v_snd_40_);
lean_dec_ref(v_head_35_);
v___x_41_ = lp_SSExactMajority_SSEM_Config_step___redArg(v_P_36_, v_x_37_, v_fst_39_, v_snd_40_, v___y_38_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_foldl___at___00SSEM_runPairs_spec__0___redArg(lean_object* v_P_42_, lean_object* v_x_43_, lean_object* v_x_44_, lean_object* v___y_45_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v___x_46_; 
lean_dec_ref(v_P_42_);
v___x_46_ = lean_apply_1(v_x_43_, v___y_45_);
return v___x_46_;
}
else
{
lean_object* v_head_47_; lean_object* v_tail_48_; lean_object* v___f_49_; 
v_head_47_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_head_47_);
v_tail_48_ = lean_ctor_get(v_x_44_, 1);
lean_inc(v_tail_48_);
lean_dec_ref(v_x_44_);
lean_inc_ref(v_P_42_);
v___f_49_ = lean_alloc_closure((void*)(lp_SSExactMajority_List_foldl___at___00SSEM_runPairs_spec__0___redArg___lam__0), 4, 3);
lean_closure_set(v___f_49_, 0, v_head_47_);
lean_closure_set(v___f_49_, 1, v_P_42_);
lean_closure_set(v___f_49_, 2, v_x_43_);
v_x_43_ = v___f_49_;
v_x_44_ = v_tail_48_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_runPairs___redArg(lean_object* v_n_51_, lean_object* v_P_52_, lean_object* v_C_53_, lean_object* v_L_54_, lean_object* v_a_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lp_SSExactMajority_List_foldl___at___00SSEM_runPairs_spec__0___redArg(v_P_52_, v_C_53_, v_L_54_, v_a_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_runPairs___redArg___boxed(lean_object* v_n_57_, lean_object* v_P_58_, lean_object* v_C_59_, lean_object* v_L_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_SSExactMajority_SSEM_runPairs___redArg(v_n_57_, v_P_58_, v_C_59_, v_L_60_, v_a_61_);
lean_dec(v_n_57_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_runPairs(lean_object* v_n_63_, lean_object* v_Q_64_, lean_object* v_X_65_, lean_object* v_Y_66_, lean_object* v_P_67_, lean_object* v_C_68_, lean_object* v_L_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lp_SSExactMajority_List_foldl___at___00SSEM_runPairs_spec__0___redArg(v_P_67_, v_C_68_, v_L_69_, v_a_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_runPairs___boxed(lean_object* v_n_72_, lean_object* v_Q_73_, lean_object* v_X_74_, lean_object* v_Y_75_, lean_object* v_P_76_, lean_object* v_C_77_, lean_object* v_L_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = lp_SSExactMajority_SSEM_runPairs(v_n_72_, v_Q_73_, v_X_74_, v_Y_75_, v_P_76_, v_C_77_, v_L_78_, v_a_79_);
lean_dec(v_n_72_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_foldl___at___00SSEM_runPairs_spec__0(lean_object* v_Q_81_, lean_object* v_X_82_, lean_object* v_Y_83_, lean_object* v_n_84_, lean_object* v_P_85_, lean_object* v_x_86_, lean_object* v_x_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lp_SSExactMajority_List_foldl___at___00SSEM_runPairs_spec__0___redArg(v_P_85_, v_x_86_, v_x_87_, v___y_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_foldl___at___00SSEM_runPairs_spec__0___boxed(lean_object* v_Q_90_, lean_object* v_X_91_, lean_object* v_Y_92_, lean_object* v_n_93_, lean_object* v_P_94_, lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = lp_SSExactMajority_List_foldl___at___00SSEM_runPairs_spec__0(v_Q_90_, v_X_91_, v_Y_92_, v_n_93_, v_P_94_, v_x_95_, v_x_96_, v___y_97_);
lean_dec(v_n_93_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_schedOfList___redArg(lean_object* v_inst_99_, lean_object* v_L_100_, lean_object* v_t_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_List_getD___redArg(v_L_100_, v_t_101_, v_inst_99_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_schedOfList___redArg___boxed(lean_object* v_inst_103_, lean_object* v_L_104_, lean_object* v_t_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = lp_SSExactMajority_SSEM_schedOfList___redArg(v_inst_103_, v_L_104_, v_t_105_);
lean_dec(v_L_104_);
lean_dec_ref(v_inst_103_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_schedOfList(lean_object* v_n_107_, lean_object* v_inst_108_, lean_object* v_L_109_, lean_object* v_t_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_List_getD___redArg(v_L_109_, v_t_110_, v_inst_108_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_schedOfList___boxed(lean_object* v_n_112_, lean_object* v_inst_113_, lean_object* v_L_114_, lean_object* v_t_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = lp_SSExactMajority_SSEM_schedOfList(v_n_112_, v_inst_113_, v_L_114_, v_t_115_);
lean_dec(v_L_114_);
lean_dec_ref(v_inst_113_);
lean_dec(v_n_112_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledContribution___redArg(lean_object* v_s_117_){
_start:
{
uint8_t v_role_118_; lean_object* v_errorcount_119_; uint8_t v___x_120_; uint8_t v___x_121_; 
v_role_118_ = lean_ctor_get_uint8(v_s_117_, sizeof(void*)*6);
v_errorcount_119_ = lean_ctor_get(v_s_117_, 4);
v___x_120_ = 2;
v___x_121_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_118_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
v___x_122_ = lean_unsigned_to_nat(0u);
return v___x_122_;
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_add(v_errorcount_119_, v___x_123_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledContribution___redArg___boxed(lean_object* v_s_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = lp_SSExactMajority_SSEM_unsettledContribution___redArg(v_s_125_);
lean_dec_ref(v_s_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledContribution(lean_object* v_n_127_, lean_object* v_s_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lp_SSExactMajority_SSEM_unsettledContribution___redArg(v_s_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledContribution___boxed(lean_object* v_n_130_, lean_object* v_s_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = lp_SSExactMajority_SSEM_unsettledContribution(v_n_130_, v_s_131_);
lean_dec_ref(v_s_131_);
lean_dec(v_n_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledMass___lam__0(lean_object* v_C_133_, lean_object* v_w_134_){
_start:
{
lean_object* v___x_135_; lean_object* v_fst_136_; lean_object* v___x_137_; 
v___x_135_ = lean_apply_1(v_C_133_, v_w_134_);
v_fst_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_fst_136_);
lean_dec_ref(v___x_135_);
v___x_137_ = lp_SSExactMajority_SSEM_unsettledContribution___redArg(v_fst_136_);
lean_dec(v_fst_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_sum___at___00Finset_sum___at___00SSEM_unsettledMass_spec__0_spec__0(lean_object* v_s_139_){
_start:
{
lean_object* v___f_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___f_140_ = ((lean_object*)(lp_SSExactMajority_Multiset_sum___at___00Finset_sum___at___00SSEM_unsettledMass_spec__0_spec__0___closed__0));
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = l_List_foldrTR___redArg(v___f_140_, v___x_141_, v_s_139_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_sum___at___00SSEM_unsettledMass_spec__0___redArg(lean_object* v_s_143_, lean_object* v_f_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lp_mathlib_Multiset_map___redArg(v_f_144_, v_s_143_);
v___x_146_ = lp_SSExactMajority_Multiset_sum___at___00Finset_sum___at___00SSEM_unsettledMass_spec__0_spec__0(v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_unsettledMass(lean_object* v_n_147_, lean_object* v_C_148_){
_start:
{
lean_object* v___f_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___f_149_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_unsettledMass___lam__0), 2, 1);
lean_closure_set(v___f_149_, 0, v_C_148_);
v___x_150_ = l_List_finRange(v_n_147_);
v___x_151_ = lp_SSExactMajority_Finset_sum___at___00SSEM_unsettledMass_spec__0___redArg(v___x_150_, v___f_149_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_sum___at___00SSEM_unsettledMass_spec__0(lean_object* v_00_u03b9_152_, lean_object* v_s_153_, lean_object* v_f_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lp_SSExactMajority_Finset_sum___at___00SSEM_unsettledMass_spec__0___redArg(v_s_153_, v_f_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanProof_0__SSEM_transitionPEM_match__1_splitter___redArg(lean_object* v_x_156_, lean_object* v_h__1_157_){
_start:
{
lean_object* v_fst_158_; lean_object* v_snd_159_; lean_object* v_fst_160_; lean_object* v_snd_161_; lean_object* v_fst_162_; lean_object* v_snd_163_; lean_object* v___x_164_; 
v_fst_158_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_fst_158_);
v_snd_159_ = lean_ctor_get(v_x_156_, 1);
lean_inc(v_snd_159_);
lean_dec_ref(v_x_156_);
v_fst_160_ = lean_ctor_get(v_fst_158_, 0);
lean_inc(v_fst_160_);
v_snd_161_ = lean_ctor_get(v_fst_158_, 1);
lean_inc(v_snd_161_);
lean_dec(v_fst_158_);
v_fst_162_ = lean_ctor_get(v_snd_159_, 0);
lean_inc(v_fst_162_);
v_snd_163_ = lean_ctor_get(v_snd_159_, 1);
lean_inc(v_snd_163_);
lean_dec(v_snd_159_);
v___x_164_ = lean_apply_4(v_h__1_157_, v_fst_160_, v_snd_161_, v_fst_162_, v_snd_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanProof_0__SSEM_transitionPEM_match__1_splitter(lean_object* v_n_165_, lean_object* v_motive_166_, lean_object* v_x_167_, lean_object* v_h__1_168_){
_start:
{
lean_object* v_fst_169_; lean_object* v_snd_170_; lean_object* v_fst_171_; lean_object* v_snd_172_; lean_object* v_fst_173_; lean_object* v_snd_174_; lean_object* v___x_175_; 
v_fst_169_ = lean_ctor_get(v_x_167_, 0);
lean_inc(v_fst_169_);
v_snd_170_ = lean_ctor_get(v_x_167_, 1);
lean_inc(v_snd_170_);
lean_dec_ref(v_x_167_);
v_fst_171_ = lean_ctor_get(v_fst_169_, 0);
lean_inc(v_fst_171_);
v_snd_172_ = lean_ctor_get(v_fst_169_, 1);
lean_inc(v_snd_172_);
lean_dec(v_fst_169_);
v_fst_173_ = lean_ctor_get(v_snd_170_, 0);
lean_inc(v_fst_173_);
v_snd_174_ = lean_ctor_get(v_snd_170_, 1);
lean_inc(v_snd_174_);
lean_dec(v_snd_170_);
v___x_175_ = lean_apply_4(v_h__1_168_, v_fst_171_, v_snd_172_, v_fst_173_, v_snd_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanProof_0__SSEM_transitionPEM_match__1_splitter___boxed(lean_object* v_n_176_, lean_object* v_motive_177_, lean_object* v_x_178_, lean_object* v_h__1_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = lp_SSExactMajority___private_SSExactMajority_Convergence_BurmanProof_0__SSEM_transitionPEM_match__1_splitter(v_n_176_, v_motive_177_, v_x_178_, v_h__1_179_);
lean_dec(v_n_176_);
return v_res_180_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_nonResettingCount___lam__0(lean_object* v_C_181_, lean_object* v_a_182_){
_start:
{
lean_object* v___x_183_; lean_object* v_fst_184_; uint8_t v_role_185_; uint8_t v___x_186_; uint8_t v___x_187_; 
v___x_183_ = lean_apply_1(v_C_181_, v_a_182_);
v_fst_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_fst_184_);
lean_dec_ref(v___x_183_);
v_role_185_ = lean_ctor_get_uint8(v_fst_184_, sizeof(void*)*6);
lean_dec(v_fst_184_);
v___x_186_ = 0;
v___x_187_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_185_, v___x_186_);
if (v___x_187_ == 0)
{
uint8_t v___x_188_; 
v___x_188_ = 1;
return v___x_188_;
}
else
{
uint8_t v___x_189_; 
v___x_189_ = 0;
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nonResettingCount___lam__0___boxed(lean_object* v_C_190_, lean_object* v_a_191_){
_start:
{
uint8_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = lp_SSExactMajority_SSEM_nonResettingCount___lam__0(v_C_190_, v_a_191_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nonResettingCount(lean_object* v_n_194_, lean_object* v_C_195_){
_start:
{
lean_object* v___f_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___f_196_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_nonResettingCount___lam__0___boxed), 2, 1);
lean_closure_set(v___f_196_, 0, v_C_195_);
v___x_197_ = l_List_finRange(v_n_194_);
v___x_198_ = lp_mathlib_Multiset_filter___redArg(v___f_196_, v___x_197_);
v___x_199_ = l_List_lengthTR___redArg(v___x_198_);
lean_dec(v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_resetLeaderCount___lam__0(lean_object* v_C_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___x_202_; lean_object* v_fst_203_; uint8_t v_role_204_; uint8_t v_leader_205_; lean_object* v_resetcount_206_; uint8_t v___x_207_; uint8_t v___x_208_; 
v___x_202_ = lean_apply_1(v_C_200_, v_a_201_);
v_fst_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_fst_203_);
lean_dec_ref(v___x_202_);
v_role_204_ = lean_ctor_get_uint8(v_fst_203_, sizeof(void*)*6);
v_leader_205_ = lean_ctor_get_uint8(v_fst_203_, sizeof(void*)*6 + 1);
v_resetcount_206_ = lean_ctor_get(v_fst_203_, 1);
lean_inc(v_resetcount_206_);
lean_dec(v_fst_203_);
v___x_207_ = 0;
v___x_208_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_204_, v___x_207_);
if (v___x_208_ == 0)
{
lean_dec(v_resetcount_206_);
return v___x_208_;
}
else
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_nat_dec_eq(v_resetcount_206_, v___x_209_);
lean_dec(v_resetcount_206_);
if (v___x_210_ == 0)
{
return v___x_210_;
}
else
{
uint8_t v___x_211_; uint8_t v___x_212_; 
v___x_211_ = 0;
v___x_212_ = lp_SSExactMajority_SSEM_instDecidableEqLeader(v_leader_205_, v___x_211_);
return v___x_212_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetLeaderCount___lam__0___boxed(lean_object* v_C_213_, lean_object* v_a_214_){
_start:
{
uint8_t v_res_215_; lean_object* v_r_216_; 
v_res_215_ = lp_SSExactMajority_SSEM_resetLeaderCount___lam__0(v_C_213_, v_a_214_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resetLeaderCount(lean_object* v_n_217_, lean_object* v_C_218_){
_start:
{
lean_object* v___f_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___f_219_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_resetLeaderCount___lam__0___boxed), 2, 1);
lean_closure_set(v___f_219_, 0, v_C_218_);
v___x_220_ = l_List_finRange(v_n_217_);
v___x_221_ = lp_mathlib_Multiset_filter___redArg(v___f_219_, v___x_220_);
v___x_222_ = l_List_lengthTR___redArg(v___x_221_);
lean_dec(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_positiveRcExcept___lam__0(lean_object* v_00_u2113_223_, lean_object* v_C_224_, lean_object* v_a_225_){
_start:
{
uint8_t v___x_226_; 
v___x_226_ = lean_nat_dec_eq(v_a_225_, v_00_u2113_223_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v_fst_228_; lean_object* v_resetcount_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_227_ = lean_apply_1(v_C_224_, v_a_225_);
v_fst_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_fst_228_);
lean_dec_ref(v___x_227_);
v_resetcount_229_ = lean_ctor_get(v_fst_228_, 1);
lean_inc(v_resetcount_229_);
lean_dec(v_fst_228_);
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_nat_dec_lt(v___x_230_, v_resetcount_229_);
lean_dec(v_resetcount_229_);
return v___x_231_;
}
else
{
uint8_t v___x_232_; 
lean_dec(v_a_225_);
lean_dec_ref(v_C_224_);
v___x_232_ = 0;
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_positiveRcExcept___lam__0___boxed(lean_object* v_00_u2113_233_, lean_object* v_C_234_, lean_object* v_a_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = lp_SSExactMajority_SSEM_positiveRcExcept___lam__0(v_00_u2113_233_, v_C_234_, v_a_235_);
lean_dec(v_00_u2113_233_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_positiveRcExcept(lean_object* v_n_238_, lean_object* v_C_239_, lean_object* v_00_u2113_240_){
_start:
{
lean_object* v___f_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___f_241_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_positiveRcExcept___lam__0___boxed), 3, 2);
lean_closure_set(v___f_241_, 0, v_00_u2113_240_);
lean_closure_set(v___f_241_, 1, v_C_239_);
v___x_242_ = l_List_finRange(v_n_238_);
v___x_243_ = lp_mathlib_Multiset_filter___redArg(v___f_241_, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_positiveRcAgents___lam__0(lean_object* v_C_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___x_246_; lean_object* v_fst_247_; lean_object* v_resetcount_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_246_ = lean_apply_1(v_C_244_, v_a_245_);
v_fst_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_fst_247_);
lean_dec_ref(v___x_246_);
v_resetcount_248_ = lean_ctor_get(v_fst_247_, 1);
lean_inc(v_resetcount_248_);
lean_dec(v_fst_247_);
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = lean_nat_dec_lt(v___x_249_, v_resetcount_248_);
lean_dec(v_resetcount_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_positiveRcAgents___lam__0___boxed(lean_object* v_C_251_, lean_object* v_a_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = lp_SSExactMajority_SSEM_positiveRcAgents___lam__0(v_C_251_, v_a_252_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_positiveRcAgents(lean_object* v_n_255_, lean_object* v_C_256_){
_start:
{
lean_object* v___f_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___f_257_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_positiveRcAgents___lam__0___boxed), 2, 1);
lean_closure_set(v___f_257_, 0, v_C_256_);
v___x_258_ = l_List_finRange(v_n_255_);
v___x_259_ = lp_mathlib_Multiset_filter___redArg(v___f_257_, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_resettingCount___lam__0(lean_object* v_C_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_262_; lean_object* v_fst_263_; uint8_t v_role_264_; uint8_t v___x_265_; uint8_t v___x_266_; 
v___x_262_ = lean_apply_1(v_C_260_, v_a_261_);
v_fst_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_fst_263_);
lean_dec_ref(v___x_262_);
v_role_264_ = lean_ctor_get_uint8(v_fst_263_, sizeof(void*)*6);
lean_dec(v_fst_263_);
v___x_265_ = 0;
v___x_266_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_264_, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resettingCount___lam__0___boxed(lean_object* v_C_267_, lean_object* v_a_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = lp_SSExactMajority_SSEM_resettingCount___lam__0(v_C_267_, v_a_268_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_resettingCount(lean_object* v_n_271_, lean_object* v_C_272_){
_start:
{
lean_object* v___f_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___f_273_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_resettingCount___lam__0___boxed), 2, 1);
lean_closure_set(v___f_273_, 0, v_C_272_);
v___x_274_ = l_List_finRange(v_n_271_);
v___x_275_ = lp_mathlib_Multiset_filter___redArg(v___f_273_, v___x_274_);
v___x_276_ = l_List_lengthTR___redArg(v___x_275_);
lean_dec(v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_followerDormantContribution___redArg(lean_object* v_s_277_){
_start:
{
uint8_t v_role_278_; lean_object* v_delaytimer_279_; uint8_t v___x_280_; uint8_t v___x_281_; 
v_role_278_ = lean_ctor_get_uint8(v_s_277_, sizeof(void*)*6);
v_delaytimer_279_ = lean_ctor_get(v_s_277_, 5);
v___x_280_ = 0;
v___x_281_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_278_, v___x_280_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; 
v___x_282_ = lean_unsigned_to_nat(0u);
return v___x_282_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(1u);
v___x_284_ = lean_nat_add(v_delaytimer_279_, v___x_283_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_followerDormantContribution___redArg___boxed(lean_object* v_s_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = lp_SSExactMajority_SSEM_followerDormantContribution___redArg(v_s_285_);
lean_dec_ref(v_s_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_followerDormantContribution(lean_object* v_n_287_, lean_object* v_s_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lp_SSExactMajority_SSEM_followerDormantContribution___redArg(v_s_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_followerDormantContribution___boxed(lean_object* v_n_290_, lean_object* v_s_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = lp_SSExactMajority_SSEM_followerDormantContribution(v_n_290_, v_s_291_);
lean_dec_ref(v_s_291_);
lean_dec(v_n_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_followerDormantMeasure___lam__0(lean_object* v_C_293_, lean_object* v_w_294_){
_start:
{
lean_object* v___x_295_; lean_object* v_fst_296_; lean_object* v___x_297_; 
v___x_295_ = lean_apply_1(v_C_293_, v_w_294_);
v_fst_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_fst_296_);
lean_dec_ref(v___x_295_);
v___x_297_ = lp_SSExactMajority_SSEM_followerDormantContribution___redArg(v_fst_296_);
lean_dec(v_fst_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_followerDormantMeasure(lean_object* v_n_298_, lean_object* v_C_299_){
_start:
{
lean_object* v___f_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___f_300_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_followerDormantMeasure___lam__0), 2, 1);
lean_closure_set(v___f_300_, 0, v_C_299_);
v___x_301_ = l_List_finRange(v_n_298_);
v___x_302_ = lp_SSExactMajority_Finset_sum___at___00SSEM_unsettledMass_spec__0___redArg(v___x_301_, v___f_300_);
return v___x_302_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_awakeningResettingFollowers___lam__0(lean_object* v_C_303_, lean_object* v_a_304_){
_start:
{
lean_object* v___x_305_; lean_object* v_fst_306_; uint8_t v_role_307_; uint8_t v_leader_308_; uint8_t v___x_309_; uint8_t v___x_310_; 
v___x_305_ = lean_apply_1(v_C_303_, v_a_304_);
v_fst_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_fst_306_);
lean_dec_ref(v___x_305_);
v_role_307_ = lean_ctor_get_uint8(v_fst_306_, sizeof(void*)*6);
v_leader_308_ = lean_ctor_get_uint8(v_fst_306_, sizeof(void*)*6 + 1);
lean_dec(v_fst_306_);
v___x_309_ = 1;
v___x_310_ = lp_SSExactMajority_SSEM_instDecidableEqLeader(v_leader_308_, v___x_309_);
if (v___x_310_ == 0)
{
return v___x_310_;
}
else
{
uint8_t v___x_311_; uint8_t v___x_312_; 
v___x_311_ = 0;
v___x_312_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_307_, v___x_311_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_awakeningResettingFollowers___lam__0___boxed(lean_object* v_C_313_, lean_object* v_a_314_){
_start:
{
uint8_t v_res_315_; lean_object* v_r_316_; 
v_res_315_ = lp_SSExactMajority_SSEM_awakeningResettingFollowers___lam__0(v_C_313_, v_a_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_awakeningResettingFollowers(lean_object* v_n_317_, lean_object* v_C_318_){
_start:
{
lean_object* v___f_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___f_319_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_awakeningResettingFollowers___lam__0___boxed), 2, 1);
lean_closure_set(v___f_319_, 0, v_C_318_);
v___x_320_ = l_List_finRange(v_n_317_);
v___x_321_ = lp_mathlib_Multiset_filter___redArg(v___f_319_, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_heapParent(lean_object* v_k_322_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_unsigned_to_nat(1u);
v___x_324_ = lean_nat_sub(v_k_322_, v___x_323_);
v___x_325_ = lean_nat_shiftr(v___x_324_, v___x_323_);
lean_dec(v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_heapParent___boxed(lean_object* v_k_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = lp_SSExactMajority_SSEM_heapParent(v_k_326_);
lean_dec(v_k_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_heapChildIndex(lean_object* v_k_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = lean_nat_sub(v_k_328_, v___x_329_);
v___x_331_ = lean_unsigned_to_nat(2u);
v___x_332_ = lean_nat_mod(v___x_330_, v___x_331_);
lean_dec(v___x_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_heapChildIndex___boxed(lean_object* v_k_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = lp_SSExactMajority_SSEM_heapChildIndex(v_k_333_);
lean_dec(v_k_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_heapChildrenBefore(lean_object* v_k_335_, lean_object* v_r_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___y_341_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_337_ = lean_unsigned_to_nat(2u);
v___x_338_ = lean_nat_mul(v___x_337_, v_r_336_);
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_345_ = lean_nat_add(v___x_338_, v___x_339_);
v___x_346_ = lean_nat_dec_lt(v___x_345_, v_k_335_);
lean_dec(v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
v___x_347_ = lean_unsigned_to_nat(0u);
v___y_341_ = v___x_347_;
goto v___jp_340_;
}
else
{
v___y_341_ = v___x_339_;
goto v___jp_340_;
}
v___jp_340_:
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = lean_nat_add(v___x_338_, v___x_337_);
lean_dec(v___x_338_);
v___x_343_ = lean_nat_dec_lt(v___x_342_, v_k_335_);
lean_dec(v___x_342_);
if (v___x_343_ == 0)
{
lean_inc(v___y_341_);
return v___y_341_;
}
else
{
lean_object* v___x_344_; 
v___x_344_ = lean_nat_add(v___y_341_, v___x_339_);
return v___x_344_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_heapChildrenBefore___boxed(lean_object* v_k_348_, lean_object* v_r_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = lp_SSExactMajority_SSEM_heapChildrenBefore(v_k_348_, v_r_349_);
lean_dec(v_r_349_);
lean_dec(v_k_348_);
return v_res_350_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_BurmanProperties(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Order_BigOperators_Group_Finset(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Card(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_BurmanProof(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_BurmanProperties(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Order_BigOperators_Group_Finset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Card(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
