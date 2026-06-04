// Lean compiler output
// Module: SSExactMajority.Probability.RandomScheduler
// Imports: public import Init public meta import Init public import Mathlib.Probability.ProbabilityMassFunction.Constructions public import Mathlib.Probability.Distributions.Uniform public import SSExactMajority.Defs.Execution
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
lean_object* lp_SSExactMajority_SSEM_Config_step___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Probability_OffDiagonalPairs___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Probability_OffDiagonalPairs___lam__0___boxed(lean_object*);
static const lean_closure_object lp_SSExactMajority_SSEM_Probability_OffDiagonalPairs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SSExactMajority_SSEM_Probability_OffDiagonalPairs___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SSExactMajority_SSEM_Probability_OffDiagonalPairs___closed__0 = (const lean_object*)&lp_SSExactMajority_SSEM_Probability_OffDiagonalPairs___closed__0_value;
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Probability_OffDiagonalPairs(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Probability_PairsInvolving___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Probability_PairsInvolving___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Probability_PairsInvolving(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Probability_GoodPairs___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Probability_GoodPairs___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Probability_GoodPairs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Probability_GoodPairs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_RandomScheduler_0__SSEM_Probability_nthStepDist_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_RandomScheduler_0__SSEM_Probability_nthStepDist_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_RandomScheduler_0__SSEM_Probability_nthStepDist_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_RandomScheduler_0__SSEM_Probability_nthStepDist_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Probability_OffDiagonalPairs___lam__0(lean_object* v_a_1_){
_start:
{
lean_object* v_fst_2_; lean_object* v_snd_3_; uint8_t v___x_4_; 
v_fst_2_ = lean_ctor_get(v_a_1_, 0);
v_snd_3_ = lean_ctor_get(v_a_1_, 1);
v___x_4_ = lean_nat_dec_eq(v_fst_2_, v_snd_3_);
if (v___x_4_ == 0)
{
uint8_t v___x_5_; 
v___x_5_ = 1;
return v___x_5_;
}
else
{
uint8_t v___x_6_; 
v___x_6_ = 0;
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Probability_OffDiagonalPairs___lam__0___boxed(lean_object* v_a_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = lp_SSExactMajority_SSEM_Probability_OffDiagonalPairs___lam__0(v_a_7_);
lean_dec_ref(v_a_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Probability_OffDiagonalPairs(lean_object* v_n_11_){
_start:
{
lean_object* v___f_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___f_12_ = ((lean_object*)(lp_SSExactMajority_SSEM_Probability_OffDiagonalPairs___closed__0));
v___x_13_ = l_List_finRange(v_n_11_);
lean_inc(v___x_13_);
v___x_14_ = lp_mathlib_Multiset_product___redArg(v___x_13_, v___x_13_);
v___x_15_ = lp_mathlib_Multiset_filter___redArg(v___f_12_, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Probability_PairsInvolving___lam__0(lean_object* v_i_16_, lean_object* v_a_17_){
_start:
{
lean_object* v_fst_18_; lean_object* v_snd_19_; uint8_t v___x_20_; 
v_fst_18_ = lean_ctor_get(v_a_17_, 0);
v_snd_19_ = lean_ctor_get(v_a_17_, 1);
v___x_20_ = lean_nat_dec_eq(v_fst_18_, v_i_16_);
if (v___x_20_ == 0)
{
uint8_t v___x_21_; 
v___x_21_ = lean_nat_dec_eq(v_snd_19_, v_i_16_);
return v___x_21_;
}
else
{
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Probability_PairsInvolving___lam__0___boxed(lean_object* v_i_22_, lean_object* v_a_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = lp_SSExactMajority_SSEM_Probability_PairsInvolving___lam__0(v_i_22_, v_a_23_);
lean_dec_ref(v_a_23_);
lean_dec(v_i_22_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Probability_PairsInvolving(lean_object* v_n_26_, lean_object* v_i_27_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___f_28_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_Probability_PairsInvolving___lam__0___boxed), 2, 1);
lean_closure_set(v___f_28_, 0, v_i_27_);
v___x_29_ = lp_SSExactMajority_SSEM_Probability_OffDiagonalPairs(v_n_26_);
v___x_30_ = lp_mathlib_Multiset_filter___redArg(v___f_28_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Probability_GoodPairs___redArg___lam__0(lean_object* v_n_31_, lean_object* v_P_32_, lean_object* v_C_33_, lean_object* v_00_u03c6_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_fst_36_; lean_object* v_snd_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v_fst_36_ = lean_ctor_get(v_a_35_, 0);
lean_inc(v_fst_36_);
v_snd_37_ = lean_ctor_get(v_a_35_, 1);
lean_inc(v_snd_37_);
lean_dec_ref(v_a_35_);
lean_inc_ref(v_C_33_);
v___x_38_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_Config_step___boxed), 9, 8);
lean_closure_set(v___x_38_, 0, lean_box(0));
lean_closure_set(v___x_38_, 1, lean_box(0));
lean_closure_set(v___x_38_, 2, lean_box(0));
lean_closure_set(v___x_38_, 3, v_n_31_);
lean_closure_set(v___x_38_, 4, v_P_32_);
lean_closure_set(v___x_38_, 5, v_C_33_);
lean_closure_set(v___x_38_, 6, v_fst_36_);
lean_closure_set(v___x_38_, 7, v_snd_37_);
lean_inc_ref(v_00_u03c6_34_);
v___x_39_ = lean_apply_1(v_00_u03c6_34_, v___x_38_);
v___x_40_ = lean_apply_1(v_00_u03c6_34_, v_C_33_);
v___x_41_ = lean_nat_dec_lt(v___x_39_, v___x_40_);
lean_dec(v___x_40_);
lean_dec(v___x_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Probability_GoodPairs___redArg___lam__0___boxed(lean_object* v_n_42_, lean_object* v_P_43_, lean_object* v_C_44_, lean_object* v_00_u03c6_45_, lean_object* v_a_46_){
_start:
{
uint8_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = lp_SSExactMajority_SSEM_Probability_GoodPairs___redArg___lam__0(v_n_42_, v_P_43_, v_C_44_, v_00_u03c6_45_, v_a_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Probability_GoodPairs___redArg(lean_object* v_n_49_, lean_object* v_P_50_, lean_object* v_00_u03c6_51_, lean_object* v_C_52_){
_start:
{
lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
lean_inc(v_n_49_);
v___f_53_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_Probability_GoodPairs___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_53_, 0, v_n_49_);
lean_closure_set(v___f_53_, 1, v_P_50_);
lean_closure_set(v___f_53_, 2, v_C_52_);
lean_closure_set(v___f_53_, 3, v_00_u03c6_51_);
v___x_54_ = lp_SSExactMajority_SSEM_Probability_OffDiagonalPairs(v_n_49_);
v___x_55_ = lp_mathlib_Multiset_filter___redArg(v___f_53_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Probability_GoodPairs(lean_object* v_Q_56_, lean_object* v_X_57_, lean_object* v_Y_58_, lean_object* v_n_59_, lean_object* v_P_60_, lean_object* v_00_u03c6_61_, lean_object* v_C_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lp_SSExactMajority_SSEM_Probability_GoodPairs___redArg(v_n_59_, v_P_60_, v_00_u03c6_61_, v_C_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_RandomScheduler_0__SSEM_Probability_nthStepDist_match__1_splitter___redArg(lean_object* v_x_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_){
_start:
{
lean_object* v_zero_67_; uint8_t v_isZero_68_; 
v_zero_67_ = lean_unsigned_to_nat(0u);
v_isZero_68_ = lean_nat_dec_eq(v_x_64_, v_zero_67_);
if (v_isZero_68_ == 1)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_h__2_66_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_apply_1(v_h__1_65_, v___x_69_);
return v___x_70_;
}
else
{
lean_object* v_one_71_; lean_object* v_n_72_; lean_object* v___x_73_; 
lean_dec(v_h__1_65_);
v_one_71_ = lean_unsigned_to_nat(1u);
v_n_72_ = lean_nat_sub(v_x_64_, v_one_71_);
v___x_73_ = lean_apply_1(v_h__2_66_, v_n_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_RandomScheduler_0__SSEM_Probability_nthStepDist_match__1_splitter___redArg___boxed(lean_object* v_x_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_SSExactMajority___private_SSExactMajority_Probability_RandomScheduler_0__SSEM_Probability_nthStepDist_match__1_splitter___redArg(v_x_74_, v_h__1_75_, v_h__2_76_);
lean_dec(v_x_74_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_RandomScheduler_0__SSEM_Probability_nthStepDist_match__1_splitter(lean_object* v_motive_78_, lean_object* v_x_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
_start:
{
lean_object* v_zero_82_; uint8_t v_isZero_83_; 
v_zero_82_ = lean_unsigned_to_nat(0u);
v_isZero_83_ = lean_nat_dec_eq(v_x_79_, v_zero_82_);
if (v_isZero_83_ == 1)
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_h__2_81_);
v___x_84_ = lean_box(0);
v___x_85_ = lean_apply_1(v_h__1_80_, v___x_84_);
return v___x_85_;
}
else
{
lean_object* v_one_86_; lean_object* v_n_87_; lean_object* v___x_88_; 
lean_dec(v_h__1_80_);
v_one_86_ = lean_unsigned_to_nat(1u);
v_n_87_ = lean_nat_sub(v_x_79_, v_one_86_);
v___x_88_ = lean_apply_1(v_h__2_81_, v_n_87_);
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_RandomScheduler_0__SSEM_Probability_nthStepDist_match__1_splitter___boxed(lean_object* v_motive_89_, lean_object* v_x_90_, lean_object* v_h__1_91_, lean_object* v_h__2_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = lp_SSExactMajority___private_SSExactMajority_Probability_RandomScheduler_0__SSEM_Probability_nthStepDist_match__1_splitter(v_motive_89_, v_x_90_, v_h__1_91_, v_h__2_92_);
lean_dec(v_x_90_);
return v_res_93_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Probability_ProbabilityMassFunction_Constructions(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Probability_Distributions_Uniform(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Execution(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Probability_RandomScheduler(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Probability_ProbabilityMassFunction_Constructions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Probability_Distributions_Uniform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Defs_Execution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
