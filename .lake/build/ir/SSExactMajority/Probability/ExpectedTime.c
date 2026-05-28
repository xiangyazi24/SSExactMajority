// Lean compiler output
// Module: SSExactMajority.Probability.ExpectedTime
// Imports: public import Init public meta import Init public import SSExactMajority.Probability.RandomScheduler public import SSExactMajority.Convergence.Silent public import Mathlib.Analysis.SpecificLimits.Basic public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov public import Mathlib.Topology.Instances.ENNReal.Lemmas
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDist_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDist_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDist_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDist_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDistFrom_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDistFrom_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDistFrom_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDistFrom_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDist_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_1_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_apply_1(v_h__1_2_, v___x_6_);
return v___x_7_;
}
else
{
lean_object* v_one_8_; lean_object* v_n_9_; lean_object* v___x_10_; 
lean_dec(v_h__1_2_);
v_one_8_ = lean_unsigned_to_nat(1u);
v_n_9_ = lean_nat_sub(v_x_1_, v_one_8_);
v___x_10_ = lean_apply_1(v_h__2_3_, v_n_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDist_match__1_splitter___redArg___boxed(lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDist_match__1_splitter___redArg(v_x_11_, v_h__1_12_, v_h__2_13_);
lean_dec(v_x_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDist_match__1_splitter(lean_object* v_motive_15_, lean_object* v_x_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_){
_start:
{
lean_object* v_zero_19_; uint8_t v_isZero_20_; 
v_zero_19_ = lean_unsigned_to_nat(0u);
v_isZero_20_ = lean_nat_dec_eq(v_x_16_, v_zero_19_);
if (v_isZero_20_ == 1)
{
lean_object* v___x_21_; lean_object* v___x_22_; 
lean_dec(v_h__2_18_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_apply_1(v_h__1_17_, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v_one_23_; lean_object* v_n_24_; lean_object* v___x_25_; 
lean_dec(v_h__1_17_);
v_one_23_ = lean_unsigned_to_nat(1u);
v_n_24_ = lean_nat_sub(v_x_16_, v_one_23_);
v___x_25_ = lean_apply_1(v_h__2_18_, v_n_24_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDist_match__1_splitter___boxed(lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDist_match__1_splitter(v_motive_26_, v_x_27_, v_h__1_28_, v_h__2_29_);
lean_dec(v_x_27_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDistFrom_match__1_splitter___redArg(lean_object* v_x_31_, lean_object* v_x_32_, lean_object* v_h__1_33_, lean_object* v_h__2_34_){
_start:
{
lean_object* v_zero_35_; uint8_t v_isZero_36_; 
v_zero_35_ = lean_unsigned_to_nat(0u);
v_isZero_36_ = lean_nat_dec_eq(v_x_32_, v_zero_35_);
if (v_isZero_36_ == 1)
{
lean_object* v___x_37_; 
lean_dec(v_h__2_34_);
v___x_37_ = lean_apply_1(v_h__1_33_, v_x_31_);
return v___x_37_;
}
else
{
lean_object* v_one_38_; lean_object* v_n_39_; lean_object* v___x_40_; 
lean_dec(v_h__1_33_);
v_one_38_ = lean_unsigned_to_nat(1u);
v_n_39_ = lean_nat_sub(v_x_32_, v_one_38_);
v___x_40_ = lean_apply_2(v_h__2_34_, v_x_31_, v_n_39_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDistFrom_match__1_splitter___redArg___boxed(lean_object* v_x_41_, lean_object* v_x_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDistFrom_match__1_splitter___redArg(v_x_41_, v_x_42_, v_h__1_43_, v_h__2_44_);
lean_dec(v_x_42_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDistFrom_match__1_splitter(lean_object* v_Q_46_, lean_object* v_X_47_, lean_object* v_n_48_, lean_object* v_motive_49_, lean_object* v_x_50_, lean_object* v_x_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_){
_start:
{
lean_object* v_zero_54_; uint8_t v_isZero_55_; 
v_zero_54_ = lean_unsigned_to_nat(0u);
v_isZero_55_ = lean_nat_dec_eq(v_x_51_, v_zero_54_);
if (v_isZero_55_ == 1)
{
lean_object* v___x_56_; 
lean_dec(v_h__2_53_);
v___x_56_ = lean_apply_1(v_h__1_52_, v_x_50_);
return v___x_56_;
}
else
{
lean_object* v_one_57_; lean_object* v_n_58_; lean_object* v___x_59_; 
lean_dec(v_h__1_52_);
v_one_57_ = lean_unsigned_to_nat(1u);
v_n_58_ = lean_nat_sub(v_x_51_, v_one_57_);
v___x_59_ = lean_apply_2(v_h__2_53_, v_x_50_, v_n_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDistFrom_match__1_splitter___boxed(lean_object* v_Q_60_, lean_object* v_X_61_, lean_object* v_n_62_, lean_object* v_motive_63_, lean_object* v_x_64_, lean_object* v_x_65_, lean_object* v_h__1_66_, lean_object* v_h__2_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_SSExactMajority___private_SSExactMajority_Probability_ExpectedTime_0__SSEM_Probability_hitFlagDistFrom_match__1_splitter(v_Q_60_, v_X_61_, v_n_62_, v_motive_63_, v_x_64_, v_x_65_, v_h__1_66_, v_h__2_67_);
lean_dec(v_x_65_);
lean_dec(v_n_62_);
return v_res_68_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Probability_RandomScheduler(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_Silent(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecificLimits_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Integral_Lebesgue_Markov(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_Instances_ENNReal_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Probability_ExpectedTime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Probability_RandomScheduler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_Silent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecificLimits_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Integral_Lebesgue_Markov(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_Instances_ENNReal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
