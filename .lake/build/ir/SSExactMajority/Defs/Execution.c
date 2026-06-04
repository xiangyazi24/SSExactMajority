// Lean compiler output
// Module: SSExactMajority.Defs.Execution
// Imports: public import Init public meta import Init public import SSExactMajority.Defs.Config public import Mathlib.Data.Finset.Card
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
lean_object* lp_SSExactMajority_SSEM_Config_step___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_execution___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_execution___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_execution(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_execution___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_execution___redArg___boxed(lean_object* v_P_1_, lean_object* v_C_u2080_2_, lean_object* v_00_u03b3_3_, lean_object* v_x_4_, lean_object* v_a_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_SSExactMajority_SSEM_execution___redArg(v_P_1_, v_C_u2080_2_, v_00_u03b3_3_, v_x_4_, v_a_5_);
lean_dec(v_x_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_execution___redArg(lean_object* v_P_7_, lean_object* v_C_u2080_8_, lean_object* v_00_u03b3_9_, lean_object* v_x_10_, lean_object* v_a_11_){
_start:
{
lean_object* v_zero_12_; uint8_t v_isZero_13_; 
v_zero_12_ = lean_unsigned_to_nat(0u);
v_isZero_13_ = lean_nat_dec_eq(v_x_10_, v_zero_12_);
if (v_isZero_13_ == 1)
{
lean_object* v___x_14_; 
lean_dec_ref(v_00_u03b3_9_);
lean_dec_ref(v_P_7_);
v___x_14_ = lean_apply_1(v_C_u2080_8_, v_a_11_);
return v___x_14_;
}
else
{
lean_object* v_one_15_; lean_object* v_n_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v_fst_19_; lean_object* v_snd_20_; lean_object* v___x_21_; 
v_one_15_ = lean_unsigned_to_nat(1u);
v_n_16_ = lean_nat_sub(v_x_10_, v_one_15_);
lean_inc(v_n_16_);
lean_inc_ref(v_00_u03b3_9_);
lean_inc_ref(v_P_7_);
v___x_17_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_execution___redArg___boxed), 5, 4);
lean_closure_set(v___x_17_, 0, v_P_7_);
lean_closure_set(v___x_17_, 1, v_C_u2080_8_);
lean_closure_set(v___x_17_, 2, v_00_u03b3_9_);
lean_closure_set(v___x_17_, 3, v_n_16_);
v___x_18_ = lean_apply_1(v_00_u03b3_9_, v_n_16_);
v_fst_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_fst_19_);
v_snd_20_ = lean_ctor_get(v___x_18_, 1);
lean_inc(v_snd_20_);
lean_dec_ref(v___x_18_);
v___x_21_ = lp_SSExactMajority_SSEM_Config_step___redArg(v_P_7_, v___x_17_, v_fst_19_, v_snd_20_, v_a_11_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_execution(lean_object* v_Q_22_, lean_object* v_X_23_, lean_object* v_Y_24_, lean_object* v_n_25_, lean_object* v_P_26_, lean_object* v_C_u2080_27_, lean_object* v_00_u03b3_28_, lean_object* v_x_29_, lean_object* v_a_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_SSExactMajority_SSEM_execution___redArg(v_P_26_, v_C_u2080_27_, v_00_u03b3_28_, v_x_29_, v_a_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_execution___boxed(lean_object* v_Q_32_, lean_object* v_X_33_, lean_object* v_Y_34_, lean_object* v_n_35_, lean_object* v_P_36_, lean_object* v_C_u2080_37_, lean_object* v_00_u03b3_38_, lean_object* v_x_39_, lean_object* v_a_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_SSExactMajority_SSEM_execution(v_Q_32_, v_X_33_, v_Y_34_, v_n_35_, v_P_36_, v_C_u2080_37_, v_00_u03b3_38_, v_x_39_, v_a_40_);
lean_dec(v_x_39_);
lean_dec(v_n_35_);
return v_res_41_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Config(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Card(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Execution(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Defs_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Card(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
