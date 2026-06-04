// Lean compiler output
// Module: SSExactMajority.UpperBound.Time.DecisionTiming
// Imports: public import Init public meta import Init public import SSExactMajority.UpperBound.Time
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_decisionWindow(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_decisionWindow___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_kanayaDecisionWindow(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_kanayaDecisionWindow___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_decisionWindow(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_2_ = lean_unsigned_to_nat(2u);
v___x_3_ = lean_nat_mul(v___x_2_, v_n_1_);
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_sub(v_n_1_, v___x_4_);
v___x_6_ = lean_nat_mul(v___x_3_, v___x_5_);
lean_dec(v___x_5_);
lean_dec(v___x_3_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_decisionWindow___boxed(lean_object* v_n_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_SSExactMajority_SSEM_decisionWindow(v_n_7_);
lean_dec(v_n_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_kanayaDecisionWindow(lean_object* v_n_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_10_ = lean_unsigned_to_nat(4u);
v___x_11_ = lean_nat_mul(v___x_10_, v_n_9_);
v___x_12_ = lean_nat_mul(v___x_11_, v_n_9_);
lean_dec(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_kanayaDecisionWindow___boxed(lean_object* v_n_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_SSExactMajority_SSEM_kanayaDecisionWindow(v_n_13_);
lean_dec(v_n_13_);
return v_res_14_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_DecisionTiming(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_UpperBound_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
