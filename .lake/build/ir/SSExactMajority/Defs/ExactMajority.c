// Lean compiler output
// Module: SSExactMajority.Defs.ExactMajority
// Imports: public import Init public meta import Init public import SSExactMajority.Defs.Execution
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_majorityOpinion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_majorityOpinion___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_majorityOpinion(lean_object* v_countA_1_, lean_object* v_countB_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_lt(v_countB_2_, v_countA_1_);
if (v___x_3_ == 0)
{
uint8_t v___x_4_; 
v___x_4_ = lean_nat_dec_lt(v_countA_1_, v_countB_2_);
if (v___x_4_ == 0)
{
uint8_t v___x_5_; 
v___x_5_ = 2;
return v___x_5_;
}
else
{
uint8_t v___x_6_; 
v___x_6_ = 1;
return v___x_6_;
}
}
else
{
uint8_t v___x_7_; 
v___x_7_ = 0;
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_majorityOpinion___boxed(lean_object* v_countA_8_, lean_object* v_countB_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = lp_SSExactMajority_SSEM_majorityOpinion(v_countA_8_, v_countB_9_);
lean_dec(v_countB_9_);
lean_dec(v_countA_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Execution(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Defs_ExactMajority(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
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
