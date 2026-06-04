// Lean compiler output
// Module: SSExactMajority.Convergence.Schedule
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_concatScheduler___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_concatScheduler___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_concatScheduler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_concatScheduler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_concatScheduler___redArg(lean_object* v_00_u03b3_u2081_1_, lean_object* v_k_2_, lean_object* v_00_u03b3_u2082_3_, lean_object* v_t_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_nat_dec_lt(v_t_4_, v_k_2_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec_ref(v_00_u03b3_u2081_1_);
v___x_6_ = lean_nat_sub(v_t_4_, v_k_2_);
lean_dec(v_t_4_);
v___x_7_ = lean_apply_1(v_00_u03b3_u2082_3_, v___x_6_);
return v___x_7_;
}
else
{
lean_object* v___x_8_; 
lean_dec_ref(v_00_u03b3_u2082_3_);
v___x_8_ = lean_apply_1(v_00_u03b3_u2081_1_, v_t_4_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_concatScheduler___redArg___boxed(lean_object* v_00_u03b3_u2081_9_, lean_object* v_k_10_, lean_object* v_00_u03b3_u2082_11_, lean_object* v_t_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_SSExactMajority_SSEM_concatScheduler___redArg(v_00_u03b3_u2081_9_, v_k_10_, v_00_u03b3_u2082_11_, v_t_12_);
lean_dec(v_k_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_concatScheduler(lean_object* v_n_14_, lean_object* v_00_u03b3_u2081_15_, lean_object* v_k_16_, lean_object* v_00_u03b3_u2082_17_, lean_object* v_t_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_SSExactMajority_SSEM_concatScheduler___redArg(v_00_u03b3_u2081_15_, v_k_16_, v_00_u03b3_u2082_17_, v_t_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_concatScheduler___boxed(lean_object* v_n_20_, lean_object* v_00_u03b3_u2081_21_, lean_object* v_k_22_, lean_object* v_00_u03b3_u2082_23_, lean_object* v_t_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_SSExactMajority_SSEM_concatScheduler(v_n_20_, v_00_u03b3_u2081_21_, v_k_22_, v_00_u03b3_u2082_23_, v_t_24_);
lean_dec(v_k_22_);
lean_dec(v_n_20_);
return v_res_25_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Execution(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_Schedule(uint8_t builtin) {
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
