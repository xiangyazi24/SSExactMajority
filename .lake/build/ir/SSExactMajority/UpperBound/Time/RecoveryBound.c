// Lean compiler output
// Module: SSExactMajority.UpperBound.Time.RecoveryBound
// Imports: public import Init public meta import Init public import SSExactMajority.Convergence.BurmanConvergenceFinal public import SSExactMajority.Probability.ExpectedTime public import SSExactMajority.UpperBound.Time.RankingBound public import SSExactMajority.UpperBound.Time.RecoveryBridge
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
lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_SSExactMajority_SSEM_protocolPEM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocolCoupled_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocolCoupled_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocolCoupled_x27___redArg(lean_object* v_n_1_, lean_object* v_Rmax_2_, lean_object* v_Emax_3_, lean_object* v_Dmax_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
lean_inc_n(v_Rmax_2_, 2);
lean_inc(v_n_1_);
v___x_5_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed), 6, 5);
lean_closure_set(v___x_5_, 0, v_n_1_);
lean_closure_set(v___x_5_, 1, v_Rmax_2_);
lean_closure_set(v___x_5_, 2, v_Emax_3_);
lean_closure_set(v___x_5_, 3, v_Dmax_4_);
lean_closure_set(v___x_5_, 4, lean_box(0));
v___x_6_ = lp_SSExactMajority_SSEM_protocolPEM(v_n_1_, v_Rmax_2_, v_Rmax_2_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocolCoupled_x27(lean_object* v_n_7_, lean_object* v_Rmax_8_, lean_object* v_Emax_9_, lean_object* v_Dmax_10_, lean_object* v_hn_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
lean_inc_n(v_Rmax_8_, 2);
lean_inc(v_n_7_);
v___x_12_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed), 6, 5);
lean_closure_set(v___x_12_, 0, v_n_7_);
lean_closure_set(v___x_12_, 1, v_Rmax_8_);
lean_closure_set(v___x_12_, 2, v_Emax_9_);
lean_closure_set(v___x_12_, 3, v_Dmax_10_);
lean_closure_set(v___x_12_, 4, lean_box(0));
v___x_13_ = lp_SSExactMajority_SSEM_protocolPEM(v_n_7_, v_Rmax_8_, v_Rmax_8_, v___x_12_);
return v___x_13_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_BurmanConvergenceFinal(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Probability_ExpectedTime(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_RankingBound(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_RecoveryBridge(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_RecoveryBound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_BurmanConvergenceFinal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Probability_ExpectedTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_UpperBound_Time_RankingBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_UpperBound_Time_RecoveryBridge(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
