// Lean compiler output
// Module: SSExactMajority.Convergence.DecisionReach
// Imports: public import Init public meta import Init public import SSExactMajority.Convergence.PotentialReach public import SSExactMajority.Convergence.SwapPhase public import SSExactMajority.Convergence.RankPreservation
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
uint8_t lp_SSExactMajority_SSEM_majorityAnswer(lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqAnswer(uint8_t, uint8_t);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_wrongAnswerCount___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongAnswerCount___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongAnswerCount(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_wrongAnswerCount___lam__0(lean_object* v_C_1_, lean_object* v_n_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_fst_5_; uint8_t v_answer_6_; uint8_t v___x_7_; uint8_t v___x_8_; 
lean_inc_ref(v_C_1_);
v___x_4_ = lean_apply_1(v_C_1_, v_a_3_);
v_fst_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_fst_5_);
lean_dec_ref(v___x_4_);
v_answer_6_ = lean_ctor_get_uint8(v_fst_5_, sizeof(void*)*6 + 2);
lean_dec(v_fst_5_);
v___x_7_ = lp_SSExactMajority_SSEM_majorityAnswer(v_n_2_, v_C_1_);
v___x_8_ = lp_SSExactMajority_SSEM_instDecidableEqAnswer(v_answer_6_, v___x_7_);
if (v___x_8_ == 0)
{
uint8_t v___x_9_; 
v___x_9_ = 1;
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongAnswerCount___lam__0___boxed(lean_object* v_C_11_, lean_object* v_n_12_, lean_object* v_a_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = lp_SSExactMajority_SSEM_wrongAnswerCount___lam__0(v_C_11_, v_n_12_, v_a_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongAnswerCount(lean_object* v_n_16_, lean_object* v_C_17_){
_start:
{
lean_object* v___f_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
lean_inc(v_n_16_);
v___f_18_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_wrongAnswerCount___lam__0___boxed), 3, 2);
lean_closure_set(v___f_18_, 0, v_C_17_);
lean_closure_set(v___f_18_, 1, v_n_16_);
v___x_19_ = l_List_finRange(v_n_16_);
v___x_20_ = lp_mathlib_Multiset_filter___redArg(v___f_18_, v___x_19_);
v___x_21_ = l_List_lengthTR___redArg(v___x_20_);
lean_dec(v___x_20_);
return v___x_21_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_PotentialReach(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_SwapPhase(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_RankPreservation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_DecisionReach(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_PotentialReach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_SwapPhase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_RankPreservation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
