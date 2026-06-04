// Lean compiler output
// Module: SSExactMajority.UpperBound.Time.EpidemicBound
// Imports: public import Init public meta import Init public import SSExactMajority.Convergence.BurmanConvergenceFinal public import SSExactMajority.Probability.ExpectedTime
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
uint8_t lp_SSExactMajority_SSEM_instDecidableEqAnswer(uint8_t, uint8_t);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndunion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_phiAgents___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phiAgents___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phiAgents(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_nonPhiAgents___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nonPhiAgents___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nonPhiAgents(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_phiNonPhiPairs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phiNonPhiPairs___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phiNonPhiPairs(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_phiAgents___lam__0(lean_object* v_C_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; lean_object* v_fst_4_; uint8_t v_answer_5_; uint8_t v___x_6_; uint8_t v___x_7_; 
v___x_3_ = lean_apply_1(v_C_1_, v_a_2_);
v_fst_4_ = lean_ctor_get(v___x_3_, 0);
lean_inc(v_fst_4_);
lean_dec_ref(v___x_3_);
v_answer_5_ = lean_ctor_get_uint8(v_fst_4_, sizeof(void*)*6 + 2);
lean_dec(v_fst_4_);
v___x_6_ = 0;
v___x_7_ = lp_SSExactMajority_SSEM_instDecidableEqAnswer(v_answer_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phiAgents___lam__0___boxed(lean_object* v_C_8_, lean_object* v_a_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = lp_SSExactMajority_SSEM_phiAgents___lam__0(v_C_8_, v_a_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phiAgents(lean_object* v_n_12_, lean_object* v_C_13_){
_start:
{
lean_object* v___f_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___f_14_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_phiAgents___lam__0___boxed), 2, 1);
lean_closure_set(v___f_14_, 0, v_C_13_);
v___x_15_ = l_List_finRange(v_n_12_);
v___x_16_ = lp_mathlib_Multiset_filter___redArg(v___f_14_, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_nonPhiAgents___lam__0(lean_object* v_C_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___x_19_; lean_object* v_fst_20_; uint8_t v_answer_21_; uint8_t v___x_22_; uint8_t v___x_23_; 
v___x_19_ = lean_apply_1(v_C_17_, v_a_18_);
v_fst_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_fst_20_);
lean_dec_ref(v___x_19_);
v_answer_21_ = lean_ctor_get_uint8(v_fst_20_, sizeof(void*)*6 + 2);
lean_dec(v_fst_20_);
v___x_22_ = 0;
v___x_23_ = lp_SSExactMajority_SSEM_instDecidableEqAnswer(v_answer_21_, v___x_22_);
if (v___x_23_ == 0)
{
uint8_t v___x_24_; 
v___x_24_ = 1;
return v___x_24_;
}
else
{
uint8_t v___x_25_; 
v___x_25_ = 0;
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nonPhiAgents___lam__0___boxed(lean_object* v_C_26_, lean_object* v_a_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = lp_SSExactMajority_SSEM_nonPhiAgents___lam__0(v_C_26_, v_a_27_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nonPhiAgents(lean_object* v_n_30_, lean_object* v_C_31_){
_start:
{
lean_object* v___f_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___f_32_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_nonPhiAgents___lam__0___boxed), 2, 1);
lean_closure_set(v___f_32_, 0, v_C_31_);
v___x_33_ = l_List_finRange(v_n_30_);
v___x_34_ = lp_mathlib_Multiset_filter___redArg(v___f_32_, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_phiNonPhiPairs___lam__0(lean_object* v_n_35_, lean_object* v_a_36_, lean_object* v_b_37_){
_start:
{
lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_38_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_38_, 0, v_n_35_);
lean_inc_ref(v___x_38_);
v___x_39_ = l_instDecidableEqProd___redArg(v___x_38_, v___x_38_, v_a_36_, v_b_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phiNonPhiPairs___lam__0___boxed(lean_object* v_n_40_, lean_object* v_a_41_, lean_object* v_b_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = lp_SSExactMajority_SSEM_phiNonPhiPairs___lam__0(v_n_40_, v_a_41_, v_b_42_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_phiNonPhiPairs(lean_object* v_n_45_, lean_object* v_C_46_){
_start:
{
lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
lean_inc_n(v_n_45_, 2);
v___f_47_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_phiNonPhiPairs___lam__0___boxed), 3, 1);
lean_closure_set(v___f_47_, 0, v_n_45_);
lean_inc_ref(v_C_46_);
v___x_48_ = lp_SSExactMajority_SSEM_phiAgents(v_n_45_, v_C_46_);
v___x_49_ = lp_SSExactMajority_SSEM_nonPhiAgents(v_n_45_, v_C_46_);
lean_inc(v___x_49_);
lean_inc(v___x_48_);
v___x_50_ = lp_mathlib_Multiset_product___redArg(v___x_48_, v___x_49_);
v___x_51_ = lp_mathlib_Multiset_product___redArg(v___x_49_, v___x_48_);
v___x_52_ = lp_mathlib_Multiset_ndunion___redArg(v___f_47_, v___x_50_, v___x_51_);
return v___x_52_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_BurmanConvergenceFinal(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Probability_ExpectedTime(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_EpidemicBound(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
