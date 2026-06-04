// Lean compiler output
// Module: SSExactMajority.Convergence.NonMedianExistence
// Imports: public import Init public meta import Init public import SSExactMajority.Convergence.SwapStep
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_SSExactMajority_SSEM_ceilHalf(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_SSExactMajority_SSEM_misorderedSet(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_nonMedianMisorderedSet___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nonMedianMisorderedSet___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nonMedianMisorderedSet(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_nonMedianMisorderedSet___lam__0(lean_object* v_C_1_, lean_object* v_n_2_, lean_object* v_a_3_){
_start:
{
lean_object* v_fst_4_; lean_object* v_snd_5_; lean_object* v___x_6_; lean_object* v_fst_7_; lean_object* v_rank_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v_fst_4_ = lean_ctor_get(v_a_3_, 0);
lean_inc(v_fst_4_);
v_snd_5_ = lean_ctor_get(v_a_3_, 1);
lean_inc(v_snd_5_);
lean_dec_ref(v_a_3_);
lean_inc_ref(v_C_1_);
v___x_6_ = lean_apply_1(v_C_1_, v_fst_4_);
v_fst_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_fst_7_);
lean_dec_ref(v___x_6_);
v_rank_8_ = lean_ctor_get(v_fst_7_, 0);
lean_inc(v_rank_8_);
lean_dec(v_fst_7_);
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_nat_add(v_rank_8_, v___x_9_);
lean_dec(v_rank_8_);
v___x_11_ = lp_SSExactMajority_SSEM_ceilHalf(v_n_2_);
v___x_12_ = lean_nat_dec_eq(v___x_10_, v___x_11_);
lean_dec(v___x_10_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; lean_object* v_fst_14_; lean_object* v_rank_15_; lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_13_ = lean_apply_1(v_C_1_, v_snd_5_);
v_fst_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_fst_14_);
lean_dec_ref(v___x_13_);
v_rank_15_ = lean_ctor_get(v_fst_14_, 0);
lean_inc(v_rank_15_);
lean_dec(v_fst_14_);
v___x_16_ = lean_nat_add(v_rank_15_, v___x_9_);
lean_dec(v_rank_15_);
v___x_17_ = lean_nat_dec_eq(v___x_16_, v___x_11_);
lean_dec(v___x_11_);
lean_dec(v___x_16_);
if (v___x_17_ == 0)
{
uint8_t v___x_18_; 
v___x_18_ = 1;
return v___x_18_;
}
else
{
return v___x_12_;
}
}
else
{
uint8_t v___x_19_; 
lean_dec(v___x_11_);
lean_dec(v_snd_5_);
lean_dec_ref(v_C_1_);
v___x_19_ = 0;
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nonMedianMisorderedSet___lam__0___boxed(lean_object* v_C_20_, lean_object* v_n_21_, lean_object* v_a_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = lp_SSExactMajority_SSEM_nonMedianMisorderedSet___lam__0(v_C_20_, v_n_21_, v_a_22_);
lean_dec(v_n_21_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_nonMedianMisorderedSet(lean_object* v_n_25_, lean_object* v_C_26_){
_start:
{
lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
lean_inc(v_n_25_);
lean_inc_ref(v_C_26_);
v___f_27_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_nonMedianMisorderedSet___lam__0___boxed), 3, 2);
lean_closure_set(v___f_27_, 0, v_C_26_);
lean_closure_set(v___f_27_, 1, v_n_25_);
v___x_28_ = lp_SSExactMajority_SSEM_misorderedSet(v_n_25_, v_C_26_);
v___x_29_ = lp_mathlib_Multiset_filter___redArg(v___f_27_, v___x_28_);
return v___x_29_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_SwapStep(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_NonMedianExistence(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_SwapStep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
