// Lean compiler output
// Module: SSExactMajority.Convergence.SwapPhase
// Imports: public import Init public meta import Init public import SSExactMajority.Convergence.Sets public import Mathlib.Data.Fintype.Prod
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
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqOpinion(uint8_t, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableMisorderedPair___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableMisorderedPair___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableMisorderedPair(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableMisorderedPair___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_misorderedSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_misorderedCount(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableMisorderedPair___redArg(lean_object* v_C_1_, lean_object* v_uv_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; lean_object* v___x_5_; lean_object* v_fst_6_; lean_object* v_snd_7_; uint8_t v___x_8_; uint8_t v___x_9_; uint8_t v___x_10_; 
v_fst_3_ = lean_ctor_get(v_uv_2_, 0);
lean_inc(v_fst_3_);
v_snd_4_ = lean_ctor_get(v_uv_2_, 1);
lean_inc(v_snd_4_);
lean_dec_ref(v_uv_2_);
lean_inc_ref(v_C_1_);
v___x_5_ = lean_apply_1(v_C_1_, v_fst_3_);
v_fst_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_fst_6_);
v_snd_7_ = lean_ctor_get(v___x_5_, 1);
lean_inc(v_snd_7_);
lean_dec_ref(v___x_5_);
v___x_8_ = 1;
v___x_9_ = lean_unbox(v_snd_7_);
lean_dec(v_snd_7_);
v___x_10_ = lp_SSExactMajority_SSEM_instDecidableEqOpinion(v___x_9_, v___x_8_);
if (v___x_10_ == 0)
{
lean_dec(v_fst_6_);
lean_dec(v_snd_4_);
lean_dec_ref(v_C_1_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; lean_object* v_fst_12_; lean_object* v_snd_13_; uint8_t v___x_14_; uint8_t v___x_15_; uint8_t v___x_16_; 
v___x_11_ = lean_apply_1(v_C_1_, v_snd_4_);
v_fst_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc(v_fst_12_);
v_snd_13_ = lean_ctor_get(v___x_11_, 1);
lean_inc(v_snd_13_);
lean_dec_ref(v___x_11_);
v___x_14_ = 0;
v___x_15_ = lean_unbox(v_snd_13_);
lean_dec(v_snd_13_);
v___x_16_ = lp_SSExactMajority_SSEM_instDecidableEqOpinion(v___x_15_, v___x_14_);
if (v___x_16_ == 0)
{
lean_dec(v_fst_12_);
lean_dec(v_fst_6_);
return v___x_16_;
}
else
{
lean_object* v_rank_17_; lean_object* v_rank_18_; uint8_t v___x_19_; 
v_rank_17_ = lean_ctor_get(v_fst_6_, 0);
lean_inc(v_rank_17_);
lean_dec(v_fst_6_);
v_rank_18_ = lean_ctor_get(v_fst_12_, 0);
lean_inc(v_rank_18_);
lean_dec(v_fst_12_);
v___x_19_ = lean_nat_dec_lt(v_rank_17_, v_rank_18_);
lean_dec(v_rank_18_);
lean_dec(v_rank_17_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableMisorderedPair___redArg___boxed(lean_object* v_C_20_, lean_object* v_uv_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = lp_SSExactMajority_SSEM_instDecidableMisorderedPair___redArg(v_C_20_, v_uv_21_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_instDecidableMisorderedPair(lean_object* v_n_24_, lean_object* v_C_25_, lean_object* v_uv_26_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = lp_SSExactMajority_SSEM_instDecidableMisorderedPair___redArg(v_C_25_, v_uv_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_instDecidableMisorderedPair___boxed(lean_object* v_n_28_, lean_object* v_C_29_, lean_object* v_uv_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = lp_SSExactMajority_SSEM_instDecidableMisorderedPair(v_n_28_, v_C_29_, v_uv_30_);
lean_dec(v_n_28_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__1___redArg(lean_object* v_C_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
if (lean_obj_tag(v_a_34_) == 0)
{
lean_object* v___x_36_; 
lean_dec_ref(v_C_33_);
v___x_36_ = l_List_reverse___redArg(v_a_35_);
return v___x_36_;
}
else
{
lean_object* v_head_37_; lean_object* v_tail_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_48_; 
v_head_37_ = lean_ctor_get(v_a_34_, 0);
v_tail_38_ = lean_ctor_get(v_a_34_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v_a_34_);
if (v_isSharedCheck_48_ == 0)
{
v___x_40_ = v_a_34_;
v_isShared_41_ = v_isSharedCheck_48_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_tail_38_);
lean_inc(v_head_37_);
lean_dec(v_a_34_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_48_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
uint8_t v___x_42_; 
lean_inc(v_head_37_);
lean_inc_ref(v_C_33_);
v___x_42_ = lp_SSExactMajority_SSEM_instDecidableMisorderedPair___redArg(v_C_33_, v_head_37_);
if (v___x_42_ == 0)
{
lean_del_object(v___x_40_);
lean_dec(v_head_37_);
v_a_34_ = v_tail_38_;
goto _start;
}
else
{
lean_object* v___x_45_; 
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 1, v_a_35_);
v___x_45_ = v___x_40_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_head_37_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_a_35_);
v___x_45_ = v_reuseFailAlloc_47_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
v_a_34_ = v_tail_38_;
v_a_35_ = v___x_45_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg(lean_object* v_n_49_, lean_object* v_C_50_, lean_object* v_s_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_box(0);
v___x_53_ = lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__1___redArg(v_C_50_, v_s_51_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg___boxed(lean_object* v_n_54_, lean_object* v_C_55_, lean_object* v_s_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg(v_n_54_, v_C_55_, v_s_56_);
lean_dec(v_n_54_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_misorderedSet(lean_object* v_n_58_, lean_object* v_C_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
lean_inc(v_n_58_);
v___x_60_ = l_List_finRange(v_n_58_);
lean_inc(v___x_60_);
v___x_61_ = lp_mathlib_Multiset_product___redArg(v___x_60_, v___x_60_);
v___x_62_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg(v_n_58_, v_C_59_, v___x_61_);
lean_dec(v_n_58_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0___redArg(lean_object* v_n_63_, lean_object* v_C_64_, lean_object* v_s_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg(v_n_63_, v_C_64_, v_s_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0___redArg___boxed(lean_object* v_n_67_, lean_object* v_C_68_, lean_object* v_s_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0___redArg(v_n_67_, v_C_68_, v_s_69_);
lean_dec(v_n_67_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0(lean_object* v_n_71_, lean_object* v_C_72_, lean_object* v_p_73_, lean_object* v_s_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg(v_n_71_, v_C_72_, v_s_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0___boxed(lean_object* v_n_76_, lean_object* v_C_77_, lean_object* v_p_78_, lean_object* v_s_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = lp_SSExactMajority_Finset_filter___at___00SSEM_misorderedSet_spec__0(v_n_76_, v_C_77_, v_p_78_, v_s_79_);
lean_dec(v_n_76_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0(lean_object* v_n_81_, lean_object* v_C_82_, lean_object* v_p_83_, lean_object* v_s_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___redArg(v_n_81_, v_C_82_, v_s_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0___boxed(lean_object* v_n_86_, lean_object* v_C_87_, lean_object* v_p_88_, lean_object* v_s_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0(v_n_86_, v_C_87_, v_p_88_, v_s_89_);
lean_dec(v_n_86_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__1(lean_object* v_n_91_, lean_object* v_C_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__1___redArg(v_C_92_, v_a_93_, v_a_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__1___boxed(lean_object* v_n_96_, lean_object* v_C_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_misorderedSet_spec__0_spec__0_spec__1(v_n_96_, v_C_97_, v_a_98_, v_a_99_);
lean_dec(v_n_96_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_misorderedCount(lean_object* v_n_101_, lean_object* v_C_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lp_SSExactMajority_SSEM_misorderedSet(v_n_101_, v_C_102_);
v___x_104_ = l_List_lengthTR___redArg(v___x_103_);
lean_dec(v___x_103_);
return v___x_104_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_Sets(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Prod(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_SwapPhase(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_Sets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
