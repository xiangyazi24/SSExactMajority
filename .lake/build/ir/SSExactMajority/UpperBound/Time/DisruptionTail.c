// Lean compiler output
// Module: SSExactMajority.UpperBound.Time.DisruptionTail
// Imports: public import Init public meta import Init public import SSExactMajority.Probability.RandomScheduler public import SSExactMajority.Protocol.RankDelta public import Mathlib.Data.Finset.Powerset public import Mathlib.Data.Set.PowersetCard public import Mathlib.Data.Nat.Choose.Bounds
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_selectedAt__decidable___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_selectedAt__decidable___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_selectedAt__decidable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_selectedAt__decidable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_selectionCount(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_selectionCount___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_selectionCount_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_selectionCount_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_selectionCount_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_selectionCount_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_prefixSelectedAt__decidable___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_prefixSelectedAt__decidable___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_prefixSelectedAt__decidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_prefixSelectedAt__decidable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_prefixSelectionCount(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_prefixSelectionCount___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_prefixSelectionCount_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_prefixSelectionCount_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_prefixSelectionCount_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_prefixSelectionCount_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_selectedAt__decidable___redArg(lean_object* v_00_u03b3_1_, lean_object* v_a_2_, lean_object* v_t_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_fst_5_; lean_object* v_snd_6_; uint8_t v___x_7_; 
v___x_4_ = lean_apply_1(v_00_u03b3_1_, v_t_3_);
v_fst_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_fst_5_);
v_snd_6_ = lean_ctor_get(v___x_4_, 1);
lean_inc(v_snd_6_);
lean_dec_ref(v___x_4_);
v___x_7_ = lean_nat_dec_eq(v_a_2_, v_fst_5_);
lean_dec(v_fst_5_);
if (v___x_7_ == 0)
{
uint8_t v___x_8_; 
v___x_8_ = lean_nat_dec_eq(v_a_2_, v_snd_6_);
lean_dec(v_snd_6_);
return v___x_8_;
}
else
{
lean_dec(v_snd_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_selectedAt__decidable___redArg___boxed(lean_object* v_00_u03b3_9_, lean_object* v_a_10_, lean_object* v_t_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = lp_SSExactMajority_SSEM_selectedAt__decidable___redArg(v_00_u03b3_9_, v_a_10_, v_t_11_);
lean_dec(v_a_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_selectedAt__decidable(lean_object* v_n_14_, lean_object* v_00_u03b3_15_, lean_object* v_a_16_, lean_object* v_t_17_){
_start:
{
uint8_t v___x_18_; 
v___x_18_ = lp_SSExactMajority_SSEM_selectedAt__decidable___redArg(v_00_u03b3_15_, v_a_16_, v_t_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_selectedAt__decidable___boxed(lean_object* v_n_19_, lean_object* v_00_u03b3_20_, lean_object* v_a_21_, lean_object* v_t_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = lp_SSExactMajority_SSEM_selectedAt__decidable(v_n_19_, v_00_u03b3_20_, v_a_21_, v_t_22_);
lean_dec(v_a_21_);
lean_dec(v_n_19_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0_spec__1___redArg(lean_object* v_00_u03b3_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
if (lean_obj_tag(v_a_27_) == 0)
{
lean_object* v___x_29_; 
lean_dec_ref(v_00_u03b3_25_);
v___x_29_ = l_List_reverse___redArg(v_a_28_);
return v___x_29_;
}
else
{
lean_object* v_head_30_; lean_object* v_tail_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_41_; 
v_head_30_ = lean_ctor_get(v_a_27_, 0);
v_tail_31_ = lean_ctor_get(v_a_27_, 1);
v_isSharedCheck_41_ = !lean_is_exclusive(v_a_27_);
if (v_isSharedCheck_41_ == 0)
{
v___x_33_ = v_a_27_;
v_isShared_34_ = v_isSharedCheck_41_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_tail_31_);
lean_inc(v_head_30_);
lean_dec(v_a_27_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_41_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
uint8_t v___x_35_; 
lean_inc(v_head_30_);
lean_inc_ref(v_00_u03b3_25_);
v___x_35_ = lp_SSExactMajority_SSEM_selectedAt__decidable___redArg(v_00_u03b3_25_, v_a_26_, v_head_30_);
if (v___x_35_ == 0)
{
lean_del_object(v___x_33_);
lean_dec(v_head_30_);
v_a_27_ = v_tail_31_;
goto _start;
}
else
{
lean_object* v___x_38_; 
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 1, v_a_28_);
v___x_38_ = v___x_33_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_head_30_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_a_28_);
v___x_38_ = v_reuseFailAlloc_40_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
v_a_27_ = v_tail_31_;
v_a_28_ = v___x_38_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_00_u03b3_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0_spec__1___redArg(v_00_u03b3_42_, v_a_43_, v_a_44_, v_a_45_);
lean_dec(v_a_43_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0___redArg(lean_object* v_n_47_, lean_object* v_00_u03b3_48_, lean_object* v_a_49_, lean_object* v_s_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_box(0);
v___x_52_ = lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0_spec__1___redArg(v_00_u03b3_48_, v_a_49_, v_s_50_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0___redArg___boxed(lean_object* v_n_53_, lean_object* v_00_u03b3_54_, lean_object* v_a_55_, lean_object* v_s_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0___redArg(v_n_53_, v_00_u03b3_54_, v_a_55_, v_s_56_);
lean_dec(v_a_55_);
lean_dec(v_n_53_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_selectionCount(lean_object* v_n_58_, lean_object* v_00_u03b3_59_, lean_object* v_a_60_, lean_object* v_K_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = l_List_range(v_K_61_);
v___x_63_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0___redArg(v_n_58_, v_00_u03b3_59_, v_a_60_, v___x_62_);
v___x_64_ = l_List_lengthTR___redArg(v___x_63_);
lean_dec(v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_selectionCount___boxed(lean_object* v_n_65_, lean_object* v_00_u03b3_66_, lean_object* v_a_67_, lean_object* v_K_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = lp_SSExactMajority_SSEM_selectionCount(v_n_65_, v_00_u03b3_66_, v_a_67_, v_K_68_);
lean_dec(v_a_67_);
lean_dec(v_n_65_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_selectionCount_spec__0___redArg(lean_object* v_n_70_, lean_object* v_00_u03b3_71_, lean_object* v_a_72_, lean_object* v_s_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0___redArg(v_n_70_, v_00_u03b3_71_, v_a_72_, v_s_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_selectionCount_spec__0___redArg___boxed(lean_object* v_n_75_, lean_object* v_00_u03b3_76_, lean_object* v_a_77_, lean_object* v_s_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lp_SSExactMajority_Finset_filter___at___00SSEM_selectionCount_spec__0___redArg(v_n_75_, v_00_u03b3_76_, v_a_77_, v_s_78_);
lean_dec(v_a_77_);
lean_dec(v_n_75_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_selectionCount_spec__0(lean_object* v_n_80_, lean_object* v_00_u03b3_81_, lean_object* v_a_82_, lean_object* v_p_83_, lean_object* v_s_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0___redArg(v_n_80_, v_00_u03b3_81_, v_a_82_, v_s_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_selectionCount_spec__0___boxed(lean_object* v_n_86_, lean_object* v_00_u03b3_87_, lean_object* v_a_88_, lean_object* v_p_89_, lean_object* v_s_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = lp_SSExactMajority_Finset_filter___at___00SSEM_selectionCount_spec__0(v_n_86_, v_00_u03b3_87_, v_a_88_, v_p_89_, v_s_90_);
lean_dec(v_a_88_);
lean_dec(v_n_86_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0(lean_object* v_n_92_, lean_object* v_00_u03b3_93_, lean_object* v_a_94_, lean_object* v_p_95_, lean_object* v_s_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0___redArg(v_n_92_, v_00_u03b3_93_, v_a_94_, v_s_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0___boxed(lean_object* v_n_98_, lean_object* v_00_u03b3_99_, lean_object* v_a_100_, lean_object* v_p_101_, lean_object* v_s_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0(v_n_98_, v_00_u03b3_99_, v_a_100_, v_p_101_, v_s_102_);
lean_dec(v_a_100_);
lean_dec(v_n_98_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0_spec__1(lean_object* v_n_104_, lean_object* v_00_u03b3_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0_spec__1___redArg(v_00_u03b3_105_, v_a_106_, v_a_107_, v_a_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0_spec__1___boxed(lean_object* v_n_110_, lean_object* v_00_u03b3_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_selectionCount_spec__0_spec__0_spec__1(v_n_110_, v_00_u03b3_111_, v_a_112_, v_a_113_, v_a_114_);
lean_dec(v_a_112_);
lean_dec(v_n_110_);
return v_res_115_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_prefixSelectedAt__decidable___redArg(lean_object* v_00_u03c3_116_, lean_object* v_a_117_, lean_object* v_t_118_){
_start:
{
lean_object* v___x_119_; lean_object* v_fst_120_; lean_object* v_snd_121_; uint8_t v___x_122_; 
v___x_119_ = lean_apply_1(v_00_u03c3_116_, v_t_118_);
v_fst_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_fst_120_);
v_snd_121_ = lean_ctor_get(v___x_119_, 1);
lean_inc(v_snd_121_);
lean_dec_ref(v___x_119_);
v___x_122_ = lean_nat_dec_eq(v_a_117_, v_fst_120_);
lean_dec(v_fst_120_);
if (v___x_122_ == 0)
{
uint8_t v___x_123_; 
v___x_123_ = lean_nat_dec_eq(v_a_117_, v_snd_121_);
lean_dec(v_snd_121_);
return v___x_123_;
}
else
{
lean_dec(v_snd_121_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_prefixSelectedAt__decidable___redArg___boxed(lean_object* v_00_u03c3_124_, lean_object* v_a_125_, lean_object* v_t_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = lp_SSExactMajority_SSEM_prefixSelectedAt__decidable___redArg(v_00_u03c3_124_, v_a_125_, v_t_126_);
lean_dec(v_a_125_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_prefixSelectedAt__decidable(lean_object* v_n_129_, lean_object* v_K_130_, lean_object* v_00_u03c3_131_, lean_object* v_a_132_, lean_object* v_t_133_){
_start:
{
uint8_t v___x_134_; 
v___x_134_ = lp_SSExactMajority_SSEM_prefixSelectedAt__decidable___redArg(v_00_u03c3_131_, v_a_132_, v_t_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_prefixSelectedAt__decidable___boxed(lean_object* v_n_135_, lean_object* v_K_136_, lean_object* v_00_u03c3_137_, lean_object* v_a_138_, lean_object* v_t_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = lp_SSExactMajority_SSEM_prefixSelectedAt__decidable(v_n_135_, v_K_136_, v_00_u03c3_137_, v_a_138_, v_t_139_);
lean_dec(v_a_138_);
lean_dec(v_K_136_);
lean_dec(v_n_135_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0_spec__1___redArg(lean_object* v_00_u03c3_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
if (lean_obj_tag(v_a_144_) == 0)
{
lean_object* v___x_146_; 
lean_dec_ref(v_00_u03c3_142_);
v___x_146_ = l_List_reverse___redArg(v_a_145_);
return v___x_146_;
}
else
{
lean_object* v_head_147_; lean_object* v_tail_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_158_; 
v_head_147_ = lean_ctor_get(v_a_144_, 0);
v_tail_148_ = lean_ctor_get(v_a_144_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_a_144_);
if (v_isSharedCheck_158_ == 0)
{
v___x_150_ = v_a_144_;
v_isShared_151_ = v_isSharedCheck_158_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_tail_148_);
lean_inc(v_head_147_);
lean_dec(v_a_144_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_158_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
uint8_t v___x_152_; 
lean_inc(v_head_147_);
lean_inc_ref(v_00_u03c3_142_);
v___x_152_ = lp_SSExactMajority_SSEM_prefixSelectedAt__decidable___redArg(v_00_u03c3_142_, v_a_143_, v_head_147_);
if (v___x_152_ == 0)
{
lean_del_object(v___x_150_);
lean_dec(v_head_147_);
v_a_144_ = v_tail_148_;
goto _start;
}
else
{
lean_object* v___x_155_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v_a_145_);
v___x_155_ = v___x_150_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_head_147_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_a_145_);
v___x_155_ = v_reuseFailAlloc_157_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
v_a_144_ = v_tail_148_;
v_a_145_ = v___x_155_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_00_u03c3_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0_spec__1___redArg(v_00_u03c3_159_, v_a_160_, v_a_161_, v_a_162_);
lean_dec(v_a_160_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0___redArg(lean_object* v_n_164_, lean_object* v_K_165_, lean_object* v_00_u03c3_166_, lean_object* v_a_167_, lean_object* v_s_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_box(0);
v___x_170_ = lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0_spec__1___redArg(v_00_u03c3_166_, v_a_167_, v_s_168_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0___redArg___boxed(lean_object* v_n_171_, lean_object* v_K_172_, lean_object* v_00_u03c3_173_, lean_object* v_a_174_, lean_object* v_s_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0___redArg(v_n_171_, v_K_172_, v_00_u03c3_173_, v_a_174_, v_s_175_);
lean_dec(v_a_174_);
lean_dec(v_K_172_);
lean_dec(v_n_171_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_prefixSelectionCount(lean_object* v_n_177_, lean_object* v_K_178_, lean_object* v_00_u03c3_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_inc(v_K_178_);
v___x_181_ = l_List_finRange(v_K_178_);
v___x_182_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0___redArg(v_n_177_, v_K_178_, v_00_u03c3_179_, v_a_180_, v___x_181_);
lean_dec(v_K_178_);
v___x_183_ = l_List_lengthTR___redArg(v___x_182_);
lean_dec(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_prefixSelectionCount___boxed(lean_object* v_n_184_, lean_object* v_K_185_, lean_object* v_00_u03c3_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = lp_SSExactMajority_SSEM_prefixSelectionCount(v_n_184_, v_K_185_, v_00_u03c3_186_, v_a_187_);
lean_dec(v_a_187_);
lean_dec(v_n_184_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_prefixSelectionCount_spec__0___redArg(lean_object* v_n_189_, lean_object* v_K_190_, lean_object* v_00_u03c3_191_, lean_object* v_a_192_, lean_object* v_s_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0___redArg(v_n_189_, v_K_190_, v_00_u03c3_191_, v_a_192_, v_s_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_prefixSelectionCount_spec__0___redArg___boxed(lean_object* v_n_195_, lean_object* v_K_196_, lean_object* v_00_u03c3_197_, lean_object* v_a_198_, lean_object* v_s_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = lp_SSExactMajority_Finset_filter___at___00SSEM_prefixSelectionCount_spec__0___redArg(v_n_195_, v_K_196_, v_00_u03c3_197_, v_a_198_, v_s_199_);
lean_dec(v_a_198_);
lean_dec(v_K_196_);
lean_dec(v_n_195_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_prefixSelectionCount_spec__0(lean_object* v_n_201_, lean_object* v_K_202_, lean_object* v_00_u03c3_203_, lean_object* v_a_204_, lean_object* v_p_205_, lean_object* v_s_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0___redArg(v_n_201_, v_K_202_, v_00_u03c3_203_, v_a_204_, v_s_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Finset_filter___at___00SSEM_prefixSelectionCount_spec__0___boxed(lean_object* v_n_208_, lean_object* v_K_209_, lean_object* v_00_u03c3_210_, lean_object* v_a_211_, lean_object* v_p_212_, lean_object* v_s_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = lp_SSExactMajority_Finset_filter___at___00SSEM_prefixSelectionCount_spec__0(v_n_208_, v_K_209_, v_00_u03c3_210_, v_a_211_, v_p_212_, v_s_213_);
lean_dec(v_a_211_);
lean_dec(v_K_209_);
lean_dec(v_n_208_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0(lean_object* v_n_215_, lean_object* v_K_216_, lean_object* v_00_u03c3_217_, lean_object* v_a_218_, lean_object* v_p_219_, lean_object* v_s_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0___redArg(v_n_215_, v_K_216_, v_00_u03c3_217_, v_a_218_, v_s_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0___boxed(lean_object* v_n_222_, lean_object* v_K_223_, lean_object* v_00_u03c3_224_, lean_object* v_a_225_, lean_object* v_p_226_, lean_object* v_s_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = lp_SSExactMajority_Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0(v_n_222_, v_K_223_, v_00_u03c3_224_, v_a_225_, v_p_226_, v_s_227_);
lean_dec(v_a_225_);
lean_dec(v_K_223_);
lean_dec(v_n_222_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0_spec__1(lean_object* v_n_229_, lean_object* v_K_230_, lean_object* v_00_u03c3_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0_spec__1___redArg(v_00_u03c3_231_, v_a_232_, v_a_233_, v_a_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0_spec__1___boxed(lean_object* v_n_236_, lean_object* v_K_237_, lean_object* v_00_u03c3_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = lp_SSExactMajority_List_filterTR_loop___at___00Multiset_filter___at___00Finset_filter___at___00SSEM_prefixSelectionCount_spec__0_spec__0_spec__1(v_n_236_, v_K_237_, v_00_u03c3_238_, v_a_239_, v_a_240_, v_a_241_);
lean_dec(v_a_239_);
lean_dec(v_K_237_);
lean_dec(v_n_236_);
return v_res_242_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Probability_RandomScheduler(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_RankDelta(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Powerset(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Set_PowersetCard(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Nat_Choose_Bounds(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_DisruptionTail(uint8_t builtin) {
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
res = initialize_SSExactMajority_SSExactMajority_Protocol_RankDelta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Powerset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Set_PowersetCard(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Nat_Choose_Bounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
