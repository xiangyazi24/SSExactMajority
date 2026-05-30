// Lean compiler output
// Module: SSExactMajority.UpperBound.Time
// Imports: public import Init public meta import Init public import SSExactMajority.Convergence.BurmanConvergenceFinal public import SSExactMajority.Probability.ExpectedTime public import Mathlib.Analysis.PSeries
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
uint8_t lp_SSExactMajority_SSEM_instDecidableEqOpinion(uint8_t, uint8_t);
lean_object* lp_SSExactMajority_SSEM_nAOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_SSExactMajority_SSEM_protocolPEM(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqRole(uint8_t, uint8_t);
lean_object* lp_SSExactMajority_SSEM_nonResettingCount(lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_majorityAnswer(lean_object*, lean_object*);
uint8_t lp_SSExactMajority_SSEM_instDecidableEqAnswer(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocol___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocolCoupled___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocolCoupled(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ConcretePEM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ConcretePEM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_wrongLowBSet___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongLowBSet___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongLowBSet(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_wrongHighASet___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongHighASet___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongHighASet(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_lowRankSet___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowRankSet___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowRankSet(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_lowASet___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowASet___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowASet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongLowBCount(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongHighACount(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_richResetSeedSet___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_richResetSeedSet___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_richResetSeedSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_richResetSeedCount(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_UpperBound_Time_0__SSEM_propagateReset_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_UpperBound_Time_0__SSEM_propagateReset_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_UpperBound_Time_0__SSEM_propagateReset_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocol___redArg(lean_object* v_n_1_, lean_object* v_trank_2_, lean_object* v_Rmax_3_, lean_object* v_Emax_4_, lean_object* v_Dmax_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_inc(v_Rmax_3_);
lean_inc(v_n_1_);
v___x_6_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed), 6, 5);
lean_closure_set(v___x_6_, 0, v_n_1_);
lean_closure_set(v___x_6_, 1, v_Rmax_3_);
lean_closure_set(v___x_6_, 2, v_Emax_4_);
lean_closure_set(v___x_6_, 3, v_Dmax_5_);
lean_closure_set(v___x_6_, 4, lean_box(0));
v___x_7_ = lp_SSExactMajority_SSEM_protocolPEM(v_n_1_, v_trank_2_, v_Rmax_3_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocol(lean_object* v_n_8_, lean_object* v_trank_9_, lean_object* v_Rmax_10_, lean_object* v_Emax_11_, lean_object* v_Dmax_12_, lean_object* v_hn_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_inc(v_Rmax_10_);
lean_inc(v_n_8_);
v___x_14_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed), 6, 5);
lean_closure_set(v___x_14_, 0, v_n_8_);
lean_closure_set(v___x_14_, 1, v_Rmax_10_);
lean_closure_set(v___x_14_, 2, v_Emax_11_);
lean_closure_set(v___x_14_, 3, v_Dmax_12_);
lean_closure_set(v___x_14_, 4, lean_box(0));
v___x_15_ = lp_SSExactMajority_SSEM_protocolPEM(v_n_8_, v_trank_9_, v_Rmax_10_, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocolCoupled___redArg(lean_object* v_n_16_, lean_object* v_Rmax_17_, lean_object* v_Emax_18_, lean_object* v_Dmax_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
lean_inc_n(v_Rmax_17_, 2);
lean_inc(v_n_16_);
v___x_20_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed), 6, 5);
lean_closure_set(v___x_20_, 0, v_n_16_);
lean_closure_set(v___x_20_, 1, v_Rmax_17_);
lean_closure_set(v___x_20_, 2, v_Emax_18_);
lean_closure_set(v___x_20_, 3, v_Dmax_19_);
lean_closure_set(v___x_20_, 4, lean_box(0));
v___x_21_ = lp_SSExactMajority_SSEM_protocolPEM(v_n_16_, v_Rmax_17_, v_Rmax_17_, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_PEMProtocolCoupled(lean_object* v_n_22_, lean_object* v_Rmax_23_, lean_object* v_Emax_24_, lean_object* v_Dmax_25_, lean_object* v_hn_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
lean_inc_n(v_Rmax_23_, 2);
lean_inc(v_n_22_);
v___x_27_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed), 6, 5);
lean_closure_set(v___x_27_, 0, v_n_22_);
lean_closure_set(v___x_27_, 1, v_Rmax_23_);
lean_closure_set(v___x_27_, 2, v_Emax_24_);
lean_closure_set(v___x_27_, 3, v_Dmax_25_);
lean_closure_set(v___x_27_, 4, lean_box(0));
v___x_28_ = lp_SSExactMajority_SSEM_protocolPEM(v_n_22_, v_Rmax_23_, v_Rmax_23_, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ConcretePEM___redArg(lean_object* v_n_29_, lean_object* v_Emax_30_, lean_object* v_Dmax_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
lean_inc_n(v_n_29_, 4);
v___x_32_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed), 6, 5);
lean_closure_set(v___x_32_, 0, v_n_29_);
lean_closure_set(v___x_32_, 1, v_n_29_);
lean_closure_set(v___x_32_, 2, v_Emax_30_);
lean_closure_set(v___x_32_, 3, v_Dmax_31_);
lean_closure_set(v___x_32_, 4, lean_box(0));
v___x_33_ = lp_SSExactMajority_SSEM_protocolPEM(v_n_29_, v_n_29_, v_n_29_, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_ConcretePEM(lean_object* v_n_34_, lean_object* v_Emax_35_, lean_object* v_Dmax_36_, lean_object* v_hn_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_inc_n(v_n_34_, 4);
v___x_38_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_rankDeltaOSSR___boxed), 6, 5);
lean_closure_set(v___x_38_, 0, v_n_34_);
lean_closure_set(v___x_38_, 1, v_n_34_);
lean_closure_set(v___x_38_, 2, v_Emax_35_);
lean_closure_set(v___x_38_, 3, v_Dmax_36_);
lean_closure_set(v___x_38_, 4, lean_box(0));
v___x_39_ = lp_SSExactMajority_SSEM_protocolPEM(v_n_34_, v_n_34_, v_n_34_, v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_wrongLowBSet___lam__0(lean_object* v_C_40_, lean_object* v_n_41_, lean_object* v_a_42_){
_start:
{
lean_object* v___x_43_; lean_object* v_fst_44_; lean_object* v_snd_45_; uint8_t v___x_46_; uint8_t v___x_47_; uint8_t v___x_48_; 
lean_inc_ref(v_C_40_);
v___x_43_ = lean_apply_1(v_C_40_, v_a_42_);
v_fst_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc(v_fst_44_);
v_snd_45_ = lean_ctor_get(v___x_43_, 1);
lean_inc(v_snd_45_);
lean_dec_ref(v___x_43_);
v___x_46_ = 1;
v___x_47_ = lean_unbox(v_snd_45_);
lean_dec(v_snd_45_);
v___x_48_ = lp_SSExactMajority_SSEM_instDecidableEqOpinion(v___x_47_, v___x_46_);
if (v___x_48_ == 0)
{
lean_dec(v_fst_44_);
lean_dec(v_n_41_);
lean_dec_ref(v_C_40_);
return v___x_48_;
}
else
{
lean_object* v_rank_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v_rank_49_ = lean_ctor_get(v_fst_44_, 0);
lean_inc(v_rank_49_);
lean_dec(v_fst_44_);
v___x_50_ = lp_SSExactMajority_SSEM_nAOf(v_n_41_, v_C_40_);
v___x_51_ = lean_nat_dec_lt(v_rank_49_, v___x_50_);
lean_dec(v___x_50_);
lean_dec(v_rank_49_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongLowBSet___lam__0___boxed(lean_object* v_C_52_, lean_object* v_n_53_, lean_object* v_a_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = lp_SSExactMajority_SSEM_wrongLowBSet___lam__0(v_C_52_, v_n_53_, v_a_54_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongLowBSet(lean_object* v_n_57_, lean_object* v_C_58_){
_start:
{
lean_object* v___f_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
lean_inc(v_n_57_);
v___f_59_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_wrongLowBSet___lam__0___boxed), 3, 2);
lean_closure_set(v___f_59_, 0, v_C_58_);
lean_closure_set(v___f_59_, 1, v_n_57_);
v___x_60_ = l_List_finRange(v_n_57_);
v___x_61_ = lp_mathlib_Multiset_filter___redArg(v___f_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_wrongHighASet___lam__0(lean_object* v_C_62_, lean_object* v_n_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_65_; lean_object* v_fst_66_; lean_object* v_snd_67_; uint8_t v___x_68_; uint8_t v___x_69_; uint8_t v___x_70_; 
lean_inc_ref(v_C_62_);
v___x_65_ = lean_apply_1(v_C_62_, v_a_64_);
v_fst_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_fst_66_);
v_snd_67_ = lean_ctor_get(v___x_65_, 1);
lean_inc(v_snd_67_);
lean_dec_ref(v___x_65_);
v___x_68_ = 0;
v___x_69_ = lean_unbox(v_snd_67_);
lean_dec(v_snd_67_);
v___x_70_ = lp_SSExactMajority_SSEM_instDecidableEqOpinion(v___x_69_, v___x_68_);
if (v___x_70_ == 0)
{
lean_dec(v_fst_66_);
lean_dec(v_n_63_);
lean_dec_ref(v_C_62_);
return v___x_70_;
}
else
{
lean_object* v_rank_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v_rank_71_ = lean_ctor_get(v_fst_66_, 0);
lean_inc(v_rank_71_);
lean_dec(v_fst_66_);
v___x_72_ = lp_SSExactMajority_SSEM_nAOf(v_n_63_, v_C_62_);
v___x_73_ = lean_nat_dec_le(v___x_72_, v_rank_71_);
lean_dec(v_rank_71_);
lean_dec(v___x_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongHighASet___lam__0___boxed(lean_object* v_C_74_, lean_object* v_n_75_, lean_object* v_a_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = lp_SSExactMajority_SSEM_wrongHighASet___lam__0(v_C_74_, v_n_75_, v_a_76_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongHighASet(lean_object* v_n_79_, lean_object* v_C_80_){
_start:
{
lean_object* v___f_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
lean_inc(v_n_79_);
v___f_81_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_wrongHighASet___lam__0___boxed), 3, 2);
lean_closure_set(v___f_81_, 0, v_C_80_);
lean_closure_set(v___f_81_, 1, v_n_79_);
v___x_82_ = l_List_finRange(v_n_79_);
v___x_83_ = lp_mathlib_Multiset_filter___redArg(v___f_81_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_lowRankSet___lam__0(lean_object* v_C_84_, lean_object* v_n_85_, lean_object* v_a_86_){
_start:
{
lean_object* v___x_87_; lean_object* v_fst_88_; lean_object* v_rank_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
lean_inc_ref(v_C_84_);
v___x_87_ = lean_apply_1(v_C_84_, v_a_86_);
v_fst_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_fst_88_);
lean_dec_ref(v___x_87_);
v_rank_89_ = lean_ctor_get(v_fst_88_, 0);
lean_inc(v_rank_89_);
lean_dec(v_fst_88_);
v___x_90_ = lp_SSExactMajority_SSEM_nAOf(v_n_85_, v_C_84_);
v___x_91_ = lean_nat_dec_lt(v_rank_89_, v___x_90_);
lean_dec(v___x_90_);
lean_dec(v_rank_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowRankSet___lam__0___boxed(lean_object* v_C_92_, lean_object* v_n_93_, lean_object* v_a_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = lp_SSExactMajority_SSEM_lowRankSet___lam__0(v_C_92_, v_n_93_, v_a_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowRankSet(lean_object* v_n_97_, lean_object* v_C_98_){
_start:
{
lean_object* v___f_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
lean_inc(v_n_97_);
v___f_99_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_lowRankSet___lam__0___boxed), 3, 2);
lean_closure_set(v___f_99_, 0, v_C_98_);
lean_closure_set(v___f_99_, 1, v_n_97_);
v___x_100_ = l_List_finRange(v_n_97_);
v___x_101_ = lp_mathlib_Multiset_filter___redArg(v___f_99_, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_lowASet___lam__0(lean_object* v_C_102_, lean_object* v_n_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_105_; lean_object* v_fst_106_; lean_object* v_snd_107_; uint8_t v___x_108_; uint8_t v___x_109_; uint8_t v___x_110_; 
lean_inc_ref(v_C_102_);
v___x_105_ = lean_apply_1(v_C_102_, v_a_104_);
v_fst_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_fst_106_);
v_snd_107_ = lean_ctor_get(v___x_105_, 1);
lean_inc(v_snd_107_);
lean_dec_ref(v___x_105_);
v___x_108_ = 0;
v___x_109_ = lean_unbox(v_snd_107_);
lean_dec(v_snd_107_);
v___x_110_ = lp_SSExactMajority_SSEM_instDecidableEqOpinion(v___x_109_, v___x_108_);
if (v___x_110_ == 0)
{
lean_dec(v_fst_106_);
lean_dec(v_n_103_);
lean_dec_ref(v_C_102_);
return v___x_110_;
}
else
{
lean_object* v_rank_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_rank_111_ = lean_ctor_get(v_fst_106_, 0);
lean_inc(v_rank_111_);
lean_dec(v_fst_106_);
v___x_112_ = lp_SSExactMajority_SSEM_nAOf(v_n_103_, v_C_102_);
v___x_113_ = lean_nat_dec_lt(v_rank_111_, v___x_112_);
lean_dec(v___x_112_);
lean_dec(v_rank_111_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowASet___lam__0___boxed(lean_object* v_C_114_, lean_object* v_n_115_, lean_object* v_a_116_){
_start:
{
uint8_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = lp_SSExactMajority_SSEM_lowASet___lam__0(v_C_114_, v_n_115_, v_a_116_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_lowASet(lean_object* v_n_119_, lean_object* v_C_120_){
_start:
{
lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
lean_inc(v_n_119_);
v___f_121_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_lowASet___lam__0___boxed), 3, 2);
lean_closure_set(v___f_121_, 0, v_C_120_);
lean_closure_set(v___f_121_, 1, v_n_119_);
v___x_122_ = l_List_finRange(v_n_119_);
v___x_123_ = lp_mathlib_Multiset_filter___redArg(v___f_121_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongLowBCount(lean_object* v_n_124_, lean_object* v_C_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lp_SSExactMajority_SSEM_wrongLowBSet(v_n_124_, v_C_125_);
v___x_127_ = l_List_lengthTR___redArg(v___x_126_);
lean_dec(v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_wrongHighACount(lean_object* v_n_128_, lean_object* v_C_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lp_SSExactMajority_SSEM_wrongHighASet(v_n_128_, v_C_129_);
v___x_131_ = l_List_lengthTR___redArg(v___x_130_);
lean_dec(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_richResetSeedSet___lam__0(lean_object* v_C_132_, lean_object* v_n_133_, lean_object* v_a_134_){
_start:
{
lean_object* v___x_135_; lean_object* v_fst_136_; uint8_t v_role_137_; lean_object* v_resetcount_138_; uint8_t v_answer_139_; uint8_t v___x_140_; uint8_t v___x_141_; 
lean_inc_ref(v_C_132_);
v___x_135_ = lean_apply_1(v_C_132_, v_a_134_);
v_fst_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_fst_136_);
lean_dec_ref(v___x_135_);
v_role_137_ = lean_ctor_get_uint8(v_fst_136_, sizeof(void*)*6);
v_resetcount_138_ = lean_ctor_get(v_fst_136_, 1);
lean_inc(v_resetcount_138_);
v_answer_139_ = lean_ctor_get_uint8(v_fst_136_, sizeof(void*)*6 + 2);
lean_dec(v_fst_136_);
v___x_140_ = 0;
v___x_141_ = lp_SSExactMajority_SSEM_instDecidableEqRole(v_role_137_, v___x_140_);
if (v___x_141_ == 0)
{
lean_dec(v_resetcount_138_);
lean_dec(v_n_133_);
lean_dec_ref(v_C_132_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; uint8_t v___x_143_; 
lean_inc_ref(v_C_132_);
lean_inc(v_n_133_);
v___x_142_ = lp_SSExactMajority_SSEM_nonResettingCount(v_n_133_, v_C_132_);
v___x_143_ = lean_nat_dec_lt(v___x_142_, v_resetcount_138_);
lean_dec(v_resetcount_138_);
lean_dec(v___x_142_);
if (v___x_143_ == 0)
{
lean_dec(v_n_133_);
lean_dec_ref(v_C_132_);
return v___x_143_;
}
else
{
uint8_t v___x_144_; uint8_t v___x_145_; 
v___x_144_ = lp_SSExactMajority_SSEM_majorityAnswer(v_n_133_, v_C_132_);
v___x_145_ = lp_SSExactMajority_SSEM_instDecidableEqAnswer(v_answer_139_, v___x_144_);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_richResetSeedSet___lam__0___boxed(lean_object* v_C_146_, lean_object* v_n_147_, lean_object* v_a_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = lp_SSExactMajority_SSEM_richResetSeedSet___lam__0(v_C_146_, v_n_147_, v_a_148_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_richResetSeedSet(lean_object* v_n_151_, lean_object* v_C_152_){
_start:
{
lean_object* v___f_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
lean_inc(v_n_151_);
v___f_153_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_richResetSeedSet___lam__0___boxed), 3, 2);
lean_closure_set(v___f_153_, 0, v_C_152_);
lean_closure_set(v___f_153_, 1, v_n_151_);
v___x_154_ = l_List_finRange(v_n_151_);
v___x_155_ = lp_mathlib_Multiset_filter___redArg(v___f_153_, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_richResetSeedCount(lean_object* v_n_156_, lean_object* v_C_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lp_SSExactMajority_SSEM_richResetSeedSet(v_n_156_, v_C_157_);
v___x_159_ = l_List_lengthTR___redArg(v___x_158_);
lean_dec(v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_UpperBound_Time_0__SSEM_propagateReset_match__1_splitter___redArg(lean_object* v_x_160_, lean_object* v_h__1_161_){
_start:
{
lean_object* v_fst_162_; lean_object* v_snd_163_; lean_object* v___x_164_; 
v_fst_162_ = lean_ctor_get(v_x_160_, 0);
lean_inc(v_fst_162_);
v_snd_163_ = lean_ctor_get(v_x_160_, 1);
lean_inc(v_snd_163_);
lean_dec_ref(v_x_160_);
v___x_164_ = lean_apply_2(v_h__1_161_, v_fst_162_, v_snd_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_UpperBound_Time_0__SSEM_propagateReset_match__1_splitter(lean_object* v_n_165_, lean_object* v_motive_166_, lean_object* v_x_167_, lean_object* v_h__1_168_){
_start:
{
lean_object* v_fst_169_; lean_object* v_snd_170_; lean_object* v___x_171_; 
v_fst_169_ = lean_ctor_get(v_x_167_, 0);
lean_inc(v_fst_169_);
v_snd_170_ = lean_ctor_get(v_x_167_, 1);
lean_inc(v_snd_170_);
lean_dec_ref(v_x_167_);
v___x_171_ = lean_apply_2(v_h__1_168_, v_fst_169_, v_snd_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority___private_SSExactMajority_UpperBound_Time_0__SSEM_propagateReset_match__1_splitter___boxed(lean_object* v_n_172_, lean_object* v_motive_173_, lean_object* v_x_174_, lean_object* v_h__1_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = lp_SSExactMajority___private_SSExactMajority_UpperBound_Time_0__SSEM_propagateReset_match__1_splitter(v_n_172_, v_motive_173_, v_x_174_, v_h__1_175_);
lean_dec(v_n_172_);
return v_res_176_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_BurmanConvergenceFinal(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Probability_ExpectedTime(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_PSeries(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time(uint8_t builtin) {
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
res = initialize_mathlib_Mathlib_Analysis_PSeries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
