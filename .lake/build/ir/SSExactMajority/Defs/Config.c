// Lean compiler output
// Module: SSExactMajority.Defs.Config
// Imports: public import Init public meta import Init public import SSExactMajority.Defs.Protocol public import Mathlib.Data.Fintype.Basic public import Mathlib.Data.Finset.Basic
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
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_stateOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_stateOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_stateOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_inputOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_inputOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_inputOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_outputOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_outputOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_outputOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_step___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_step___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Config_agentsWithInput___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_stateOf___redArg(lean_object* v_C_1_, lean_object* v_v_2_){
_start:
{
lean_object* v___x_3_; lean_object* v_fst_4_; 
v___x_3_ = lean_apply_1(v_C_1_, v_v_2_);
v_fst_4_ = lean_ctor_get(v___x_3_, 0);
lean_inc(v_fst_4_);
lean_dec_ref(v___x_3_);
return v_fst_4_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_stateOf(lean_object* v_Q_5_, lean_object* v_X_6_, lean_object* v_n_7_, lean_object* v_C_8_, lean_object* v_v_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lp_SSExactMajority_SSEM_Config_stateOf___redArg(v_C_8_, v_v_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_stateOf___boxed(lean_object* v_Q_11_, lean_object* v_X_12_, lean_object* v_n_13_, lean_object* v_C_14_, lean_object* v_v_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_SSExactMajority_SSEM_Config_stateOf(v_Q_11_, v_X_12_, v_n_13_, v_C_14_, v_v_15_);
lean_dec(v_n_13_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_inputOf___redArg(lean_object* v_C_17_, lean_object* v_v_18_){
_start:
{
lean_object* v___x_19_; lean_object* v_snd_20_; 
v___x_19_ = lean_apply_1(v_C_17_, v_v_18_);
v_snd_20_ = lean_ctor_get(v___x_19_, 1);
lean_inc(v_snd_20_);
lean_dec_ref(v___x_19_);
return v_snd_20_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_inputOf(lean_object* v_Q_21_, lean_object* v_X_22_, lean_object* v_n_23_, lean_object* v_C_24_, lean_object* v_v_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_SSExactMajority_SSEM_Config_inputOf___redArg(v_C_24_, v_v_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_inputOf___boxed(lean_object* v_Q_27_, lean_object* v_X_28_, lean_object* v_n_29_, lean_object* v_C_30_, lean_object* v_v_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_SSExactMajority_SSEM_Config_inputOf(v_Q_27_, v_X_28_, v_n_29_, v_C_30_, v_v_31_);
lean_dec(v_n_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_outputOf___redArg(lean_object* v_P_33_, lean_object* v_C_34_, lean_object* v_v_35_){
_start:
{
lean_object* v_00_u03c0__out_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v_00_u03c0__out_36_ = lean_ctor_get(v_P_33_, 1);
lean_inc(v_00_u03c0__out_36_);
lean_dec_ref(v_P_33_);
v___x_37_ = lean_apply_1(v_C_34_, v_v_35_);
v___x_38_ = lean_apply_1(v_00_u03c0__out_36_, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_outputOf(lean_object* v_Q_39_, lean_object* v_X_40_, lean_object* v_Y_41_, lean_object* v_n_42_, lean_object* v_P_43_, lean_object* v_C_44_, lean_object* v_v_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lp_SSExactMajority_SSEM_Config_outputOf___redArg(v_P_43_, v_C_44_, v_v_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_outputOf___boxed(lean_object* v_Q_47_, lean_object* v_X_48_, lean_object* v_Y_49_, lean_object* v_n_50_, lean_object* v_P_51_, lean_object* v_C_52_, lean_object* v_v_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_SSExactMajority_SSEM_Config_outputOf(v_Q_47_, v_X_48_, v_Y_49_, v_n_50_, v_P_51_, v_C_52_, v_v_53_);
lean_dec(v_n_50_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_step___redArg(lean_object* v_P_55_, lean_object* v_C_56_, lean_object* v_u_57_, lean_object* v_v_58_, lean_object* v_a_59_){
_start:
{
uint8_t v___x_60_; 
v___x_60_ = lean_nat_dec_eq(v_u_57_, v_v_58_);
if (v___x_60_ == 0)
{
lean_object* v_00_u03b4_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_94_; 
v_00_u03b4_61_ = lean_ctor_get(v_P_55_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v_P_55_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; 
v_unused_95_ = lean_ctor_get(v_P_55_, 1);
lean_dec(v_unused_95_);
v___x_63_ = v_P_55_;
v_isShared_64_ = v_isSharedCheck_94_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_00_u03b4_61_);
lean_dec(v_P_55_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_94_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
lean_inc_ref_n(v_C_56_, 2);
lean_inc(v_u_57_);
v___x_65_ = lean_apply_1(v_C_56_, v_u_57_);
lean_inc(v_v_58_);
v___x_66_ = lean_apply_1(v_C_56_, v_v_58_);
lean_inc_ref(v___x_66_);
lean_inc_ref(v___x_65_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 1, v___x_66_);
lean_ctor_set(v___x_63_, 0, v___x_65_);
v___x_68_ = v___x_63_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v___x_66_);
v___x_68_ = v_reuseFailAlloc_93_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v_result_69_; uint8_t v___x_70_; 
v_result_69_ = lean_apply_1(v_00_u03b4_61_, v___x_68_);
v___x_70_ = lean_nat_dec_eq(v_a_59_, v_u_57_);
lean_dec(v_u_57_);
if (v___x_70_ == 0)
{
uint8_t v___x_71_; 
lean_dec_ref(v___x_65_);
v___x_71_ = lean_nat_dec_eq(v_a_59_, v_v_58_);
lean_dec(v_v_58_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; 
lean_dec_ref(v_result_69_);
lean_dec_ref(v___x_66_);
v___x_72_ = lean_apply_1(v_C_56_, v_a_59_);
return v___x_72_;
}
else
{
lean_object* v_snd_73_; lean_object* v_snd_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_81_; 
lean_dec(v_a_59_);
lean_dec_ref(v_C_56_);
v_snd_73_ = lean_ctor_get(v_result_69_, 1);
lean_inc(v_snd_73_);
lean_dec_ref(v_result_69_);
v_snd_74_ = lean_ctor_get(v___x_66_, 1);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_81_ == 0)
{
lean_object* v_unused_82_; 
v_unused_82_ = lean_ctor_get(v___x_66_, 0);
lean_dec(v_unused_82_);
v___x_76_ = v___x_66_;
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_snd_74_);
lean_dec(v___x_66_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_79_; 
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 0, v_snd_73_);
v___x_79_ = v___x_76_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_snd_73_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v_snd_74_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
else
{
lean_object* v_fst_83_; lean_object* v_snd_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
lean_dec_ref(v___x_66_);
lean_dec(v_a_59_);
lean_dec(v_v_58_);
lean_dec_ref(v_C_56_);
v_fst_83_ = lean_ctor_get(v_result_69_, 0);
lean_inc(v_fst_83_);
lean_dec_ref(v_result_69_);
v_snd_84_ = lean_ctor_get(v___x_65_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_91_ == 0)
{
lean_object* v_unused_92_; 
v_unused_92_ = lean_ctor_get(v___x_65_, 0);
lean_dec(v_unused_92_);
v___x_86_ = v___x_65_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_snd_84_);
lean_dec(v___x_65_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v_fst_83_);
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_fst_83_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_snd_84_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v_v_58_);
lean_dec(v_u_57_);
lean_dec_ref(v_P_55_);
v___x_96_ = lean_apply_1(v_C_56_, v_a_59_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_step(lean_object* v_Q_97_, lean_object* v_X_98_, lean_object* v_Y_99_, lean_object* v_n_100_, lean_object* v_P_101_, lean_object* v_C_102_, lean_object* v_u_103_, lean_object* v_v_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lp_SSExactMajority_SSEM_Config_step___redArg(v_P_101_, v_C_102_, v_u_103_, v_v_104_, v_a_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_step___boxed(lean_object* v_Q_107_, lean_object* v_X_108_, lean_object* v_Y_109_, lean_object* v_n_110_, lean_object* v_P_111_, lean_object* v_C_112_, lean_object* v_u_113_, lean_object* v_v_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = lp_SSExactMajority_SSEM_Config_step(v_Q_107_, v_X_108_, v_Y_109_, v_n_110_, v_P_111_, v_C_112_, v_u_113_, v_v_114_, v_a_115_);
lean_dec(v_n_110_);
return v_res_116_;
}
}
LEAN_EXPORT uint8_t lp_SSExactMajority_SSEM_Config_agentsWithInput___redArg___lam__0(lean_object* v_C_117_, lean_object* v_inst_118_, lean_object* v_x_119_, lean_object* v_a_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_121_ = lp_SSExactMajority_SSEM_Config_inputOf___redArg(v_C_117_, v_a_120_);
v___x_122_ = lean_apply_2(v_inst_118_, v___x_121_, v_x_119_);
v___x_123_ = lean_unbox(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___redArg___lam__0___boxed(lean_object* v_C_124_, lean_object* v_inst_125_, lean_object* v_x_126_, lean_object* v_a_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = lp_SSExactMajority_SSEM_Config_agentsWithInput___redArg___lam__0(v_C_124_, v_inst_125_, v_x_126_, v_a_127_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___redArg(lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_C_132_, lean_object* v_x_133_){
_start:
{
lean_object* v___f_134_; lean_object* v___x_135_; 
v___f_134_ = lean_alloc_closure((void*)(lp_SSExactMajority_SSEM_Config_agentsWithInput___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_134_, 0, v_C_132_);
lean_closure_set(v___f_134_, 1, v_inst_130_);
lean_closure_set(v___f_134_, 2, v_x_133_);
v___x_135_ = lp_mathlib_Multiset_filter___redArg(v___f_134_, v_inst_131_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput(lean_object* v_Q_136_, lean_object* v_X_137_, lean_object* v_n_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_C_141_, lean_object* v_x_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lp_SSExactMajority_SSEM_Config_agentsWithInput___redArg(v_inst_139_, v_inst_140_, v_C_141_, v_x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* lp_SSExactMajority_SSEM_Config_agentsWithInput___boxed(lean_object* v_Q_144_, lean_object* v_X_145_, lean_object* v_n_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_C_149_, lean_object* v_x_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = lp_SSExactMajority_SSEM_Config_agentsWithInput(v_Q_144_, v_X_145_, v_n_146_, v_inst_147_, v_inst_148_, v_C_149_, v_x_150_);
lean_dec(v_n_146_);
return v_res_151_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Protocol(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Config(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Defs_Protocol(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
