// Lean compiler output
// Module: SSExactMajority.UpperBound.Time.PhaseProofs
// Imports: public import Init public meta import Init public import SSExactMajority.UpperBound.Time.HeavyProofs public import SSExactMajority.UpperBound.Time.CRSOdd public import SSExactMajority.UpperBound.Time.CRSEven public import SSExactMajority.UpperBound.Time.RecoveryBound
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_HeavyProofs(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_CRSOdd(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_CRSEven(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_RecoveryBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority_UpperBound_Time_PhaseProofs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_UpperBound_Time_HeavyProofs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_UpperBound_Time_CRSOdd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_UpperBound_Time_CRSEven(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_UpperBound_Time_RecoveryBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
