// Lean compiler output
// Module: SSExactMajority
// Imports: public import Init public import SSExactMajority.Defs.Protocol public import SSExactMajority.Defs.Config public import SSExactMajority.Defs.Execution public import SSExactMajority.Defs.ExactMajority public import SSExactMajority.Embed public import SSExactMajority.Impossibility.WithoutN public import SSExactMajority.LowerBound.Space public import SSExactMajority.LowerBound.Time public import SSExactMajority.Protocol.State public import SSExactMajority.Protocol.Transition public import SSExactMajority.Protocol.Correctness public import SSExactMajority.Protocol.RankDelta public import SSExactMajority.Convergence.Silent public import SSExactMajority.Convergence.AnswerPreservation public import SSExactMajority.Convergence.StatePreservation public import SSExactMajority.Convergence.Step public import SSExactMajority.Convergence.Theorem4 public import SSExactMajority.Convergence.Sets public import SSExactMajority.Convergence.Schedule public import SSExactMajority.Convergence.Composition public import SSExactMajority.Convergence.SwapPhase public import SSExactMajority.Convergence.PotentialReach public import SSExactMajority.Convergence.SwapReach public import SSExactMajority.Convergence.DecisionReach public import SSExactMajority.Convergence.SwapStep public import SSExactMajority.Convergence.TrivialBase public import SSExactMajority.Convergence.NonMedianExistence public import SSExactMajority.Convergence.SwapStepTimer public import SSExactMajority.Convergence.Final public import SSExactMajority.Convergence.RankPreservation public import SSExactMajority.Convergence.TimerDescent public import SSExactMajority.Convergence.ResetCycle public import SSExactMajority.Convergence.MasterModuloBurman public import SSExactMajority.Convergence.MedianWitnesses public import SSExactMajority.Convergence.SwapVMedian public import SSExactMajority.Convergence.SwapFromRanking
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
lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Protocol(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Config(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Defs_Execution(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Defs_ExactMajority(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Embed(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Impossibility_WithoutN(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_LowerBound_Space(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_LowerBound_Time(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_State(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_Transition(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_Correctness(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Protocol_RankDelta(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_Silent(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_AnswerPreservation(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_StatePreservation(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_Step(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_Theorem4(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_Sets(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_Schedule(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_Composition(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_SwapPhase(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_PotentialReach(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_SwapReach(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_DecisionReach(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_SwapStep(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_TrivialBase(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_NonMedianExistence(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_SwapStepTimer(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_Final(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_RankPreservation(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_TimerDescent(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_ResetCycle(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_MasterModuloBurman(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_MedianWitnesses(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_SwapVMedian(uint8_t builtin);
lean_object* initialize_SSExactMajority_SSExactMajority_Convergence_SwapFromRanking(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SSExactMajority_SSExactMajority(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Defs_Protocol(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Defs_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Defs_Execution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Defs_ExactMajority(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Embed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Impossibility_WithoutN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_LowerBound_Space(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_LowerBound_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Protocol_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Protocol_Transition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Protocol_Correctness(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Protocol_RankDelta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_Silent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_AnswerPreservation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_StatePreservation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_Step(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_Theorem4(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_Sets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_Schedule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_Composition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_SwapPhase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_PotentialReach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_SwapReach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_DecisionReach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_SwapStep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_TrivialBase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_NonMedianExistence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_SwapStepTimer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_Final(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_RankPreservation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_TimerDescent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_ResetCycle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_MasterModuloBurman(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_MedianWitnesses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_SwapVMedian(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SSExactMajority_SSExactMajority_Convergence_SwapFromRanking(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
