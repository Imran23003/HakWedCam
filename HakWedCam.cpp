#include "Python.h"
#include "pycore_abstract.h"      // _PyIndex_Check()
#include "pycore_ceval.h"         // _PyEval_SignalAsyncExc()
#include "pycore_code.h"
#include "pycore_emscripten_signal.h"  // _Py_CHECK_EMSCRIPTEN_SIGNALS
#include "pycore_function.h"
#include "pycore_instruments.h"
#include "pycore_intrinsics.h"
#include "pycore_long.h"          // _PyLong_GetZero()
#include "pycore_moduleobject.h"  // PyModuleObject
#include "pycore_object.h"        // _PyObject_GC_TRACK()
#include "pycore_opcode_metadata.h"  // uop names
#include "pycore_opcode_utils.h"  // MAKE_FUNCTION_*
#include "pycore_pyerrors.h"      // _PyErr_GetRaisedException()
#include "pycore_pystate.h"       // _PyInterpreterState_GET()
#include "pycore_range.h"         // _PyRangeIterObject
#include "pycore_setobject.h"     // _PySet_NextEntry()
#include "pycore_sliceobject.h"   // _PyBuildSlice_ConsumeRefs
#include "pycore_sysmodule.h"     // _PySys_Audit()
#include "pycore_tuple.h"         // _PyTuple_ITEMS()
#include "pycore_typeobject.h"    // _PySuper_Lookup()

#include "pycore_dict.h"
#include "dictobject.h"
#include "pycore_frame.h"
#include "opcode.h"
#include "optimizer.h"
#include "pydtrace.h"
#include "setobject.h"


#define USE_COMPUTED_GOTOS 0
#include "ceval_macros.h"

/* Flow control macros */
#define GO_TO_INSTRUCTION(instname) ((void)0)

#define inst(name, ...) case name:
#define op(name, ...) /* NAME is ignored */
#define macro(name) static int MACRO_##name
#define super(name) static int SUPER_##name
#define family(name, ...) static int family_##name
#define pseudo(name) static int pseudo_##name

/* Annotations */
#define guard
#define override
#define specializing

// Dummy variables for stack effects.
static PyObject *value, *value1, *value2, *left, *right, *res, *sum, *prod, *sub;
static PyObject *container, *start, *stop, *v, *lhs, *rhs, *res2;
static PyObject *list, *tuple, *dict, *owner, *set, *str, *tup, *map, *keys;
static PyObject *exit_func, *lasti, *val, *retval, *obj, *iter, *exhausted;
static PyObject *aiter, *awaitable, *iterable, *w, *exc_value, *bc, *locals;
static PyObject *orig, *excs, *update, *b, *fromlist, *level, *from;
static PyObject **pieces, **values;
static size_t jump;
// Dummy variables for cache effects
static uint16_t invert, counter, index, hint;
#define unused 0  // Used in a macro def, can't be static
static uint32_t type_version;
static _PyExecutorObject *current_executor;

static PyObject *
dummy_func(
    PyThreadState *tstate,
    _PyInterpreterFrame *frame,
    unsigned char opcode,
    unsigned int oparg,
    _Py_CODEUNIT *next_instr,
    PyObject **stack_pointer,
    int throwflag,
    PyObject *args[]
)
{
    // Dummy labels.
    pop_1_error:
    // Dummy locals.
    PyObject *dummy;
    _Py_CODEUNIT *this_instr;
    PyObject *attr;
    PyObject *attrs;
    PyObject *bottom;
    PyObject *callable;
    PyObject *callargs;
    PyObject *codeobj;
    PyObject *cond;
    PyObject *descr;
    _PyInterpreterFrame  entry_frame;
    PyObject *exc;
    PyObject *exit;
    PyObject *fget;
    PyObject *fmt_spec;
    PyObject *func;
    uint32_t func_version;
    PyObject *getattribute;
    PyObject *kwargs;
    PyObject *kwdefaults;
    PyObject *len_o;
    PyObject *match;
    PyObject *match_type;
    PyObject *method;
    PyObject *mgr;
    Py_ssize_t min_args;
    PyObject *names;
    PyObject *new_exc;
    PyObject *next;
    PyObject *none;
    PyObject *null;
    PyObject *prev_exc;
    PyObject *receiver;
    PyObject *rest;
    int result;
    PyObject *self;
    PyObject *seq;
    PyObject *slice;
    PyObject *step;
    PyObject *subject;
    PyObject *top;
    PyObject *type;
    PyObject *typevars;
    int values_or_none;

    switch (opcode) {

// BEGIN BYTECODES //
        inst(NOP, (--)) {
        }

        family(RESUME, 0) = {
            RESUME_CHECK,
        };

        inst(RESUME, (--)) {
            TIER_ONE_ONLY
            assert(frame == tstate->current_frame);
            uintptr_t global_version =
                _Py_atomic_load_uintptr_relaxed(&tstate->interp->ceval.eval_breaker) &
                ~_PY_EVAL_EVENTS_MASK;
            uintptr_t code_version = _PyFrame_GetCode(frame)->_co_instrumentation_version;
            assert((code_version & 255) == 0);
            if (code_version != global_version) {
                int err = _Py_Instrument(_PyFrame_GetCode(frame), tstate->interp);
                ERROR_IF(err, error);
                next_instr = this_instr;
            }
            else {
                if ((oparg & RESUME_OPARG_LOCATION_MASK) < RESUME_AFTER_YIELD_FROM) {
                    CHECK_EVAL_BREAKER();
                }
                this_instr->op.code = RESUME_CHECK;
            }
        }

        inst(RESUME_CHECK, (--)) {
#if defined(__EMSCRIPTEN__)
            DEOPT_IF(_Py_emscripten_signal_clock == 0);
            _Py_emscripten_signal_clock -= Py_EMSCRIPTEN_SIGNAL_HANDLING;
#endif
            uintptr_t eval_breaker = _Py_atomic_load_uintptr_relaxed(&tstate->interp->ceval.eval_breaker);
            uintptr_t version = _PyFrame_GetCode(frame)->_co_instrumentation_version;
            assert((version & _PY_EVAL_EVENTS_MASK) == 0);
            DEOPT_IF(eval_breaker != version);
        }

        inst(INSTRUMENTED_RESUME, (--)) {
            uintptr_t global_version = _Py_atomic_load_uintptr_relaxed(&tstate->interp->ceval.eval_breaker) & ~_PY_EVAL_EVENTS_MASK;
            uintptr_t code_version = _PyFrame_GetCode(frame)->_co_instrumentation_version;
            if (code_version != global_version) {
                if (_Py_Instrument(_PyFrame_GetCode(frame), tstate->interp)) {
                    GOTO_ERROR(error);
                }
                next_instr = this_instr;
            }
            else {
                if ((oparg & RESUME_OPARG_LOCATION_MASK) < RESUME_AFTER_YIELD_FROM) {
                    CHECK_EVAL_BREAKER();
                }
                _PyFrame_SetStackPointer(frame, stack_pointer);
                int err = _Py_call_instrumentation(
                        tstate, oparg > 0, frame, this_instr);
                stack_pointer = _PyFrame_GetStackPointer(frame);
                ERROR_IF(err, error);
                if (frame->instr_ptr != this_instr) {
                    /* Instrumentation has jumped */
                    next_instr = frame->instr_ptr;
                    DISPATCH();
                }
            }
        }

        pseudo(LOAD_CLOSURE) = {
            LOAD_FAST,
        };

        inst(LOAD_FAST_CHECK, (-- value)) {
            value = GETLOCAL(oparg);
            ERROR_IF(value == NULL, unbound_local_error);
            Py_INCREF(value);
        }

        pure inst(LOAD_FAST, (-- value)) {
            value = GETLOCAL(oparg);
            assert(value != NULL);
            Py_INCREF(value);
        }

        inst(LOAD_FAST_AND_CLEAR, (-- value)) {
            value = GETLOCAL(oparg);
            // do not use SETLOCAL here, it decrefs the old value
            GETLOCAL(oparg) = NULL;
        }

        inst(LOAD_FAST_LOAD_FAST, ( -- value1, value2)) {
            uint32_t oparg1 = oparg >> 4;
            uint32_t oparg2 = oparg & 15;
            value1 = GETLOCAL(oparg1);
            value2 = GETLOCAL(oparg2);
            Py_INCREF(value1);
            Py_INCREF(value2);
        }

        pure inst(LOAD_CONST, (-- value)) {
            value = GETITEM(FRAME_CO_CONSTS, oparg);
            Py_INCREF(value);
        }

        inst(STORE_FAST, (value --)) {
            SETLOCAL(oparg, value);
        }

        pseudo(STORE_FAST_MAYBE_NULL) = {
            STORE_FAST,
        };

        inst(STORE_FAST_LOAD_FAST, (value1 -- value2)) {
            uint32_t oparg1 = oparg >> 4;
            uint32_t oparg2 = oparg & 15;
            SETLOCAL(oparg1, value1);
            value2 = GETLOCAL(oparg2);
            Py_INCREF(value2);
        }

        inst(STORE_FAST_STORE_FAST, (value2, value1 --)) {
            uint32_t oparg1 = oparg >> 4;
            uint32_t oparg2 = oparg & 15;
            SETLOCAL(oparg1, value1);
            SETLOCAL(oparg2, value2);
        }

        pure inst(POP_TOP, (value --)) {
            DECREF_INPUTS();
        }

        pure inst(PUSH_NULL, (-- res)) {
            res = NULL;
        }

        macro(END_FOR) = POP_TOP;

        inst(INSTRUMENTED_END_FOR, (receiver, value -- receiver)) {
            TIER_ONE_ONLY
            /* Need to create a fake StopIteration error here,
             * to conform to PEP 380 */
            if (PyGen_Check(receiver)) {
                PyErr_SetObject(PyExc_StopIteration, value);
                if (monitor_stop_iteration(tstate, frame, this_instr)) {
                    GOTO_ERROR(error);
                }
                PyErr_SetRaisedException(NULL);
            }
            DECREF_INPUTS();
        }

        pure inst(END_SEND, (receiver, value -- value)) {
            Py_DECREF(receiver);
        }

        inst(INSTRUMENTED_END_SEND, (receiver, value -- value)) {
            TIER_ONE_ONLY
            if (PyGen_Check(receiver) || PyCoro_CheckExact(receiver)) {
                PyErr_SetObject(PyExc_StopIteration, value);
                if (monitor_stop_iteration(tstate, frame, this_instr)) {
                    GOTO_ERROR(error);
                }
                PyErr_SetRaisedException(NULL);
            }
            Py_DECREF(receiver);
        }

        inst(UNARY_NEGATIVE, (value -- res)) {
            res = PyNumber_Negative(value);
            DECREF_INPUTS();
            ERROR_IF(res == NULL, error);
        }

        pure inst(UNARY_NOT, (value -- res)) {
            assert(PyBool_Check(value));
            res = Py_IsFalse(value) ? Py_True : Py_False;
        }

        family(TO_BOOL, INLINE_CACHE_ENTRIES_TO_BOOL) = {
            TO_BOOL_ALWAYS_TRUE,
            TO_BOOL_BOOL,
            TO_BOOL_INT,
            TO_BOOL_LIST,
            TO_BOOL_NONE,
            TO_BOOL_STR,
        };

        specializing op(_SPECIALIZE_TO_BOOL, (counter/1, value -- value)) {
            TIER_ONE_ONLY
            #if ENABLE_SPECIALIZATION
            if (ADAPTIVE_COUNTER_IS_ZERO(counter)) {
                next_instr = this_instr;
                _Py_Specialize_ToBool(value, next_instr);
                DISPATCH_SAME_OPARG();
            }
            STAT_INC(TO_BOOL, deferred);
            DECREMENT_ADAPTIVE_COUNTER(this_instr[1].cache);
            #endif  /* ENABLE_SPECIALIZATION */
        }

        op(_TO_BOOL, (value -- res)) {
            int err = PyObject_IsTrue(value);
            DECREF_INPUTS();
            ERROR_IF(err < 0, error);
            res = err ? Py_True : Py_False;
        }

        macro(TO_BOOL) = _SPECIALIZE_TO_BOOL + unused/2 + _TO_BOOL;

        inst(TO_BOOL_BOOL, (unused/1, unused/2, value -- value)) {
            DEOPT_IF(!PyBool_Check(value));
            STAT_INC(TO_BOOL, hit);
        }

        inst(TO_BOOL_INT, (unused/1, unused/2, value -- res)) {
            DEOPT_IF(!PyLong_CheckExact(value));
            STAT_INC(TO_BOOL, hit);
            if (_PyLong_IsZero((PyLongObject *)value)) {
                assert(_Py_IsImmortal(value));
                res = Py_False;
            }
            else {
                DECREF_INPUTS();
                res = Py_True;
            }
        }

        inst(TO_BOOL_LIST, (unused/1, unused/2, value -- res)) {
            DEOPT_IF(!PyList_CheckExact(value));
            STAT_INC(TO_BOOL, hit);
            res = Py_SIZE(value) ? Py_True : Py_False;
            DECREF_INPUTS();
        }

        inst(TO_BOOL_NONE, (unused/1, unused/2, value -- res)) {
            // This one is a bit weird, because we expect *some* failures:
            DEOPT_IF(!Py_IsNone(value));
            STAT_INC(TO_BOOL, hit);
            res = Py_False;
        }

        inst(TO_BOOL_STR, (unused/1, unused/2, value -- res)) {
            DEOPT_IF(!PyUnicode_CheckExact(value));
            STAT_INC(TO_BOOL, hit);
            if (value == &_Py_STR(empty)) {
                assert(_Py_IsImmortal(value));
                res = Py_False;
            }
            else {
                assert(Py_SIZE(value));
                DECREF_INPUTS();
                res = Py_True;
            }
        }

        inst(TO_BOOL_ALWAYS_TRUE, (unused/1, version/2, value -- res)) {
            // This one is a bit weird, because we expect *some* failures:
            assert(version);
            DEOPT_IF(Py_TYPE(value)->tp_version_tag != version);
            STAT_INC(TO_BOOL, hit);
            DECREF_INPUTS();
            res = Py_True;
        }

        inst(UNARY_INVERT, (value -- res)) {
            res = PyNumber_Invert(value);
            DECREF_INPUTS();
            ERROR_IF(res == NULL, error);
        }

        family(BINARY_OP, INLINE_CACHE_ENTRIES_BINARY_OP) = {
            BINARY_OP_MULTIPLY_INT,
            BINARY_OP_ADD_INT,
            BINARY_OP_SUBTRACT_INT,
            BINARY_OP_MULTIPLY_FLOAT,
            BINARY_OP_ADD_FLOAT,
            BINARY_OP_SUBTRACT_FLOAT,
            BINARY_OP_ADD_UNICODE,
            // BINARY_OP_INPLACE_ADD_UNICODE,  // See comments at that opcode.
        };

        op(_GUARD_BOTH_INT, (left, right -- left:  &PYLONG_TYPE, right:  &PYLONG_TYPE)) {
            DEOPT_IF(!PyLong_CheckExact(left));
            DEOPT_IF(!PyLong_CheckExact(right));
        }

        pure op(_BINARY_OP_MULTIPLY_INT, (left, right -- res: &PYLONG_TYPE)) {
            STAT_INC(BINARY_OP, hit);
            res = _PyLong_Multiply((PyLongObject *)left, (PyLongObject *)right);
            _Py_DECREF_SPECIALIZED(right, (destructor)PyObject_Free);
            _Py_DECREF_SPECIALIZED(left, (destructor)PyObject_Free);
            ERROR_IF(res == NULL, error);
        }

        pure op(_BINARY_OP_ADD_INT, (left, right -- res: &PYLONG_TYPE)) {
            STAT_INC(BINARY_OP, hit);
            res = _PyLong_Add((PyLongObject *)left, (PyLongObject *)right);
            _Py_DECREF_SPECIALIZED(right, (destructor)PyObject_Free);
            _Py_DECREF_SPECIALIZED(left, (destructor)PyObject_Free);
            ERROR_IF(res == NULL, error);
        }

        pure op(_BINARY_OP_SUBTRACT_INT, (left, right -- res: &PYLONG_TYPE)) {
            STAT_INC(BINARY_OP, hit);
            res = _PyLong_Subtract((PyLongObject *)left, (PyLongObject *)right);
            _Py_DECREF_SPECIALIZED(right, (destructor)PyObject_Free);
            _Py_DECREF_SPECIALIZED(left, (destructor)PyObject_Free);
            ERROR_IF(res == NULL, error);
        }

        macro(BINARY_OP_MULTIPLY_INT) =
            _GUARD_BOTH_INT + unused/1 + _BINARY_OP_MULTIPLY_INT;
        macro(BINARY_OP_ADD_INT) =
            _GUARD_BOTH_INT + unused/1 + _BINARY_OP_ADD_INT;
        macro(BINARY_OP_SUBTRACT_INT) =
            _GUARD_BOTH_INT + unused/1 + _BINARY_OP_SUBTRACT_INT;

        op(_GUARD_BOTH_FLOAT, (left, right -- left: &PYFLOAT_TYPE, right: &PYFLOAT_TYPE)) {
            DEOPT_IF(!PyFloat_CheckExact(left));
            DEOPT_IF(!PyFloat_CheckExact(right));
        }

        pure op(_BINARY_OP_MULTIPLY_FLOAT, (left, right -- res: &PYFLOAT_TYPE)) {
            STAT_INC(BINARY_OP, hit);
            double dres =
                ((PyFloatObject *)left)->ob_fval *
                ((PyFloatObject *)right)->ob_fval;
            DECREF_INPUTS_AND_REUSE_FLOAT(left, right, dres, res);
        }

        pure op(_BINARY_OP_ADD_FLOAT, (left, right -- res: &PYFLOAT_TYPE)) {
            STAT_INC(BINARY_OP, hit);
            double dres =
                ((PyFloatObject *)left)->ob_fval +
                ((PyFloatObject *)right)->ob_fval;
            DECREF_INPUTS_AND_REUSE_FLOAT(left, right, dres, res);
        }

        pure op(_BINARY_OP_SUBTRACT_FLOAT, (left, right -- res: &PYFLOAT_TYPE)) {
            STAT_INC(BINARY_OP, hit);
            double dres =
                ((PyFloatObject *)left)->ob_fval -
                ((PyFloatObject *)right)->ob_fval;
            DECREF_INPUTS_AND_REUSE_FLOAT(left, right, dres, res);
        }

        macro(BINARY_OP_MULTIPLY_FLOAT) =
            _GUARD_BOTH_FLOAT + unused/1 + _BINARY_OP_MULTIPLY_FLOAT;
        macro(BINARY_OP_ADD_FLOAT) =
            _GUARD_BOTH_FLOAT + unused/1 + _BINARY_OP_ADD_FLOAT;
        macro(BINARY_OP_SUBTRACT_FLOAT) =
            _GUARD_BOTH_FLOAT + unused/1 + _BINARY_OP_SUBTRACT_FLOAT;

        op(_GUARD_BOTH_UNICODE, (left, right -- left: &PYUNICODE_TYPE, right: &PYUNICODE_TYPE)) {
            DEOPT_IF(!PyUnicode_CheckExact(left));
            DEOPT_IF(!PyUnicode_CheckExact(right));
        }

        pure op(_BINARY_OP_ADD_UNICODE, (left, right -- res: &PYUNICODE_TYPE)) {
            STAT_INC(BINARY_OP, hit);
            res = PyUnicode_Concat(left, right);
            _Py_DECREF_SPECIALIZED(left, _PyUnicode_ExactDealloc);
            _Py_DECREF_SPECIALIZED(right, _PyUnicode_ExactDealloc);
            ERROR_IF(res == NULL, error);
        }

        macro(BINARY_OP_ADD_UNICODE) =
            _GUARD_BOTH_UNICODE + unused/1 + _BINARY_OP_ADD_UNICODE;

        // This is a subtle one. It's a super-instruction for
        // BINARY_OP_ADD_UNICODE followed by STORE_FAST
        // where the store goes into the left argument.
        // So the inputs are the same as for all BINARY_OP
        // specializations, but there is no output.
        // At the end we just skip over the STORE_FAST.
        op(_BINARY_OP_INPLACE_ADD_UNICODE, (left, right --)) {
            TIER_ONE_ONLY
            assert(next_instr->op.code == STORE_FAST);
            PyObject **target_local = &GETLOCAL(next_instr->op.arg);
            DEOPT_IF(*target_local != left);
            STAT_INC(BINARY_OP, hit);
            /* Handle `left = left + right` or `left += right` for str.
             *
             * When possible, extend `left` in place rather than
             * allocating a new PyUnicodeObject. This attempts to avoid
             * quadratic behavior when one neglects to use str.join().
             *
             * If `left` has only two references remaining (one from
             * the stack, one in the locals), DECREFing `left` leaves
             * only the locals reference, so PyUnicode_Append knows
             * that the string is safe to mutate.
             */
            assert(Py_REFCNT(left) >= 2);
            _Py_DECREF_NO_DEALLOC(left);
            PyUnicode_Append(target_local, right);
            _Py_DECREF_SPECIALIZED(right, _PyUnicode_ExactDealloc);
            ERROR_IF(*target_local == NULL, error);
            // The STORE_FAST is already done.
            assert(next_instr->op.code == STORE_FAST);
            SKIP_OVER(1);
        }

        macro(BINARY_OP_INPLACE_ADD_UNICODE) =
            _GUARD_BOTH_UNICODE + unused/1 + _BINARY_OP_INPLACE_ADD_UNICODE;

        family(BINARY_SUBSCR, INLINE_CACHE_ENTRIES_BINARY_SUBSCR) = {
            BINARY_SUBSCR_DICT,
            BINARY_SUBSCR_GETITEM,
            BINARY_SUBSCR_LIST_INT,
            BINARY_SUBSCR_STR_INT,
            BINARY_SUBSCR_TUPLE_INT,
        };

        specializing op(_SPECIALIZE_BINARY_SUBSCR, (counter/1, container, sub -- container, sub)) {
            TIER_ONE_ONLY
            #if ENABLE_SPECIALIZATION
            if (ADAPTIVE_COUNTER_IS_ZERO(counter)) {
                next_instr = this_instr;
                _Py_Specialize_BinarySubscr(container, sub, next_instr);
                DISPATCH_SAME_OPARG();
            }
            STAT_INC(BINARY_SUBSCR, deferred);
            DECREMENT_ADAPTIVE_COUNTER(this_instr[1].cache);
            #endif  /* ENABLE_SPECIALIZATION */
        }

        op(_BINARY_SUBSCR, (container, sub -- res)) {
            res = PyObject_GetItem(container, sub);
            DECREF_INPUTS();
            ERROR_IF(res == NULL, error);
        }

        macro(BINARY_SUBSCR) = _SPECIALIZE_BINARY_SUBSCR + _BINARY_SUBSCR;

        inst(BINARY_SLICE, (container, start, stop -- res)) {
            PyObject *slice = _PyBuildSlice_ConsumeRefs(start, stop);
            // Can't use ERROR_IF() here, because we haven't
            // DECREF'ed container yet, and we still own slice.
            if (slice == NULL) {
                res = NULL;
            }
            else {
                res = PyObject_GetItem(container, slice);
                Py_DECREF(slice);
            }
            Py_DECREF(container);
            ERROR_IF(res == NULL, error);
        }

        inst(STORE_SLICE, (v, container, start, stop -- )) {
            PyObject *slice = _PyBuildSlice_ConsumeRefs(start, stop);
            int err;
            if (slice == NULL) {
                err = 1;
            }
            else {
                err = PyObject_SetItem(container, slice, v);
                Py_DECREF(slice);
            }
            Py_DECREF(v);
            Py_DECREF(container);
            ERROR_IF(err, error);
        }

        inst(BINARY_SUBSCR_LIST_INT, (unused/1, list, sub -- res)) {
            DEOPT_IF(!PyLong_CheckExact(sub));
            DEOPT_IF(!PyList_CheckExact(list));

            // Deopt unless 0 <= sub < PyList_Size(list)
            DEOPT_IF(!_PyLong_IsNonNegativeCompact((PyLongObject *)sub));
            Py_ssize_t index = ((PyLongObject*)sub)->long_value.ob_digit[0];
            DEOPT_IF(index >= PyList_GET_SIZE(list));
            STAT_INC(BINARY_SUBSCR, hit);
            res = PyList_GET_ITEM(list, index);
            assert(res != NULL);
            Py_INCREF(res);
            _Py_DECREF_SPECIALIZED(sub, (destructor)PyObject_Free);
            Py_DECREF(list);
        }

        inst(BINARY_SUBSCR_STR_INT, (unused/1, str, sub -- res)) {
            DEOPT_IF(!PyLong_CheckExact(sub));
            DEOPT_IF(!PyUnicode_CheckExact(str));
            DEOPT_IF(!_PyLong_IsNonNegativeCompact((PyLongObject *)sub));
            Py_ssize_t index = ((PyLongObject*)sub)->long_value.ob_digit[0];
            DEOPT_IF(PyUnicode_GET_LENGTH(str) <= index);
            // Specialize for reading an ASCII character from any string:
            Py_UCS4 c = PyUnicode_READ_CHAR(str, index);
            DEOPT_IF(Py_ARRAY_LENGTH(_Py_SINGLETON(strings).ascii) <= c);
            STAT_INC(BINARY_SUBSCR, hit);
            res = (PyObject*)&_Py_SINGLETON(strings).ascii[c];
            _Py_DECREF_SPECIALIZED(sub, (destructor)PyObject_Free);
            Py_DECREF(str);
        }

        inst(BINARY_SUBSCR_TUPLE_INT, (unused/1, tuple, sub -- res)) {
            DEOPT_IF(!PyLong_CheckExact(sub));
            DEOPT_IF(!PyTuple_CheckExact(tuple));

            // Deopt unless 0 <= sub < PyTuple_Size(list)
            DEOPT_IF(!_PyLong_IsNonNegativeCompact((PyLongObject *)sub));
            Py_ssize_t index = ((PyLongObject*)sub)->long_value.ob_digit[0];
            DEOPT_IF(index >= PyTuple_GET_SIZE(tuple));
            STAT_INC(BINARY_SUBSCR, hit);
            res = PyTuple_GET_ITEM(tuple, index);
            assert(res != NULL);
            Py_INCREF(res);
            _Py_DECREF_SPECIALIZED(sub, (destructor)PyObject_Free);
            Py_DECREF(tuple);
        }

        inst(BINARY_SUBSCR_DICT, (unused/1, dict, sub -- res)) {
            DEOPT_IF(!PyDict_CheckExact(dict));
            STAT_INC(BINARY_SUBSCR, hit);
            int rc = PyDict_GetItemRef(dict, sub, &res);
            if (rc == 0) {
                _PyErr_SetKeyError(sub);
            }
            DECREF_INPUTS();
            ERROR_IF(rc <= 0, error); // not found or error
        }

        inst(BINARY_SUBSCR_GETITEM, (unused/1, container, sub -- unused)) {
            DEOPT_IF(tstate->interp->eval_frame);
            PyTypeObject *tp = Py_TYPE(container);
            DEOPT_IF(!PyType_HasFeature(tp, Py_TPFLAGS_HEAPTYPE));
            PyHeapTypeObject *ht = (PyHeapTypeObject *)tp;
            PyObject *cached = ht->_spec_cache.getitem;
            DEOPT_IF(cached == NULL);
            assert(PyFunction_Check(cached));
            PyFunctionObject *getitem = (PyFunctionObject *)cached;
            uint32_t cached_version = ht->_spec_cache.getitem_version;
            DEOPT_IF(getitem->func_version != cached_version);
            PyCodeObject *code = (PyCodeObject *)getitem->func_code;
            assert(code->co_argcount == 2);
            DEOPT_IF(!_PyThreadState_HasStackSpace(tstate, code->co_framesize));
            STAT_INC(BINARY_SUBSCR, hit);
            Py_INCREF(getitem);
            _PyInterpreterFrame *new_frame = _PyFrame_PushUnchecked(tstate, getitem, 2);
            STACK_SHRINK(2);
            new_frame->localsplus[0] = container;
            new_frame->localsplus[1] = sub;
            frame->return_offset = (uint16_t)(next_instr - this_instr);
            DISPATCH_INLINED(new_frame);
        }

        inst(LIST_APPEND, (list, unused[oparg-1], v -- list, unused[oparg-1])) {
            ERROR_IF(_PyList_AppendTakeRef((PyListObject *)list, v) < 0, error);
        }

        inst(SET_ADD, (set, unused[oparg-1], v -- set, unused[oparg-1])) {
            int err = PySet_Add(set, v);
            DECREF_INPUTS();
            ERROR_IF(err, error);
        }

        family(STORE_SUBSCR, INLINE_CACHE_ENTRIES_STORE_SUBSCR) = {
            STORE_SUBSCR_DICT,
            STORE_SUBSCR_LIST_INT,
        };

        specializing op(_SPECIALIZE_STORE_SUBSCR, (counter/1, container, sub -- container, sub)) {
            TIER_ONE_ONLY
            #if ENABLE_SPECIALIZATION
            if (ADAPTIVE_COUNTER_IS_ZERO(counter)) {
                next_instr = this_instr;
                _Py_Specialize_StoreSubscr(container, sub, next_instr);
                DISPATCH_SAME_OPARG();
            }
            STAT_INC(STORE_SUBSCR, deferred);
            DECREMENT_ADAPTIVE_COUNTER(this_instr[1].cache);
            #endif  /* ENABLE_SPECIALIZATION */
        }

        op(_STORE_SUBSCR, (v, container, sub -- )) {
            /* container[sub] = v */
            int err = PyObject_SetItem(container, sub, v);
            DECREF_INPUTS();
            ERROR_IF(err, error);
        }

        macro(STORE_SUBSCR) = _SPECIALIZE_STORE_SUBSCR + _STORE_SUBSCR;

        inst(STORE_SUBSCR_LIST_INT, (unused/1, value, list, sub -- )) {
            DEOPT_IF(!PyLong_CheckExact(sub));
            DEOPT_IF(!PyList_CheckExact(list));

            // Ensure nonnegative, zero-or-one-digit ints.
            DEOPT_IF(!_PyLong_IsNonNegativeCompact((PyLongObject *)sub));
            Py_ssize_t index = ((PyLongObject*)sub)->long_value.ob_digit[0];
            // Ensure index < len(list)
            DEOPT_IF(index >= PyList_GET_SIZE(list));
            STAT_INC(STORE_SUBSCR, hit);

            PyObject *old_value = PyList_GET_ITEM(list, index);
            PyList_SET_ITEM(list, index, value);
            assert(old_value != NULL);
            Py_DECREF(old_value);
            _Py_DECREF_SPECIALIZED(sub, (destructor)PyObject_Free);
            Py_DECREF(list);
        }

        inst(STORE_SUBSCR_DICT, (unused/1, value, dict, sub -- )) {
            DEOPT_IF(!PyDict_CheckExact(dict));
            STAT_INC(STORE_SUBSCR, hit);
            int err = _PyDict_SetItem_Take2((PyDictObject *)dict, sub, value);
            Py_DECREF(dict);
            ERROR_IF(err, error);
        }

        inst(DELETE_SUBSCR, (container, sub --)) {
            /* del container[sub] */
            int err = PyObject_DelItem(container, sub);
            DECREF_INPUTS();
            ERROR_IF(err, error);
        }

        inst(CALL_INTRINSIC_1, (value -- res)) {
            assert(oparg <= MAX_INTRINSIC_1);
            res = _PyIntrinsics_UnaryFunctions[oparg].func(tstate, value);
            DECREF_INPUTS();
            ERROR_IF(res == NULL, error);
        }

        inst(CALL_INTRINSIC_2, (value2, value1 -- res)) {
            assert(oparg <= MAX_INTRINSIC_2);
            res = _PyIntrinsics_BinaryFunctions[oparg].func(tstate, value2, value1);
            DECREF_INPUTS();
            ERROR_IF(res == NULL, error);
        }

        inst(RAISE_VARARGS, (args[oparg] -- )) {
            TIER_ONE_ONLY
            PyObject *cause = NULL, *exc = NULL;
            switch (oparg) {
            case 2:
                cause = args[1];
                /* fall through */
            case 1:
                exc = args[0];
                /* fall through */
            case 0:
                if (do_raise(tstate, exc, cause)) {
                    assert(oparg == 0);
                    monitor_reraise(tstate, frame, this_instr);
                    goto exception_unwind;
                }
                break;
            default:
                _PyErr_SetString(tstate, PyExc_SystemError,
                                 "bad RAISE_VARARGS oparg");
                break;
            }
            ERROR_IF(true, error);
        }

        inst(INTERPRETER_EXIT, (retval --)) {
            TIER_ONE_ONLY
            assert(frame == &entry_frame);
            assert(_PyFrame_IsIncomplete(frame));
            /* Restore previous frame and return. */
            tstate->current_frame = frame->previous;
            assert(!_PyErr_Occurred(tstate));
            tstate->c_recursion_remaining += PY_EVAL_C_STACK_UNITS;
            return retval;
        }

        // The stack effect here is ambiguous.
        // We definitely pop the return value off the stack on entry.
        // We also push it onto the stack on exit, but that's a
        // different frame, and it's accounted for by _PUSH_FRAME.
        op(_POP_FRAME, (retval --)) {
            #if TIER_ONE
            assert(frame != &entry_frame);
            #endif
            SYNC_SP();
            _PyFrame_SetStackPointer(frame, stack_pointer);
            assert(EMPTY());
            _Py_LeaveRecursiveCallPy(tstate);
            // GH-99729: We need to unlink the frame *before* clearing it:
            _PyInterpreterFrame *dying = frame;
            frame = tstate->current_frame = dying->previous;
            _PyEval_FrameClearAndPop(tstate, dying);
            _PyFrame_StackPush(frame, retval);
            LOAD_SP();
            LOAD_IP(frame->return_offset);
#if LLTRACE && TIER_ONE
            lltrace = maybe_lltrace_resume_frame(frame, &entry_frame, GLOBALS());
            if (lltrace < 0) {
                goto exit_unwind;
            }
#endif
        }

        macro(RETURN_VALUE) =
            _POP_FRAME;

        inst(INSTRUMENTED_RETURN_VALUE, (retval --)) {
            int err = _Py_call_instrumentation_arg(
                    tstate, PY_MONITORING_EVENT_PY_RETURN,
                    frame, this_instr, retval);
            if (err) GOTO_ERROR(error);
            STACK_SHRINK(1);
            assert(EMPTY());
            _PyFrame_SetStackPointer(frame, stack_pointer);
            _Py_LeaveRecursiveCallPy(tstate);
            assert(frame != &entry_frame);
            // GH-99729: We need to unlink the frame *before* clearing it:
            _PyInterpreterFrame *dying = frame;
            frame = tstate->current_frame = dying->previous;
            _PyEval_FrameClearAndPop(tstate, dying);
            _PyFrame_StackPush(frame, retval);
            LOAD_IP(frame->return_offset);
            goto resume_frame;
        }

        macro(RETURN_CONST) =
            LOAD_CONST +
            _POP_FRAME;

        inst(INSTRUMENTED_RETURN_CONST, (--)) {
            PyObject *retval = GETITEM(FRAME_CO_CONSTS, oparg);
            int err = _Py_call_instrumentation_arg(
                    tstate, PY_MONITORING_EVENT_PY_RETURN,
                    frame, this_instr, retval);
            if (err) GOTO_ERROR(error);
            Py_INCREF(retval);
            assert(EMPTY());
            _PyFrame_SetStackPointer(frame, stack_pointer);
            _Py_LeaveRecursiveCallPy(tstate);
            assert(frame != &entry_frame);
            // GH-99729: We need to unlink the frame *before* clearing it:
            _PyInterpreterFrame *dying = frame;
            frame = tstate->current_frame = dying->previous;
            _PyEval_FrameClearAndPop(tstate, dying);
            _PyFrame_StackPush(frame, retval);
            LOAD_IP(frame->return_offset);
            goto resume_frame;
        }

        inst(GET_AITER, (obj -- iter)) {
            unaryfunc getter = NULL;
            PyTypeObject *type = Py_TYPE(obj);

            if (type->tp_as_async != NULL) {
                getter = type->tp_as_async->am_aiter;
            }

            if (getter == NULL) {
                _PyErr_Format(tstate, PyExc_TypeError,
                              "'async for' requires an object with "
                              "__aiter__ method, got %.100s",
                              type->tp_name);
                DECREF_INPUTS();
                ERROR_IF(true, error);
            }

            iter = (*getter)(obj);
            DECREF_INPUTS();
            ERROR_IF(iter == NULL, error);

            if (Py_TYPE(iter)->tp_as_async == NULL ||
                    Py_TYPE(iter)->tp_as_async->am_anext == NULL) {

                _PyErr_Format(tstate, PyExc_TypeError,
                              "'async for' received an object from __aiter__ "
                              "that does not implement __anext__: %.100s",
                              Py_TYPE(iter)->tp_name);
                Py_DECREF(iter);
                ERROR_IF(true, error);
            }
        }

        inst(GET_ANEXT, (aiter -- aiter, awaitable)) {
            unaryfunc getter = NULL;
            PyObject *next_iter = NULL;
            PyTypeObject *type = Py_TYPE(aiter);

            if (PyAsyncGen_CheckExact(aiter)) {
                awaitable = type->tp_as_async->am_anext(aiter);
                if (awaitable == NULL) {
                    GOTO_ERROR(error);
                }
            } else {
                if (type->tp_as_async != NULL){
                    getter = type->tp_as_async->am_anext;
                }

                if (getter != NULL) {
                    next_iter = (*getter)(aiter);
                    if (next_iter == NULL) {
                        GOTO_ERROR(error);
                    }
                }
                else {
                    _PyErr_Format(tstate, PyExc_TypeError,
                                  "'async for' requires an iterator with "
                                  "__anext__ method, got %.100s",
                                  type->tp_name);
                    GOTO_ERROR(error);
                }

                awaitable = _PyCoro_GetAwaitableIter(next_iter);
                if (awaitable == NULL) {
                    _PyErr_FormatFromCause(
                        PyExc_TypeError,
                        "'async for' received an invalid object "
                        "from __anext__: %.100s",
                        Py_TYPE(next_iter)->tp_name);

                    Py_DECREF(next_iter);
                    GOTO_ERROR(error);
                } else {
                    Py_DECREF(next_iter);
                }
            }
        }

        inst(GET_AWAITABLE, (iterable -- iter)) {
            iter = _PyCoro_GetAwaitableIter(iterable);

            if (iter == NULL) {
                _PyEval_FormatAwaitableError(tstate, Py_TYPE(iterable), oparg);
            }

            DECREF_INPUTS();

            if (iter != NULL && PyCoro_CheckExact(iter)) {
                PyObject *yf = _PyGen_yf((PyGenObject*)iter);
                if (yf != NULL) {
                    /* `iter` is a coroutine object that is being
                       awaited, `yf` is a pointer to the current awaitable
                       being awaited on. */
                    Py_DECREF(yf);
                    Py_CLEAR(iter);
                    _PyErr_SetString(tstate, PyExc_RuntimeError,
                                     "coroutine is being awaited already");
                    /* The code below jumps to `error` if `iter` is NULL. */
                }
            }

            ERROR_IF(iter == NULL, error);
        }

        family(SEND, INLINE_CACHE_ENTRIES_SEND) = {
            SEND_GEN,
        };

        specializing op(_SPECIALIZE_SEND, (counter/1, receiver, unused -- receiver, unused)) {
            TIER_ONE_ONLY
            #if ENABLE_SPECIALIZATION
            if (ADAPTIVE_COUNTER_IS_ZERO(counter)) {
                next_instr = this_instr;
                _Py_Specialize_Send(receiver, next_instr);
                DISPATCH_SAME_OPARG();
            }
            STAT_INC(SEND, deferred);
            DECREMENT_ADAPTIVE_COUNTER(this_instr[1].cache);
            #endif  /* ENABLE_SPECIALIZATION */
        }

        op(_SEND, (receiver, v -- receiver, retval)) {
            assert(frame != &entry_frame);
            if ((tstate->interp->eval_frame == NULL) &&
                (Py_TYPE(receiver) == &PyGen_Type || Py_TYPE(receiver) == &PyCoro_Type) &&
                ((PyGenObject *)receiver)->gi_frame_state < FRAME_EXECUTING)
            {
                PyGenObject *gen = (PyGenObject *)receiver;
                _PyInterpreterFrame *gen_frame = (_PyInterpreterFrame *)gen->gi_iframe;
                STACK_SHRINK(1);
                _PyFrame_StackPush(gen_frame, v);
                gen->gi_frame_state = FRAME_EXECUTING;
                gen->gi_exc_state.previous_item = tstate->exc_info;
                tstate->exc_info = &gen->gi_exc_state;
                assert(next_instr - this_instr + oparg <= UINT16_MAX);
                frame->return_offset = (uint16_t)(next_instr - this_instr + oparg);
                DISPATCH_INLINED(gen_frame);
            }
            if (Py_IsNone(v) && PyIter_Check(receiver)) {
                retval = Py_TYPE(receiver)->tp_iternext(receiver);
            }
            else {
                retval = PyObject_CallMethodOneArg(receiver, &_Py_ID(send), v);
            }
            if (retval == NULL) {
                if (_PyErr_ExceptionMatches(tstate, PyExc_StopIteration)
                ) {
                    monitor_raise(tstate, frame, this_instr);
                }
                if (_PyGen_FetchStopIterationValue(&retval) == 0) {
                    assert(retval != NULL);
                    JUMPBY(oparg);
                }
                else {
                    GOTO_ERROR(error);
                }
            }
            Py_DECREF(v);
        }

        macro(SEND) = _SPECIALIZE_SEND + _SEND;

        inst(SEND_GEN, (unused/1, receiver, v -- receiver, unused)) {
            DEOPT_IF(tstate->interp->eval_frame);
            PyGenObject *gen = (PyGenObject *)receiver;
            DEOPT_IF(Py_TYPE(gen) != &PyGen_Type && Py_TYPE(gen) != &PyCoro_Type);
            DEOPT_IF(gen->gi_frame_state >= FRAME_EXECUTING);
            STAT_INC(SEND, hit);
            _PyInterpreterFrame *gen_frame = (_PyInterpreterFrame *)gen->gi_iframe;
            STACK_SHRINK(1);
            _PyFrame_StackPush(gen_frame, v);
            gen->gi_frame_state = FRAME_EXECUTING;
            gen->gi_exc_state.previous_item = tstate->exc_info;
            tstate->exc_info = &gen->gi_exc_state;
            assert(next_instr - this_instr + oparg <= UINT16_MAX);
            frame->return_offset = (uint16_t)(next_instr - this_instr + oparg);
            DISPATCH_INLINED(gen_frame);
        }

        inst(INSTRUMENTED_YIELD_VALUE, (retval -- unused)) {
            assert(frame != &entry_frame);
            frame->instr_ptr = next_instr;
            PyGenObject *gen = _PyFrame_GetGenerator(frame);
            assert(FRAME_SUSPENDED_YIELD_FROM == FRAME_SUSPENDED + 1);
            assert(oparg == 0 || oparg == 1);
            gen->gi_frame_state = FRAME_SUSPENDED + oparg;
            _PyFrame_SetStackPointer(frame, stack_pointer - 1);
            int err = _Py_call_instrumentation_arg(
                    tstate, PY_MONITORING_EVENT_PY_YIELD,
                    frame, this_instr, retval);
            if (err) GOTO_ERROR(error);
            tstate->exc_info = gen->gi_exc_state.previous_item;
            gen->gi_exc_state.previous_item = NULL;
            _Py_LeaveRecursiveCallPy(tstate);
            _PyInterpreterFrame *gen_frame = frame;
            frame = tstate->current_frame = frame->previous;
            gen_frame->previous = NULL;
            _PyFrame_StackPush(frame, retval);
            /* We don't know which of these is relevant here, so keep them equal */
            assert(INLINE_CACHE_ENTRIES_SEND == INLINE_CACHE_ENTRIES_FOR_ITER);
            LOAD_IP(1 + INLINE_CACHE_ENTRIES_SEND);
            goto resume_frame;
        }

        inst(YIELD_VALUE, (retval -- unused)) {
            TIER_ONE_ONLY
            // NOTE: It's important that YIELD_VALUE never raises an exception!
            // The compiler treats any exception raised here as a failed close()
            // or throw() call.
            assert(frame != &entry_frame);
            frame->instr_ptr = next_instr;
            PyGenObject *gen = _PyFrame_GetGenerator(frame);
            assert(FRAME_SUSPENDED_YIELD_FROM == FRAME_SUSPENDED + 1);
            assert(oparg == 0 || oparg == 1);
            gen->gi_frame_state = FRAME_SUSPENDED + oparg;
            _PyFrame_SetStackPointer(frame, stack_pointer - 1);
            tstate->exc_info = gen->gi_exc_state.previous_item;
            gen->gi_exc_state.previous_item = NULL;
            _Py_LeaveRecursiveCallPy(tstate);
            _PyInterpreterFrame *gen_frame = frame;
            frame = tstate->current_frame = frame->previous;
            gen_frame->previous = NULL;
            _PyFrame_StackPush(frame, retval);
            /* We don't know which of these is relevant here, so keep them equal */
            assert(INLINE_CACHE_ENTRIES_SEND == INLINE_CACHE_ENTRIES_FOR_ITER);
            LOAD_IP(1 + INLINE_CACHE_ENTRIES_SEND);
            goto resume_frame;
        }

        inst(POP_EXCEPT, (exc_value -- )) {
            _PyErr_StackItem *exc_info = tstate->exc_info;
            Py_XSETREF(exc_info->exc_value, exc_value == Py_None ? NULL : exc_value);
        }

        inst(RERAISE, (values[oparg], exc -- values[oparg])) {
            TIER_ONE_ONLY
            assert(oparg >= 0 && oparg <= 2);
            if (oparg) {
                PyObject *lasti = values[0];
                if (PyLong_Check(lasti)) {
                    frame->instr_ptr = _PyCode_CODE(_PyFrame_GetCode(frame)) + PyLong_AsLong(lasti);
                    assert(!_PyErr_Occurred(tstate));
                }
                else {
                    assert(PyLong_Check(lasti));
                    _PyErr_SetString(tstate, PyExc_SystemError, "lasti is not an int");
                    GOTO_ERROR(error);
                }
            }
            assert(exc && PyExceptionInstance_Check(exc));
            Py_INCREF(exc);
            _PyErr_SetRaisedException(tstate, exc);
            monitor_reraise(tstate, frame, this_instr);
            goto exception_unwind;
        }

        inst(END_ASYNC_FOR, (awaitable, exc -- )) {
            TIER_ONE_ONLY
            assert(exc && PyExceptionInstance_Check(exc));
            if (PyErr_GivenExceptionMatches(exc, PyExc_StopAsyncIteration)) {
                DECREF_INPUTS();
            }
            else {
                Py_INCREF(exc);
                _PyErr_SetRaisedException(tstate, exc);
                monitor_reraise(tstate, frame, this_instr);
                goto exception_unwind;
            }
        }

        inst(CLEANUP_THROW, (sub_iter, last_sent_val, exc_value -- none, value)) {
            TIER_ONE_ONLY
            assert(throwflag);
            assert(exc_value && PyExceptionInstance_Check(exc_value));
            if (PyErr_GivenExceptionMatches(exc_value, PyExc_StopIteration)) {
                value = Py_NewRef(((PyStopIterationObject *)exc_value)->value);
                DECREF_INPUTS();
                none = Py_None;
            }
            else {
                _PyErr_SetRaisedException(tstate, Py_NewRef(exc_value));
                monitor_reraise(tstate, frame, this_instr);
                goto exception_unwind;
            }
        }

        inst(LOAD_ASSERTION_ERROR, ( -- value)) {
            value = Py_NewRef(PyExc_AssertionError);
        }

        inst(LOAD_BUILD_CLASS, ( -- bc)) {
            ERROR_IF(PyMapping_GetOptionalItem(BUILTINS(), &_Py_ID(__build_class__), &bc) < 0, error);
            if (bc == NULL) {
                _PyErr_SetString(tstate, PyExc_NameError,
                                 "__build_class__ not found");
                ERROR_IF(true, error);
            }
        }

        inst(STORE_NAME, (v -- )) {
            PyObject *name = GETITEM(FRAME_CO_NAMES, oparg);
            PyObject *ns = LOCALS();
            int err;
            if (ns == NULL) {
                _PyErr_Format(tstate, PyExc_SystemError,
                              "no locals found when storing %R", name);
                DECREF_INPUTS();
                ERROR_IF(true, error);
            }
            if (PyDict_CheckExact(ns))
                err = PyDict_SetItem(ns, name, v);
            else
                err = PyObject_SetItem(ns, name, v);
            DECREF_INPUTS();
            ERROR_IF(err, error);
        }

        inst(DELETE_NAME, (--)) {
            PyObject *name = GETITEM(FRAME_CO_NAMES, oparg);
            PyObject *ns = LOCALS();
            int err;
            if (ns == NULL) {
                _PyErr_Format(tstate, PyExc_SystemError,
                              "no locals when deleting %R", name);
                GOTO_ERROR(error);
            }
            err = PyObject_DelItem(ns, name);
            // Can't use ERROR_IF here.
            if (err != 0) {
                _PyEval_FormatExcCheckArg(tstate, PyExc_NameError,
                                          NAME_ERROR_MSG,
                                          name);
                GOTO_ERROR(error);
            }
        }

        family(UNPACK_SEQUENCE, INLINE_CACHE_ENTRIES_UNPACK_SEQUENCE) = {
            UNPACK_SEQUENCE_TWO_TUPLE,
            UNPACK_SEQUENCE_TUPLE,
            UNPACK_SEQUENCE_LIST,
        };

        specializing op(_SPECIALIZE_UNPACK_SEQUENCE, (counter/1, seq -- seq)) {
            TIER_ONE_ONLY
            #if ENABLE_SPECIALIZATION
            if (ADAPTIVE_COUNTER_IS_ZERO(counter)) {
                next_instr = this_instr;
                _Py_Specialize_UnpackSequence(seq, next_instr, oparg);
                DISPATCH_SAME_OPARG();
            }
            STAT_INC(UNPACK_SEQUENCE, deferred);
            DECREMENT_ADAPTIVE_COUNTER(this_instr[1].cache);
            #endif  /* ENABLE_SPECIALIZATION */
            (void)seq;
            (void)counter;
        }

        op(_UNPACK_SEQUENCE, (seq -- unused[oparg])) {
            PyObject **top = stack_pointer + oparg - 1;
            int res = _PyEval_UnpackIterable(tstate, seq, oparg, -1, top);
            DECREF_INPUTS();
            ERROR_IF(res == 0, error);
        }

        macro(UNPACK_SEQUENCE) = _SPECIALIZE_UNPACK_SEQUENCE + _UNPACK_SEQUENCE;

        inst(UNPACK_SEQUENCE_TWO_TUPLE, (unused/1, seq -- values[oparg])) {
            DEOPT_IF(!PyTuple_CheckExact(seq));
            DEOPT_IF(PyTuple_GET_SIZE(seq) != 2);
            assert(oparg == 2);
            STAT_INC(UNPACK_SEQUENCE, hit);
            values[0] = Py_NewRef(PyTuple_GET_ITEM(seq, 1));
            values[1] = Py_NewRef(PyTuple_GET_ITEM(seq, 0));
            DECREF_INPUTS();
        }

        inst(UNPACK_SEQUENCE_TUPLE, (unused/1, seq -- values[oparg])) {
            DEOPT_IF(!PyTuple_CheckExact(seq));
            DEOPT_IF(PyTuple_GET_SIZE(seq) != oparg);
            STAT_INC(UNPACK_SEQUENCE, hit);
            PyObject **items = _PyTuple_ITEMS(seq);
            for (int i = oparg; --i >= 0; ) {
                *values++ = Py_NewRef(items[i]);
            }
            DECREF_INPUTS();
        }

        inst(UNPACK_SEQUENCE_LIST, (unused/1, seq -- values[oparg])) {
            DEOPT_IF(!PyList_CheckExact(seq));
            DEOPT_IF(PyList_GET_SIZE(seq) != oparg);
            STAT_INC(UNPACK_SEQUENCE, hit);
            PyObject **items = _PyList_ITEMS(seq);
            for (int i = oparg; --i >= 0; ) {
                *values++ = Py_NewRef(items[i]);
            }
            DECREF_INPUTS();
        }

        inst(UNPACK_EX, (seq -- unused[oparg & 0xFF], unused, unused[oparg >> 8])) {
            int totalargs = 1 + (oparg & 0xFF) + (oparg >> 8);
            PyObject **top = stack_pointer + totalargs - 1;
            int res = _PyEval_UnpackIterable(tstate, seq, oparg & 0xFF, oparg >> 8, top);
            DECREF_INPUTS();
            ERROR_IF(res == 0, error);
        }
