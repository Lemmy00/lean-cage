// SPDX-License-Identifier: Apache-2.0
// §AR-host-boundary.interfaces.gateway: Call through CPython with the actual kwargs dictionary.
#define Py_LIMITED_API 0x030b0000
#include <Python.h>

static PyObject *gateway_call(PyObject *module, PyObject *arguments) {
    (void)module;
    PyObject *callable, *positional, *keywords;
    if (!PyArg_ParseTuple(arguments, "OOO:call", &callable, &positional, &keywords)) return NULL;
    return PyObject_Call(callable, positional, keywords);
}

static PyMethodDef methods[] = {
    { "call", gateway_call, METH_VARARGS, "Call with the supplied keyword dictionary." },
    { NULL, NULL, 0, NULL }
};
static struct PyModuleDef definition = {
    PyModuleDef_HEAD_INIT, "_gateway_call", NULL, -1, methods, NULL, NULL, NULL, NULL
};
PyMODINIT_FUNC PyInit__gateway_call(void) { return PyModule_Create(&definition); }
