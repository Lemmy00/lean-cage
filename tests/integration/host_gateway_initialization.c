/* SPDX-License-Identifier: Apache-2.0 */
/* §AR-host-boundary.interfaces: Exercise the maintained native entry guards with the real SDK. */
#include "../../linux/host_python.c"

static int expect_uninitialized(void *result) {
    if (result || !PyErr_ExceptionMatches(PyExc_RuntimeError)) return 0;
    PyErr_Clear();
    return 1;
}

static PyObject *probe(PyObject *self, PyObject *unused) {
    (void)self; (void)unused;
    /* No module initialization has run in this separate identified fixture. */
    if (host_initialized) {
        PyErr_SetString(PyExc_AssertionError, "fixture already initialized"); return NULL;
    }
    int workspace = host_workspace_init(NULL, NULL, NULL);
    if (workspace != -1 || !expect_uninitialized(NULL)) goto failed;
    if (!expect_uninitialized(host_as_path(NULL))) goto failed;
    if (!expect_uninitialized(host_exchange(NULL, 0, 0, NULL, 0))) goto failed;
    if (!expect_uninitialized(host_cli(NULL, NULL, NULL))) goto failed;
    Py_IncRef(Py_True); return Py_True;
failed:
    PyErr_Clear();
    PyErr_SetString(PyExc_AssertionError, "native entry did not reject before using its arguments");
    return NULL;
}
static PyMethodDef methods[] = {
    {"probe", probe, METH_NOARGS, "Check real pre-initialization native entries."},
    {NULL, NULL, 0, NULL}
};
static PyModuleDef module = {
    PyModuleDef_HEAD_INIT, "_initialization", NULL, -1, methods, NULL, NULL, NULL, NULL
};
PyMODINIT_FUNC PyInit__initialization(void) { return PyModule_Create(&module); }
