"""Reusable caller-policy execution in LeanCage's disposable Linux VM."""
# §FS-linux-product.operation: The CLI and integrations consume this same library.
__all__ = ["Workspace", "Outcome", "Cancellation"]


def __getattr__(name):
    if name in __all__:
        from . import runner
        return getattr(runner, name)
    raise AttributeError(name)
