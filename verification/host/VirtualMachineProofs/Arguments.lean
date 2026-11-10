import LeanCageHost.VirtualMachine

namespace LeanCage.Host.VirtualMachine

-- §FS-host-boundary.caller: QEMU receives only fixed options and the actual prepared bundle/run
-- paths.
theorem arguments_paths (bundle : Validation.Bundle) (directory : String) :
    (arguments bundle directory).cmd = bundle.root ++ "/emulator/usr/bin/qemu-system-x86_64" ∧
    (arguments bundle directory).args =
      #["-L", bundle.root ++ "/emulator/usr/share/qemu", "-no-user-config", "-nodefaults",
        "-machine", "pc,accel=tcg", "-cpu", "max", "-smp", "1", "-m", "2048M",
        "-bios", bundle.root ++ "/emulator/usr/share/seabios/bios-256k.bin", "-display", "none",
        "-monitor", "none", "-nic", "none", "-no-reboot", "-serial", "stdio",
        "-chardev", "socket,id=control,path=" ++ directory ++ "/control.sock,server=on,wait=on",
        "-serial", "chardev:control", "-device", "isa-debug-exit,iobase=0xf4,iosize=0x04",
        "-kernel", bundle.root ++ "/profile/kernel", "-initrd", directory ++ "/request.cpio",
        "-append", "console=ttyS0,115200 rdinit=/init panic=1 oops=panic loglevel=3 clocksource=acpi_pm tsc=unstable"] :=
  ⟨rfl, rfl⟩

theorem arguments_environment (bundle : Validation.Bundle) (directory : String) :
    (arguments bundle directory).inheritEnv = false ∧
    (arguments bundle directory).env =
      #[("PATH", some "/usr/bin:/bin"), ("LC_ALL", some "C"),
        ("LD_LIBRARY_PATH", some (bundle.root ++ "/emulator/usr/lib/x86_64-linux-gnu")),
        ("QEMU_MODULE_DIR", some (bundle.root ++ "/emulator/usr/lib/x86_64-linux-gnu/qemu"))] ∧
    (arguments bundle directory).stdin = .null ∧
    (arguments bundle directory).stdout = .piped ∧
    (arguments bundle directory).stderr = .piped ∧
    (arguments bundle directory).setsid = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end LeanCage.Host.VirtualMachine
