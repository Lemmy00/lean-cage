-- SPDX-License-Identifier: Apache-2.0
import CCLib.ClightExecSound

-- §AR-m4-routes.lean: Inspect the actual port theorem; no sandbox claim is made.
set_option pp.all true
#check CC.Step
#check CC.doStep_sound
#print axioms CC.doStep_sound
